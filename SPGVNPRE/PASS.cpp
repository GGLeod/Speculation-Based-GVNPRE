//===-- Frequent Path Loop Invariant Code Motion Pass ------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// EECS583 F21 - This pass can be used as a template for your Frequent Path LICM
//               homework assignment. The pass gets registered as "fplicm".
//
// This pass performs loop invariant code motion, attempting to remove as much
// code from the body of a loop as possible.  It does this by either hoisting
// code into the preheader block, or by sinking code to the exit blocks if it is
// safe. 
//
////===----------------------------------------------------------------------===//
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include <unordered_map>
#include <functional>
#include "llvm/ADT/Statistic.h"
#define DEBUG_TYPE "spgvnpre"

/* *******Implementation Starts Here******* */
// include necessary header files
/* *******Implementation Ends Here******* */
using std::unordered_map;
using namespace llvm;



//===----------------------------------------------------------------------===//
//                         ValueTable Class
//===----------------------------------------------------------------------===//
namespace {
/// This class holds the mapping between values and value numbers.  It is used
/// as an efficient mechanism to determine the expression-wise equivalence of
/// two values.


struct Expression {

  enum ExpressionOpcode { ADD, SUB, MUL, UDIV, SDIV, FDIV, UREM, SREM, 
                          FREM, SHL, LSHR, ASHR, AND, OR, XOR, ICMPEQ, 
                          ICMPNE, ICMPUGT, ICMPUGE, ICMPULT, ICMPULE, 
                          ICMPSGT, ICMPSGE, ICMPSLT, ICMPSLE, FCMPOEQ, 
                          FCMPOGT, FCMPOGE, FCMPOLT, FCMPOLE, FCMPONE, 
                          FCMPORD, FCMPUNO, FCMPUEQ, FCMPUGT, FCMPUGE, 
                          FCMPULT, FCMPULE, FCMPUNE, EXTRACT, INSERT,
                          SHUFFLE, SELECT, TRUNC, ZEXT, SEXT, FPTOUI,
                          FPTOSI, UITOFP, SITOFP, FPTRUNC, FPEXT, 
                          PTRTOINT, INTTOPTR, BITCAST, GEP, EMPTY,
                          TOMBSTONE };
  ExpressionOpcode opcode;
  const Type* type;
  uint32_t firstVN;
  uint32_t secondVN;
  uint32_t thirdVN;
  SmallVector<uint32_t, 4> varargs;
  
  Expression() { }
  explicit Expression(ExpressionOpcode o) : opcode(o) { }
  
  bool operator==(const Expression &other) const {
    if (opcode != other.opcode)
      return false;
    else if (opcode == EMPTY || opcode == TOMBSTONE)
      return true;
    else if (type != other.type)
      return false;
    else if (firstVN != other.firstVN)
      return false;
    else if (secondVN != other.secondVN)
      return false;
    else if (thirdVN != other.thirdVN)
      return false;
    else {
      if (varargs.size() != other.varargs.size())
        return false;
      
      for (size_t i = 0; i < varargs.size(); ++i)
        if (varargs[i] != other.varargs[i])
          return false;
    
      return true;
    }
  }
  
  bool operator!=(const Expression &other) const {
    if (opcode != other.opcode)
      return true;
    else if (opcode == EMPTY || opcode == TOMBSTONE)
      return false;
    else if (type != other.type)
      return true;
    else if (firstVN != other.firstVN)
      return true;
    else if (secondVN != other.secondVN)
      return true;
    else if (thirdVN != other.thirdVN)
      return true;
    else {
      if (varargs.size() != other.varargs.size())
        return true;
      
      for (size_t i = 0; i < varargs.size(); ++i)
        if (varargs[i] != other.varargs[i])
          return true;
    
      return false;
    }
  }
};
}

namespace {
  class ValueTable {
    private:
    // ExpressionOpcode opcode;
    // const Type* type;
    // uint32_t firstVN;
    // uint32_t secondVN;
    // uint32_t thirdVN;
    // SmallVector<uint32_t, 4> varargs;
      struct Exhash{
        std::size_t operator()(const Expression& E) const{
          using std::hash;
          
          size_t h = hash<int>()(E.opcode);
          h = h ^ (hash<int>()(E.firstVN) << 1) >> 1;
          h = h ^ (hash<int>()(E.secondVN) << 1) >> 1;
          h = h ^ (hash<int>()(E.thirdVN) << 1) >> 1;
          h = h ^ (hash<int>()(E.type->getTypeID()) << 1) >> 1;

          

          
          return hash<int>()(E.opcode) ^ (hash<int>()(E.firstVN) ) ;
        }
      };

      struct Exequal{
        bool operator()(const Expression& E1, const Expression& E2) const{
          bool result = E1.type->getTypeID() == E2.type->getTypeID()
           && E1.firstVN==E2.firstVN && E1.secondVN == E2.secondVN && E1.thirdVN == E2.thirdVN
            && E1.varargs.size() == E2.varargs.size();

          if(result){
            for(int i=0; i<E1.varargs.size(); i++){
              if(E1.varargs[i] != E2.varargs[i]){
                return false;
              }
            }
          }


          return result;

        }
      };


      DenseMap<Value*, uint32_t> valueNumbering;
      unordered_map<Expression, uint32_t, Exhash, Exequal> expressionNumbering;
  
      uint32_t nextValueNumber;
    
      Expression::ExpressionOpcode getOpcode(BinaryOperator* BO);
      Expression::ExpressionOpcode getOpcode(CmpInst* C);
      Expression::ExpressionOpcode getOpcode(CastInst* C);
      Expression create_expression(BinaryOperator* BO);
      Expression create_expression(CmpInst* C);
      Expression create_expression(ShuffleVectorInst* V);
      Expression create_expression(ExtractElementInst* C);
      Expression create_expression(InsertElementInst* V);
      Expression create_expression(SelectInst* V);
      Expression create_expression(CastInst* C);
      Expression create_expression(GetElementPtrInst* G);
    public:
      ValueTable() { 
        nextValueNumber = 1; 
        }
      uint32_t lookup_or_add(Value* V);
      uint32_t lookup(Value* V) const;
      void add(Value* V, uint32_t num);
      void clear();
      void erase(Value* v);
      unsigned size();
  };
}

//===----------------------------------------------------------------------===//
//                     ValueTable Internal Functions
//===----------------------------------------------------------------------===//
Expression::ExpressionOpcode 
                             ValueTable::getOpcode(BinaryOperator* BO) {
  switch(BO->getOpcode()) {
    case Instruction::Add:
      return Expression::ADD;
    case Instruction::Sub:
      return Expression::SUB;
    case Instruction::Mul:
      return Expression::MUL;
    case Instruction::UDiv:
      return Expression::UDIV;
    case Instruction::SDiv:
      return Expression::SDIV;
    case Instruction::FDiv:
      return Expression::FDIV;
    case Instruction::URem:
      return Expression::UREM;
    case Instruction::SRem:
      return Expression::SREM;
    case Instruction::FRem:
      return Expression::FREM;
    case Instruction::Shl:
      return Expression::SHL;
    case Instruction::LShr:
      return Expression::LSHR;
    case Instruction::AShr:
      return Expression::ASHR;
    case Instruction::And:
      return Expression::AND;
    case Instruction::Or:
      return Expression::OR;
    case Instruction::Xor:
      return Expression::XOR;
    
    // THIS SHOULD NEVER HAPPEN
    default:
      assert(0 && "Binary operator with unknown opcode?");
      return Expression::ADD;
  }
}
Expression::ExpressionOpcode ValueTable::getOpcode(CmpInst* C) {
  if (C->getOpcode() == Instruction::ICmp) {
    switch (C->getPredicate()) {
      case ICmpInst::ICMP_EQ:
        return Expression::ICMPEQ;
      case ICmpInst::ICMP_NE:
        return Expression::ICMPNE;
      case ICmpInst::ICMP_UGT:
        return Expression::ICMPUGT;
      case ICmpInst::ICMP_UGE:
        return Expression::ICMPUGE;
      case ICmpInst::ICMP_ULT:
        return Expression::ICMPULT;
      case ICmpInst::ICMP_ULE:
        return Expression::ICMPULE;
      case ICmpInst::ICMP_SGT:
        return Expression::ICMPSGT;
      case ICmpInst::ICMP_SGE:
        return Expression::ICMPSGE;
      case ICmpInst::ICMP_SLT:
        return Expression::ICMPSLT;
      case ICmpInst::ICMP_SLE:
        return Expression::ICMPSLE;
      
      // THIS SHOULD NEVER HAPPEN
      default:
        assert(0 && "Comparison with unknown predicate?");
        return Expression::ICMPEQ;
    }
  } else {
    switch (C->getPredicate()) {
      case FCmpInst::FCMP_OEQ:
        return Expression::FCMPOEQ;
      case FCmpInst::FCMP_OGT:
        return Expression::FCMPOGT;
      case FCmpInst::FCMP_OGE:
        return Expression::FCMPOGE;
      case FCmpInst::FCMP_OLT:
        return Expression::FCMPOLT;
      case FCmpInst::FCMP_OLE:
        return Expression::FCMPOLE;
      case FCmpInst::FCMP_ONE:
        return Expression::FCMPONE;
      case FCmpInst::FCMP_ORD:
        return Expression::FCMPORD;
      case FCmpInst::FCMP_UNO:
        return Expression::FCMPUNO;
      case FCmpInst::FCMP_UEQ:
        return Expression::FCMPUEQ;
      case FCmpInst::FCMP_UGT:
        return Expression::FCMPUGT;
      case FCmpInst::FCMP_UGE:
        return Expression::FCMPUGE;
      case FCmpInst::FCMP_ULT:
        return Expression::FCMPULT;
      case FCmpInst::FCMP_ULE:
        return Expression::FCMPULE;
      case FCmpInst::FCMP_UNE:
        return Expression::FCMPUNE;
      
      // THIS SHOULD NEVER HAPPEN
      default:
        assert(0 && "Comparison with unknown predicate?");
        return Expression::FCMPOEQ;
    }
  }
}
Expression::ExpressionOpcode 
                             ValueTable::getOpcode(CastInst* C) {
  switch(C->getOpcode()) {
    case Instruction::Trunc:
      return Expression::TRUNC;
    case Instruction::ZExt:
      return Expression::ZEXT;
    case Instruction::SExt:
      return Expression::SEXT;
    case Instruction::FPToUI:
      return Expression::FPTOUI;
    case Instruction::FPToSI:
      return Expression::FPTOSI;
    case Instruction::UIToFP:
      return Expression::UITOFP;
    case Instruction::SIToFP:
      return Expression::SITOFP;
    case Instruction::FPTrunc:
      return Expression::FPTRUNC;
    case Instruction::FPExt:
      return Expression::FPEXT;
    case Instruction::PtrToInt:
      return Expression::PTRTOINT;
    case Instruction::IntToPtr:
      return Expression::INTTOPTR;
    case Instruction::BitCast:
      return Expression::BITCAST;
    
    // THIS SHOULD NEVER HAPPEN
    default:
      assert(0 && "Cast operator with unknown opcode?");
      return Expression::BITCAST;
  }
}
Expression ValueTable::create_expression(BinaryOperator* BO) {
  Expression e;
    
  e.firstVN = lookup_or_add(BO->getOperand(0));
  e.secondVN = lookup_or_add(BO->getOperand(1));
  e.thirdVN = 0;
  e.type = BO->getType();
  e.opcode = getOpcode(BO);
  
  return e;
}
Expression ValueTable::create_expression(CmpInst* C) {
  Expression e;
    
  e.firstVN = lookup_or_add(C->getOperand(0));
  e.secondVN = lookup_or_add(C->getOperand(1));
  e.thirdVN = 0;
  e.type = C->getType();
  e.opcode = getOpcode(C);
  
  return e;
}
Expression ValueTable::create_expression(CastInst* C) {
  Expression e;
    
  e.firstVN = lookup_or_add(C->getOperand(0));
  e.secondVN = 0;
  e.thirdVN = 0;
  e.type = C->getType();
  e.opcode = getOpcode(C);
  
  return e;
}
Expression ValueTable::create_expression(ShuffleVectorInst* S) {
  Expression e;
    
  e.firstVN = lookup_or_add(S->getOperand(0));
  e.secondVN = lookup_or_add(S->getOperand(1));
  e.thirdVN = lookup_or_add(S->getOperand(2));
  e.type = S->getType();
  e.opcode = Expression::SHUFFLE;
  
  return e;
}
Expression ValueTable::create_expression(ExtractElementInst* E) {
  Expression e;
    
  e.firstVN = lookup_or_add(E->getOperand(0));
  e.secondVN = lookup_or_add(E->getOperand(1));
  e.thirdVN = 0;
  e.type = E->getType();
  e.opcode = Expression::EXTRACT;
  
  return e;
}
Expression ValueTable::create_expression(InsertElementInst* I) {
  Expression e;
    
  e.firstVN = lookup_or_add(I->getOperand(0));
  e.secondVN = lookup_or_add(I->getOperand(1));
  e.thirdVN = lookup_or_add(I->getOperand(2));
  e.type = I->getType();
  e.opcode = Expression::INSERT;
  
  return e;
}
Expression ValueTable::create_expression(SelectInst* I) {
  Expression e;
    
  e.firstVN = lookup_or_add(I->getCondition());
  e.secondVN = lookup_or_add(I->getTrueValue());
  e.thirdVN = lookup_or_add(I->getFalseValue());
  e.type = I->getType();
  e.opcode = Expression::SELECT;
  
  return e;
}
Expression ValueTable::create_expression(GetElementPtrInst* G) {
  Expression e;
    
  e.firstVN = lookup_or_add(G->getPointerOperand());
  e.secondVN = 0;
  e.thirdVN = 0;
  e.type = G->getType();
  e.opcode = Expression::GEP;
  
  for (GetElementPtrInst::op_iterator I = G->idx_begin(), E = G->idx_end();
       I != E; ++I)
    e.varargs.push_back(lookup_or_add(*I));
  
  return e;
}
//===----------------------------------------------------------------------===//
//                     ValueTable External Functions
//===----------------------------------------------------------------------===//
/// lookup_or_add - Returns the value number for the specified value, assigning
/// it a new number if it did not have one before.
uint32_t ValueTable::lookup_or_add(Value* V) {
  DenseMap<Value*, uint32_t>::iterator VI = valueNumbering.find(V);
  if (VI != valueNumbering.end())
    return VI->second;
  
  
  if (BinaryOperator* BO = dyn_cast<BinaryOperator>(V)) {
    Expression e = create_expression(BO);
    
    auto EI = expressionNumbering.find(e);
    if (EI != expressionNumbering.end()) {
      valueNumbering.insert(std::make_pair(V, EI->second));
      return EI->second;
    } else {
      expressionNumbering.insert(std::make_pair(e, nextValueNumber));
      valueNumbering.insert(std::make_pair(V, nextValueNumber));
      
      return nextValueNumber++;
    }
  } else if (CmpInst* C = dyn_cast<CmpInst>(V)) {
    Expression e = create_expression(C);
    
    auto EI = expressionNumbering.find(e);
    if (EI != expressionNumbering.end()) {
      valueNumbering.insert(std::make_pair(V, EI->second));
      return EI->second;
    } else {
      expressionNumbering.insert(std::make_pair(e, nextValueNumber));
      valueNumbering.insert(std::make_pair(V, nextValueNumber));
      
      return nextValueNumber++;
    }
  } else if (ShuffleVectorInst* U = dyn_cast<ShuffleVectorInst>(V)) {
    Expression e = create_expression(U);
    
    auto EI = expressionNumbering.find(e);
    if (EI != expressionNumbering.end()) {
      valueNumbering.insert(std::make_pair(V, EI->second));
      return EI->second;
    } else {
      expressionNumbering.insert(std::make_pair(e, nextValueNumber));
      valueNumbering.insert(std::make_pair(V, nextValueNumber));
      
      return nextValueNumber++;
    }
  } else if (ExtractElementInst* U = dyn_cast<ExtractElementInst>(V)) {
    Expression e = create_expression(U);
    
    auto EI = expressionNumbering.find(e);
    if (EI != expressionNumbering.end()) {
      valueNumbering.insert(std::make_pair(V, EI->second));
      return EI->second;
    } else {
      expressionNumbering.insert(std::make_pair(e, nextValueNumber));
      valueNumbering.insert(std::make_pair(V, nextValueNumber));
      
      return nextValueNumber++;
    }
  } else if (InsertElementInst* U = dyn_cast<InsertElementInst>(V)) {
    Expression e = create_expression(U);
    
    auto EI = expressionNumbering.find(e);
    if (EI != expressionNumbering.end()) {
      valueNumbering.insert(std::make_pair(V, EI->second));
      return EI->second;
    } else {
      expressionNumbering.insert(std::make_pair(e, nextValueNumber));
      valueNumbering.insert(std::make_pair(V, nextValueNumber));
      
      return nextValueNumber++;
    }
  } else if (SelectInst* U = dyn_cast<SelectInst>(V)) {
    Expression e = create_expression(U);
    
    auto EI = expressionNumbering.find(e);
    if (EI != expressionNumbering.end()) {
      valueNumbering.insert(std::make_pair(V, EI->second));
      return EI->second;
    } else {
      expressionNumbering.insert(std::make_pair(e, nextValueNumber));
      valueNumbering.insert(std::make_pair(V, nextValueNumber));
      
      return nextValueNumber++;
    }
  } else if (CastInst* U = dyn_cast<CastInst>(V)) {
    Expression e = create_expression(U);
    
    auto EI = expressionNumbering.find(e);
    if (EI != expressionNumbering.end()) {
      valueNumbering.insert(std::make_pair(V, EI->second));
      return EI->second;
    } else {
      expressionNumbering.insert(std::make_pair(e, nextValueNumber));
      valueNumbering.insert(std::make_pair(V, nextValueNumber));
      
      return nextValueNumber++;
    }
  } else if (GetElementPtrInst* U = dyn_cast<GetElementPtrInst>(V)) {
    Expression e = create_expression(U);
    
    auto EI = expressionNumbering.find(e);
    if (EI != expressionNumbering.end()) {
      valueNumbering.insert(std::make_pair(V, EI->second));
      return EI->second;
    } else {
      expressionNumbering.insert(std::make_pair(e, nextValueNumber));
      valueNumbering.insert(std::make_pair(V, nextValueNumber));
      
      return nextValueNumber++;
    }
  } else {
    valueNumbering.insert(std::make_pair(V, nextValueNumber));
    return nextValueNumber++;
  }
}
/// lookup - Returns the value number of the specified value. Fails if
/// the value has not yet been numbered.
uint32_t ValueTable::lookup(Value* V) const {
  auto VI = valueNumbering.find(V);
  if (VI != valueNumbering.end())
    return VI->second;
  else
    assert(0 && "Value not numbered?");
  
  return 0;
}
/// add - Add the specified value with the given value number, removing
/// its old number, if any
void ValueTable::add(Value* V, uint32_t num) {
  DenseMap<Value*, uint32_t>::iterator VI = valueNumbering.find(V);
  if (VI != valueNumbering.end())
    valueNumbering.erase(VI);
  valueNumbering.insert(std::make_pair(V, num));
}
/// clear - Remove all entries from the ValueTable
void ValueTable::clear() {
  valueNumbering.clear();
  expressionNumbering.clear();
  nextValueNumber = 1;
}
/// erase - Remove a value from the value numbering
void ValueTable::erase(Value* V) {
  valueNumbering.erase(V);
}
/// size - Return the number of assigned value numbers
unsigned ValueTable::size() {
  // NOTE: zero is never assigned
  return nextValueNumber;
}


namespace {
//===----------------------------------------------------------------------===//
//                       ValueNumberedSet Class
//===----------------------------------------------------------------------===//
class ValueNumberedSet {
  private:
    SmallPtrSet<Value*, 8> contents;
    BitVector numbers;
  public:
    ValueNumberedSet() { numbers.resize(1); }
    ValueNumberedSet(const ValueNumberedSet& other) {
      numbers = other.numbers;
      contents = other.contents;
    }
    
    typedef SmallPtrSet<Value*, 8>::iterator iterator;
    
    iterator begin() { return contents.begin(); }
    iterator end() { return contents.end(); }
    
    bool insert(Value* v) { return contents.insert(v).second; }
    void insert(iterator I, iterator E) { contents.insert(I, E); }
    void erase(Value* v) { contents.erase(v); }
    unsigned count(Value* v) { return contents.count(v); }
    size_t size() { return contents.size(); }
    
    void set(unsigned i)  {
      if (i >= numbers.size())
        numbers.resize(i+1);
      
      numbers.set(i);
    }
    
    void operator=(const ValueNumberedSet& other) {
      contents = other.contents;
      numbers = other.numbers;
    }
    
    void reset(unsigned i)  {
      if (i < numbers.size())
        numbers.reset(i);
    }
    
    bool test(unsigned i)  {
      if (i >= numbers.size())
        return false;
      
      return numbers.test(i);
    }
    
    void clear() {
      contents.clear();
      numbers.clear();
    }
};
}

namespace {
  class SPGVNPRE : public FunctionPass {
    bool runOnFunction(Function &F);
  public:
    static char ID; // Pass identification, replacement for typeid
    SPGVNPRE() : FunctionPass(ID) {}
  private:
    ValueTable VN;
    SmallVector<Instruction*, 8> createdExpressions;
    
    DenseMap<BasicBlock*, ValueNumberedSet> availableOut;
    DenseMap<BasicBlock*, ValueNumberedSet> anticipatedIn;
    DenseMap<BasicBlock*, ValueNumberedSet> generatedPhis;
    
    // This transformation requires dominator postdominator info
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesCFG();
      AU.addRequiredID(BreakCriticalEdgesID);
      //AU.addRequired<UnifyFunctionExitNodes>();
      AU.addRequired<DominatorTreeWrapperPass>();
    }
  
    // Helper fuctions
    // FIXME: eliminate or document these better
    void dump(ValueNumberedSet& s) const ;
    void clean(ValueNumberedSet& set) ;
    Value* find_leader(ValueNumberedSet& vals, uint32_t v) ;
    Value* phi_translate(Value* V, BasicBlock* pred, BasicBlock* succ) ;
    void phi_translate_set(ValueNumberedSet& anticIn, BasicBlock* pred,
                           BasicBlock* succ, ValueNumberedSet& out) ;
    
    void topo_sort(ValueNumberedSet& set,
                   SmallVector<Value*, 8>& vec) ;
    
    void cleanup() ;
    bool elimination() ;
    
    void val_insert(ValueNumberedSet& s, Value* v) ;
    void val_replace(ValueNumberedSet& s, Value* v) ;
    bool dependsOnInvoke(Value* V) ;
    void buildsets_availout(BasicBlock::iterator I,
                            ValueNumberedSet& currAvail,
                            ValueNumberedSet& currPhis,
                            ValueNumberedSet& currExps,
                            SmallPtrSet<Value*, 16>& currTemps);
    bool buildsets_anticout(BasicBlock* BB,
                            ValueNumberedSet& anticOut,
                            SmallPtrSet<BasicBlock*, 8>& visited);
    unsigned buildsets_anticin(BasicBlock* BB,
                           ValueNumberedSet& anticOut,
                           ValueNumberedSet& currExps,
                           SmallPtrSet<Value*, 16>& currTemps,
                           SmallPtrSet<BasicBlock*, 8>& visited);
    void buildsets(Function& F) ;
    
    void insertion_pre(Value* e, BasicBlock* BB,
                       DenseMap<BasicBlock*, Value*>& avail,
                       std::map<BasicBlock*,ValueNumberedSet>& new_set);
    unsigned insertion_mergepoint(SmallVector<Value*, 8>& workList,
                                  df_iterator<DomTreeNode*>& D,
                      std::map<BasicBlock*, ValueNumberedSet>& new_set);
    bool insertion(Function& F) ;
  
  };
  
  
}


// STATISTIC(NumInsertedVals, "Number of values inserted");
// STATISTIC(NumInsertedPhis, "Number of PHI nodes inserted");
// STATISTIC(NumEliminated, "Number of redundant instructions eliminated");
/// find_leader - Given a set and a value number, return the first
/// element of the set with that value number, or 0 if no such element
/// is present
Value* SPGVNPRE::find_leader(ValueNumberedSet& vals, uint32_t v) {
  if (!vals.test(v))
    return 0;
  
  for (ValueNumberedSet::iterator I = vals.begin(), E = vals.end();
       I != E; ++I)
    if (v == VN.lookup(*I))
      return *I;
  
  assert(0 && "No leader found, but present bit is set?");
  return 0;
}
/// val_insert - Insert a value into a set only if there is not a value
/// with the same value number already in the set
void SPGVNPRE::val_insert(ValueNumberedSet& s, Value* v) {
  uint32_t num = VN.lookup(v);
  if (!s.test(num))
    s.insert(v);
}
/// val_replace - Insert a value into a set, replacing any values already in
/// the set that have the same value number
void SPGVNPRE::val_replace(ValueNumberedSet& s, Value* v) {
  if (s.count(v)) return;
  
  uint32_t num = VN.lookup(v);
  Value* leader = find_leader(s, num);
  if (leader != 0)
    s.erase(leader);
  s.insert(v);
  s.set(num);
}

/// clean - Remove all non-opaque values from the set whose operands are not
/// themselves in the set, as well as all values that depend on invokes (see 
/// above)
void SPGVNPRE::clean(ValueNumberedSet& set) {
  SmallVector<Value*, 8> worklist;
  worklist.reserve(set.size());
  topo_sort(set, worklist);
  
  for (unsigned i = 0; i < worklist.size(); ++i) {
    Value* v = worklist[i];
    
    // Handle unary ops
    if (CastInst* U = dyn_cast<CastInst>(v)) {
      bool lhsValid = !isa<Instruction>(U->getOperand(0));
      lhsValid |= set.test(VN.lookup(U->getOperand(0)));
      if (lhsValid)
        lhsValid = !dependsOnInvoke(U->getOperand(0));
      
      if (!lhsValid) {
        set.erase(U);
        set.reset(VN.lookup(U));
      }
    
    // Handle binary ops
    } else if (isa<BinaryOperator>(v) || isa<CmpInst>(v) ||
        isa<ExtractElementInst>(v)) {
      User* U = cast<User>(v);
      
      bool lhsValid = !isa<Instruction>(U->getOperand(0));
      lhsValid |= set.test(VN.lookup(U->getOperand(0)));
      if (lhsValid)
        lhsValid = !dependsOnInvoke(U->getOperand(0));
    
      bool rhsValid = !isa<Instruction>(U->getOperand(1));
      rhsValid |= set.test(VN.lookup(U->getOperand(1)));
      if (rhsValid)
        rhsValid = !dependsOnInvoke(U->getOperand(1));
      
      if (!lhsValid || !rhsValid) {
        set.erase(U);
        set.reset(VN.lookup(U));
      }
    
    // Handle ternary ops
    } else if (isa<ShuffleVectorInst>(v) || isa<InsertElementInst>(v) ||
               isa<SelectInst>(v)) {
      User* U = cast<User>(v);
    
      bool lhsValid = !isa<Instruction>(U->getOperand(0));
      lhsValid |= set.test(VN.lookup(U->getOperand(0)));
      if (lhsValid)
        lhsValid = !dependsOnInvoke(U->getOperand(0));
      
      bool rhsValid = !isa<Instruction>(U->getOperand(1));
      rhsValid |= set.test(VN.lookup(U->getOperand(1)));
      if (rhsValid)
        rhsValid = !dependsOnInvoke(U->getOperand(1));
      
      bool thirdValid = !isa<Instruction>(U->getOperand(2));
      thirdValid |= set.test(VN.lookup(U->getOperand(2)));
      if (thirdValid)
        thirdValid = !dependsOnInvoke(U->getOperand(2));
    
      if (!lhsValid || !rhsValid || !thirdValid) {
        set.erase(U);
        set.reset(VN.lookup(U));
      }
    
    // Handle varargs ops
    } else if (GetElementPtrInst* U = dyn_cast<GetElementPtrInst>(v)) {
      bool ptrValid = !isa<Instruction>(U->getPointerOperand());
      ptrValid |= set.test(VN.lookup(U->getPointerOperand()));
      if (ptrValid)
        ptrValid = !dependsOnInvoke(U->getPointerOperand());
      
      bool varValid = true;
      for (GetElementPtrInst::op_iterator I = U->idx_begin(), E = U->idx_end();
           I != E; ++I)
        if (varValid) {
          varValid &= !isa<Instruction>(*I) || set.test(VN.lookup(*I));
          varValid &= !dependsOnInvoke(*I);
        }
    
      if (!ptrValid || !varValid) {
        set.erase(U);
        set.reset(VN.lookup(U));
      }
    }
  }
}

/// topo_sort - Given a set of values, sort them by topological
/// order into the provided vector.
void SPGVNPRE::topo_sort(ValueNumberedSet& set, SmallVector<Value*, 8>& vec) {
  SmallPtrSet<Value*, 16> visited;
  SmallVector<Value*, 8> stack;
  for (ValueNumberedSet::iterator I = set.begin(), E = set.end();
       I != E; ++I) {
    if (visited.count(*I) == 0)
      stack.push_back(*I);
    
    while (!stack.empty()) {
      Value* e = stack.back();
      
      // Handle unary ops
      if (CastInst* U = dyn_cast<CastInst>(e)) {
        Value* l = find_leader(set, VN.lookup(U->getOperand(0)));
    
        if (l != 0 && isa<Instruction>(l) &&
            visited.count(l) == 0)
          stack.push_back(l);
        else {
          vec.push_back(e);
          visited.insert(e);
          stack.pop_back();
        }
      
      // Handle binary ops
      } else if (isa<BinaryOperator>(e) || isa<CmpInst>(e) ||
          isa<ExtractElementInst>(e)) {
        User* U = cast<User>(e);
        Value* l = find_leader(set, VN.lookup(U->getOperand(0)));
        Value* r = find_leader(set, VN.lookup(U->getOperand(1)));
    
        if (l != 0 && isa<Instruction>(l) &&
            visited.count(l) == 0)
          stack.push_back(l);
        else if (r != 0 && isa<Instruction>(r) &&
                 visited.count(r) == 0)
          stack.push_back(r);
        else {
          vec.push_back(e);
          visited.insert(e);
          stack.pop_back();
        }
      
      // Handle ternary ops
      } else if (isa<InsertElementInst>(e) || isa<ShuffleVectorInst>(e) ||
                 isa<SelectInst>(e)) {
        User* U = cast<User>(e);
        Value* l = find_leader(set, VN.lookup(U->getOperand(0)));
        Value* r = find_leader(set, VN.lookup(U->getOperand(1)));
        Value* m = find_leader(set, VN.lookup(U->getOperand(2)));
      
        if (l != 0 && isa<Instruction>(l) &&
            visited.count(l) == 0)
          stack.push_back(l);
        else if (r != 0 && isa<Instruction>(r) &&
                 visited.count(r) == 0)
          stack.push_back(r);
        else if (m != 0 && isa<Instruction>(m) &&
                 visited.count(m) == 0)
          stack.push_back(m);
        else {
          vec.push_back(e);
          visited.insert(e);
          stack.pop_back();
        }
      
      // Handle vararg ops
      } else if (GetElementPtrInst* U = dyn_cast<GetElementPtrInst>(e)) {
        Value* p = find_leader(set, VN.lookup(U->getPointerOperand()));
        
        if (p != 0 && isa<Instruction>(p) &&
            visited.count(p) == 0)
          stack.push_back(p);
        else {
          bool push_va = false;
          for (GetElementPtrInst::op_iterator I = U->idx_begin(),
               E = U->idx_end(); I != E; ++I) {
            Value * v = find_leader(set, VN.lookup(*I));
            if (v != 0 && isa<Instruction>(v) && visited.count(v) == 0) {
              stack.push_back(v);
              push_va = true;
            }
          }
          
          if (!push_va) {
            vec.push_back(e);
            visited.insert(e);
            stack.pop_back();
          }
        }
      
      // Handle opaque ops
      } else {
        visited.insert(e);
        vec.push_back(e);
        stack.pop_back();
      }
    }
    
    stack.clear();
  }
}

/// dependsOnInvoke - Test if a value has an phi node as an operand, any of 
/// whose inputs is an invoke instruction.  If this is true, we cannot safely
/// PRE the instruction or anything that depends on it.
bool SPGVNPRE::dependsOnInvoke(Value* V) {
  if (PHINode* p = dyn_cast<PHINode>(V)) {
    for (PHINode::op_iterator I = p->op_begin(), E = p->op_end(); I != E; ++I)
      if (isa<InvokeInst>(*I))
        return true;
    return false;
  } else {
    return false;
  }
}

/// phi_translate - Given a value, its parent block, and a predecessor of its
/// parent, translate the value into legal for the predecessor block.  This 
/// means translating its operands (and recursively, their operands) through
/// any phi nodes in the parent into values available in the predecessor
Value* SPGVNPRE::phi_translate(Value* V, BasicBlock* pred, BasicBlock* succ) {
  if (V == 0)
    return 0;
  
  // Unary Operations
  if (CastInst* U = dyn_cast<CastInst>(V)) {
    Value* newOp1 = 0;
    if (isa<Instruction>(U->getOperand(0)))
      newOp1 = phi_translate(U->getOperand(0), pred, succ);
    else
      newOp1 = U->getOperand(0);
    
    if (newOp1 == 0)
      return 0;
    
    if (newOp1 != U->getOperand(0)) {
      Instruction* newVal = 0;
      if (CastInst* C = dyn_cast<CastInst>(U))
        newVal = CastInst::Create(C->getOpcode(),
                                  newOp1, C->getType(),
                                  C->getName()+".expr");
      
      uint32_t v = VN.lookup_or_add(newVal);
      
      Value* leader = find_leader(availableOut[pred], v);
      if (leader == 0) {
        createdExpressions.push_back(newVal);
        return newVal;
      } else {
        VN.erase(newVal);
        newVal->deleteValue();
        return leader;
      }
    }
  
  // Binary Operations
  } if (isa<BinaryOperator>(V) || isa<CmpInst>(V) || 
      isa<ExtractElementInst>(V)) {
    User* U = cast<User>(V);
    
    Value* newOp1 = 0;
    if (isa<Instruction>(U->getOperand(0)))
      newOp1 = phi_translate(U->getOperand(0), pred, succ);
    else
      newOp1 = U->getOperand(0);
    
    if (newOp1 == 0)
      return 0;
    
    Value* newOp2 = 0;
    if (isa<Instruction>(U->getOperand(1)))
      newOp2 = phi_translate(U->getOperand(1), pred, succ);
    else
      newOp2 = U->getOperand(1);
    
    if (newOp2 == 0)
      return 0;
    
    if (newOp1 != U->getOperand(0) || newOp2 != U->getOperand(1)) {
      Instruction* newVal = 0;
      if (BinaryOperator* BO = dyn_cast<BinaryOperator>(U))
        newVal = BinaryOperator::Create(BO->getOpcode(),
                                        newOp1, newOp2,
                                        BO->getName()+".expr");
      else if (CmpInst* C = dyn_cast<CmpInst>(U))
        newVal = CmpInst::Create(C->getOpcode(),
                                 C->getPredicate(),
                                 newOp1, newOp2,
                                 C->getName()+".expr");
      else if (ExtractElementInst* E = dyn_cast<ExtractElementInst>(U))
        newVal = ExtractElementInst::Create(newOp1, newOp2, E->getName()+".expr");
      
      uint32_t v = VN.lookup_or_add(newVal);
      
      Value* leader = find_leader(availableOut[pred], v);
      if (leader == 0) {
        createdExpressions.push_back(newVal);
        return newVal;
      } else {
        VN.erase(newVal);
        newVal->deleteValue();
        return leader;
      }
    }
  
  // Ternary Operations
  } else if (isa<ShuffleVectorInst>(V) || isa<InsertElementInst>(V) ||
             isa<SelectInst>(V)) {
    User* U = cast<User>(V);
    
    Value* newOp1 = 0;
    if (isa<Instruction>(U->getOperand(0)))
      newOp1 = phi_translate(U->getOperand(0), pred, succ);
    else
      newOp1 = U->getOperand(0);
    
    if (newOp1 == 0)
      return 0;
    
    Value* newOp2 = 0;
    if (isa<Instruction>(U->getOperand(1)))
      newOp2 = phi_translate(U->getOperand(1), pred, succ);
    else
      newOp2 = U->getOperand(1);
    
    if (newOp2 == 0)
      return 0;
    
    Value* newOp3 = 0;
    if (isa<Instruction>(U->getOperand(2)))
      newOp3 = phi_translate(U->getOperand(2), pred, succ);
    else
      newOp3 = U->getOperand(2);
    
    if (newOp3 == 0)
      return 0;
    
    if (newOp1 != U->getOperand(0) ||
        newOp2 != U->getOperand(1) ||
        newOp3 != U->getOperand(2)) {
      Instruction* newVal = 0;
      if (ShuffleVectorInst* S = dyn_cast<ShuffleVectorInst>(U))
        newVal = new ShuffleVectorInst(newOp1, newOp2, newOp3,
                                       S->getName() + ".expr");
      else if (InsertElementInst* I = dyn_cast<InsertElementInst>(U))
        newVal = InsertElementInst::Create(newOp1, newOp2, newOp3,
                                           I->getName() + ".expr");
      else if (SelectInst* I = dyn_cast<SelectInst>(U))
        newVal = SelectInst::Create(newOp1, newOp2, newOp3,
                                    I->getName() + ".expr");
      
      uint32_t v = VN.lookup_or_add(newVal);
      
      Value* leader = find_leader(availableOut[pred], v);
      if (leader == 0) {
        createdExpressions.push_back(newVal);
        return newVal;
      } else {
        VN.erase(newVal);
        newVal->deleteValue();
        return leader;
      }
    }
  
  // Varargs operators
  } else if (GetElementPtrInst* U = dyn_cast<GetElementPtrInst>(V)) {
    Value* newOp1 = 0;
    if (isa<Instruction>(U->getPointerOperand()))
      newOp1 = phi_translate(U->getPointerOperand(), pred, succ);
    else
      newOp1 = U->getPointerOperand();
    
    if (newOp1 == 0)
      return 0;
    
    bool changed_idx = false;
    SmallVector<Value*, 4> newIdx;
    for (GetElementPtrInst::op_iterator I = U->idx_begin(), E = U->idx_end();
         I != E; ++I)
      if (isa<Instruction>(*I)) {
        Value* newVal = phi_translate(*I, pred, succ);
        newIdx.push_back(newVal);
        if (newVal != *I)
          changed_idx = true;
      } else {
        newIdx.push_back(*I);
      }
    
    if (newOp1 != U->getPointerOperand() || changed_idx) {
      Instruction* newVal =
          GetElementPtrInst::Create(newOp1->getType(), newOp1,
                                    ArrayRef<Value*>(newIdx.begin(), newIdx.end()),
                                    U->getName()+".expr");
      
      uint32_t v = VN.lookup_or_add(newVal);
      
      Value* leader = find_leader(availableOut[pred], v);
      if (leader == 0) {
        createdExpressions.push_back(newVal);
        return newVal;
      } else {
        VN.erase(newVal);
        newVal->deleteValue();
        return leader;
      }
    }
  
  // PHI Nodes
  } else if (PHINode* P = dyn_cast<PHINode>(V)) {
    if (P->getParent() == succ)
      return P->getIncomingValueForBlock(pred);
  }
  
  return V;
}
/// phi_translate_set - Perform phi translation on every element of a set
void SPGVNPRE::phi_translate_set(ValueNumberedSet& anticIn,
                              BasicBlock* pred, BasicBlock* succ,
                              ValueNumberedSet& out) {
  for (ValueNumberedSet::iterator I = anticIn.begin(),
       E = anticIn.end(); I != E; ++I) {
    Value* V = phi_translate(*I, pred, succ);
    if (V != 0 && !out.test(VN.lookup_or_add(V))) {
      out.insert(V);
      out.set(VN.lookup(V));
    }
  }
}
/// buildsets_availout - When calculating availability, handle an instruction
/// by inserting it into the appropriate sets
void SPGVNPRE::buildsets_availout(BasicBlock::iterator I,
                                ValueNumberedSet& currAvail,
                                ValueNumberedSet& currPhis,
                                ValueNumberedSet& currExps,
                                SmallPtrSet<Value*, 16>& currTemps) {
  // Handle PHI nodes
  if (PHINode* p = dyn_cast<PHINode>(I)) {
    unsigned num = VN.lookup_or_add(p);
    
    currPhis.insert(p);
    currPhis.set(num);
  
  // Handle unary ops
  } else if (CastInst* U = dyn_cast<CastInst>(I)) {
    Value* leftValue = U->getOperand(0);
    
    unsigned num = VN.lookup_or_add(U);
      
    if (isa<Instruction>(leftValue))
      if (!currExps.test(VN.lookup(leftValue))) {
        currExps.insert(leftValue);
        currExps.set(VN.lookup(leftValue));
      }
    
    if (!currExps.test(num)) {
      currExps.insert(U);
      currExps.set(num);
    }
  
  // Handle binary ops
  } else if (isa<BinaryOperator>(I) || isa<CmpInst>(I) ||
             isa<ExtractElementInst>(I)) {
    User* U = cast<User>(I);
    Value* leftValue = U->getOperand(0);
    Value* rightValue = U->getOperand(1);
    
    unsigned num = VN.lookup_or_add(U);
      
    if (isa<Instruction>(leftValue))
      if (!currExps.test(VN.lookup(leftValue))) {
        currExps.insert(leftValue);
        currExps.set(VN.lookup(leftValue));
      }
    
    if (isa<Instruction>(rightValue))
      if (!currExps.test(VN.lookup(rightValue))) {
        currExps.insert(rightValue);
        currExps.set(VN.lookup(rightValue));
      }
    
    if (!currExps.test(num)) {
      currExps.insert(U);
      currExps.set(num);
    }
    
  // Handle ternary ops
  } else if (isa<InsertElementInst>(I) || isa<ShuffleVectorInst>(I) ||
             isa<SelectInst>(I)) {
    User* U = cast<User>(I);
    Value* leftValue = U->getOperand(0);
    Value* rightValue = U->getOperand(1);
    Value* thirdValue = U->getOperand(2);
      
    VN.lookup_or_add(U);
    
    unsigned num = VN.lookup_or_add(U);
    
    if (isa<Instruction>(leftValue))
      if (!currExps.test(VN.lookup(leftValue))) {
        currExps.insert(leftValue);
        currExps.set(VN.lookup(leftValue));
      }
    if (isa<Instruction>(rightValue))
      if (!currExps.test(VN.lookup(rightValue))) {
        currExps.insert(rightValue);
        currExps.set(VN.lookup(rightValue));
      }
    if (isa<Instruction>(thirdValue))
      if (!currExps.test(VN.lookup(thirdValue))) {
        currExps.insert(thirdValue);
        currExps.set(VN.lookup(thirdValue));
      }
    
    if (!currExps.test(num)) {
      currExps.insert(U);
      currExps.set(num);
    }
    
  // Handle vararg ops
  } else if (GetElementPtrInst* U = dyn_cast<GetElementPtrInst>(I)) {
    Value* ptrValue = U->getPointerOperand();
      
    VN.lookup_or_add(U);
    
    unsigned num = VN.lookup_or_add(U);
    
    if (isa<Instruction>(ptrValue))
      if (!currExps.test(VN.lookup(ptrValue))) {
        currExps.insert(ptrValue);
        currExps.set(VN.lookup(ptrValue));
      }
    
    for (GetElementPtrInst::op_iterator OI = U->idx_begin(), OE = U->idx_end();
         OI != OE; ++OI)
      if (isa<Instruction>(*OI) && !currExps.test(VN.lookup(*OI))) {
        currExps.insert(*OI);
        currExps.set(VN.lookup(*OI));
      }
    
    if (!currExps.test(VN.lookup(U))) {
      currExps.insert(U);
      currExps.set(num);
    }
    
  // Handle opaque ops
  } else if (!I->isTerminator()){
    VN.lookup_or_add(&*I);
    
    currTemps.insert(&*I);
  }
    
  if (!I->isTerminator())
    if (!currAvail.test(VN.lookup(&*I))) {
      currAvail.insert(&*I);
      currAvail.set(VN.lookup(&*I));
    }
}


/// buildsets_anticout - When walking the postdom tree, calculate the ANTIC_OUT
/// set as a function of the ANTIC_IN set of the block's predecessors
bool SPGVNPRE::buildsets_anticout(BasicBlock* BB,
                                ValueNumberedSet& anticOut,
                                SmallPtrSet<BasicBlock*, 8>& visited) {
  if (BB->getTerminator()->getNumSuccessors() == 1) {
    if (BB->getTerminator()->getSuccessor(0) != BB &&
        visited.count(BB->getTerminator()->getSuccessor(0)) == 0) {
      return true;
    }
    else {
      phi_translate_set(anticipatedIn[BB->getTerminator()->getSuccessor(0)],
                        BB,  BB->getTerminator()->getSuccessor(0), anticOut);
    }
  } else if (BB->getTerminator()->getNumSuccessors() > 1) {
    BasicBlock* first = BB->getTerminator()->getSuccessor(0);
    for (ValueNumberedSet::iterator I = anticipatedIn[first].begin(),
         E = anticipatedIn[first].end(); I != E; ++I) {
      anticOut.insert(*I);
      anticOut.set(VN.lookup(*I));
    }
    
    for (unsigned i = 1; i < BB->getTerminator()->getNumSuccessors(); ++i) {
      BasicBlock* currSucc = BB->getTerminator()->getSuccessor(i);
      ValueNumberedSet& succAnticIn = anticipatedIn[currSucc];
      
      SmallVector<Value*, 16> temp;
      
      for (ValueNumberedSet::iterator I = anticOut.begin(),
           E = anticOut.end(); I != E; ++I)
        if (!succAnticIn.test(VN.lookup(*I)))
          temp.push_back(*I);
      for (SmallVector<Value*, 16>::iterator I = temp.begin(), E = temp.end();
           I != E; ++I) {
        anticOut.erase(*I);
        anticOut.reset(VN.lookup(*I));
      }
    }
  }
  
  return false;
}


/// buildsets_anticin - Walk the postdom tree, calculating ANTIC_OUT for
/// each block.  ANTIC_IN is then a function of ANTIC_OUT and the GEN
/// sets populated in buildsets_availout
unsigned SPGVNPRE::buildsets_anticin(BasicBlock* BB,
                               ValueNumberedSet& anticOut,
                               ValueNumberedSet& currExps,
                               SmallPtrSet<Value*, 16>& currTemps,
                               SmallPtrSet<BasicBlock*, 8>& visited) {
  ValueNumberedSet& anticIn = anticipatedIn[BB];
  unsigned old = anticIn.size();
      
  bool defer = buildsets_anticout(BB, anticOut, visited);
  if (defer)
    return 0;
  
  anticIn.clear();
  
  for (ValueNumberedSet::iterator I = anticOut.begin(),
       E = anticOut.end(); I != E; ++I) {
    anticIn.insert(*I);
    anticIn.set(VN.lookup(*I));
  }
  for (ValueNumberedSet::iterator I = currExps.begin(),
       E = currExps.end(); I != E; ++I) {
    if (!anticIn.test(VN.lookup(*I))) {
      anticIn.insert(*I);
      anticIn.set(VN.lookup(*I));
    }
  } 
  
  for (SmallPtrSet<Value*, 16>::iterator I = currTemps.begin(),
       E = currTemps.end(); I != E; ++I) {
    anticIn.erase(*I);
    anticIn.reset(VN.lookup(*I));
  }
  
  clean(anticIn);
  anticOut.clear();
  
  if (old != anticIn.size())
    return 2;
  else
    return 1;
}


/// buildsets - Phase 1 of the main algorithm.  Construct the AVAIL_OUT
/// and the ANTIC_IN sets.
void SPGVNPRE::buildsets(Function& F) {
  DenseMap<BasicBlock*, ValueNumberedSet> generatedExpressions;
  DenseMap<BasicBlock*, SmallPtrSet<Value*, 16> > generatedTemporaries;
  DominatorTree &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();   
  
  // Phase 1, Part 1: calculate AVAIL_OUT
  
  // Top-down walk of the dominator tree
  for (df_iterator<DomTreeNode*> DI = df_begin(DT.getRootNode()),
         E = df_end(DT.getRootNode()); DI != E; ++DI) {
    
    // Get the sets to update for this block
    ValueNumberedSet& currExps = generatedExpressions[DI->getBlock()];
    ValueNumberedSet& currPhis = generatedPhis[DI->getBlock()];
    SmallPtrSet<Value*, 16>& currTemps = generatedTemporaries[DI->getBlock()];
    ValueNumberedSet& currAvail = availableOut[DI->getBlock()];     
    
    BasicBlock* BB = DI->getBlock();
  
    // A block inherits AVAIL_OUT from its dominator
    if (DI->getIDom() != 0)
      currAvail = availableOut[DI->getIDom()->getBlock()];
    for (BasicBlock::iterator BI = BB->begin(), BE = BB->end();
         BI != BE; ++BI)
      buildsets_availout(BI, currAvail, currPhis, currExps,
                         currTemps);
      
  }
  // Phase 1, Part 2: calculate ANTIC_IN
  
  SmallPtrSet<BasicBlock*, 8> visited;
  SmallPtrSet<BasicBlock*, 4> block_changed;
  for (Function::iterator FI = F.begin(), FE = F.end(); FI != FE; ++FI)
    block_changed.insert(&*FI);
  
  bool changed = true;
  unsigned iterations = 0;
  
  while (changed) {
    changed = false;
    ValueNumberedSet anticOut;
    
    // Postorder walk of the CFG
    for (po_iterator<BasicBlock*> BBI = po_begin(&F.getEntryBlock()),
         BBE = po_end(&F.getEntryBlock()); BBI != BBE; ++BBI) {
      BasicBlock* BB = *BBI;
      
      if (block_changed.count(BB) != 0) {
        unsigned ret = buildsets_anticin(BB, anticOut,generatedExpressions[BB],
                                         generatedTemporaries[BB], visited);
      
        if (ret == 0) {
          changed = true;
          continue;
        } else {
          visited.insert(BB);
        
          if (ret == 2)
           for (pred_iterator PI = pred_begin(BB), PE = pred_end(BB);
                 PI != PE; ++PI) {
              block_changed.insert(*PI);
           }
          else
            block_changed.erase(BB);
        
          changed |= (ret == 2);
        }
      }
    }
    
    iterations++;
  }
}


bool SPGVNPRE::runOnFunction(Function &F) {
  // Clean out global sets from any previous functions
  VN.clear();
  createdExpressions.clear();
  availableOut.clear();
  anticipatedIn.clear();
  generatedPhis.clear();
 
  bool changed_function = false;
  
  // Phase 1: BuildSets
  // This phase calculates the AVAIL_OUT and ANTIC_IN sets
  buildsets(F);
  
  // // Phase 2: Insert
  // // This phase inserts values to make partially redundant values
  // // fully redundant
  // changed_function |= insertion(F);
  
  // // Phase 3: Eliminate
  // // This phase performs trivial full redundancy elimination
  // changed_function |= elimination();
  
  // // Phase 4: Cleanup
  // // This phase cleans up values that were created solely
  // // as leaders for expressions
  // cleanup();
  
  return changed_function;
}



char SPGVNPRE::ID = 0;
  
static RegisterPass<SPGVNPRE> X("spgvnpre",
                      "SPeculation-based Global Value Numbering/Partial Redundancy Elimination");
