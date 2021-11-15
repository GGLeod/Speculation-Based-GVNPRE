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

/* *******Implementation Starts Here******* */
// include necessary header files
/* *******Implementation Ends Here******* */

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
      DenseMap<Value*, uint32_t> valueNumbering;
      DenseMap<Expression, uint32_t> expressionNumbering;
  
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
      ValueTable() { nextValueNumber = 1; }
      uint32_t lookup_or_add(Value* V);
      uint32_t lookup(Value* V) const;
      void add(Value* V, uint32_t num);
      void clear();
      void erase(Value* v);
      unsigned size();
  };
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
      AU.addRequired<DominatorTree>();
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
  DominatorTree &DT = getAnalysis<DominatorTree>();   
  
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
  
  // Phase 2: Insert
  // This phase inserts values to make partially redundant values
  // fully redundant
  changed_function |= insertion(F);
  
  // Phase 3: Eliminate
  // This phase performs trivial full redundancy elimination
  changed_function |= elimination();
  
  // Phase 4: Cleanup
  // This phase cleans up values that were created solely
  // as leaders for expressions
  cleanup();
  
  return changed_function;
}



char SPGVNPRE::ID = 0;
  
static RegisterPass<SPGVNPRE> X("gvnpre",
                      "Global Value Numbering/Partial Redundancy Elimination");
