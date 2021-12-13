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
#include "llvm/Analysis/DominanceFrontier.h"
#include "llvm/IR/Instruction.h"
#include <unordered_map>

using namespace llvm;
using std::unordered_map;
using std::string;
using std::vector;

namespace {
struct Statics : public FunctionPass {
  static char ID;
  Statics() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {

    for (Function::iterator BBi = F.begin(); BBi!=F.end(); ++BBi){ // iterate BBs 
        BasicBlock* BB = &*BBi;
        for(auto Ii = BB->begin(); Ii!=BB->end(); ++Ii){
            Instruction* I = &*Ii;
            auto last = BB->end();
            last--;
            if(Ii!=last){
                errs() << *I << "\n";
                

                for(int i=0; i<I->getNumOperands(); i++){
                    Value* op = I->getOperand(i);
                    if(isa<Instruction>(op)){
                        Instruction* Iop = cast<Instruction>(op);
                        if(Iop->getParent() == I->getParent()){
                            BasicBlock * parent = I->getParent();

                            BasicBlock * newBB = SplitBlock(parent, I);
                            // errs() << "break\n";
                            
                            // errs() << *parent;

                            BBi = F.begin();
                            Ii = (*BBi).begin();
                            break;
                        }
                    }
                }
            }
            
        }

     
    }

    for (Function::iterator BBi = F.begin(); BBi!=F.end(); ++BBi){ // iterate BBs 
        errs() << *BBi;
    }

    return false;
  }
}; // end of struct Hello
}  // end of anonymous namespace

char Statics::ID = 0;
static RegisterPass<Statics> X("splitblock", "Split Block Pass");