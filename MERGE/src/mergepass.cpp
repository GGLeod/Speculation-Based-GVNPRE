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

    for (Function::iterator bbi = F.begin(); bbi!=F.end(); ++bbi){ // iterate BBs 
        BasicBlock* bb = &*bbi;
        if(succ_size(bb)!=1) continue;
        BasicBlock* succ = *succ_begin(bb);

        if(pred_size(succ)!=1) continue;

        for(auto Ii = succ->begin(); Ii!=succ->end(); ++Ii){
            Instruction* I = &*Ii;
            Instruction* newI = I->clone();
            auto lastinsert = bb->getInstList().end();
            lastinsert--;
            bb->getInstList().insert(lastinsert, newI);
            I->replaceAllUsesWith(newI);
        }

        
        auto last = bb->getInstList().end();
        last--;
        last->removeFromParent();
        last->deleteValue();

        for(auto succsucci = succ_begin(succ); succsucci != succ_end(succ); ++succsucci){
            BasicBlock* ssucc = *succsucci;
            for(auto Ii2 = ssucc->begin(); Ii2!=ssucc->end(); ++Ii2){
                Instruction* I2 = &*Ii2;
                if(isa<PHINode>(I2)){
                    PHINode* phi = cast<PHINode>(I2);
                    int index = phi->getBasicBlockIndex(succ);
                    phi->setIncomingBlock(index, bb);
                }
            }

        }
        succ->removeFromParent();
        succ->deleteValue();

    }

    for(auto bbi=F.begin(); bbi!=F.end(); ++bbi){
        errs() << *&*bbi;
    }
    

    return false;
  }
}; // end of struct Hello
}  // end of anonymous namespace

char Statics::ID = 0;
static RegisterPass<Statics> X("mergeblock", "Merge Simple Block Pass");