#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include <vector>
#include <tuple>
#include <set>
#include <map>
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AliasSetTracker.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/UnrollLoop.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"


using namespace llvm;
using namespace std;

namespace
{
  struct CAT : public FunctionPass
  {
    static char ID;
    Module *currM;

    CAT() : FunctionPass(ID) {}

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization(Module &M) override
    {
      //errs() << "Hello LLVM World at \"doInitialization\"\n" ;
      currM = &M;

      bool modified = transformFunctions(M);

      return modified;
    }

    bool transformFunctions(Module &M)
    {
      bool modified = false;
      for (auto &F : M)
      {
        modified |= transformFunction(M, F);
      }

      return modified;
    }

    bool transformFunction(Module &M, Function &F)
    {
      std::vector<Instruction *> toDelete;
      errs() << "START" << F.getName() << "\n";

      bool modified = false;
      bool inlined = false;
      for (auto &B : F)
      {
        for (auto &I : B)
        {
          if (auto call = dyn_cast<CallInst>(&I))
          {
            auto *callee = call->getCalledFunction();
            if (callee == NULL || callee->empty())
            continue;
            errs() << "Inlining " << callee->getName() << " to " << F.getName() << "\n";
            InlineFunctionInfo IFI;
            inlined |= InlineFunction(call, IFI);
            if (inlined)
            {
              modified = true;
              break;
            }
            else
            {
              errs() << "    Failed to inline\n";
            }
          }
        }
      }
      if (inlined)
      {
        transformFunction(M, F);
      }
      return modified;
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction(Function &F) override
    {

      auto& LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
      auto& DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
      auto& SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
      auto &AC = getAnalysis<AssumptionCacheTracker>().getAssumptionCache(F);

      OptimizationRemarkEmitter ORE(&F);
      errs() << "Function: " << F.getName() << "\n";
      for (auto i : LI){
        auto loop = &*i;
        analyzeLoop(LI, loop, DT, SE, AC, ORE);
      }

      std::set<Value *> ignoreList;

      std::string funName = F.getName();
      errs() << " ________________________\n";
      errs() << "START FUNCTION: " << funName << "\n\n";
      std::map<Value *, std::set<Instruction *>> VARAPPEARANCES;

      errs() << "Function \"" << F.getName() << "\"\n";

      AliasAnalysis &aliasAnalysis = getAnalysis<AAResultsWrapperPass>().getAAResults();

      vector<Instruction *> pointers;
      vector<Instruction *> memInsts;

      std::map<Instruction *, std::set<Instruction *>> GEN;
      std::map<Instruction *, std::set<Instruction *>> KILL;

      for (auto &B : F)
      {
        for (auto &I : B)
        {
          if (I.getType()->isPointerTy() &&
          isa<CallInst>(&I))
          {
            pointers.push_back(&I);
            continue;
          }

          if (isa<LoadInst>(&I) ||
          isa<StoreInst>(&I))
          {
            memInsts.push_back(&I);
            continue;
          }
        }
      }

      errs() << " ### Pointers\n";
      for (auto &pointer : pointers)
      {
        GEN[pointer] = {};
        KILL[pointer] = {};

        auto ptrType = pointer->getType();
        auto sizePointer = F.getParent()->getDataLayout().getTypeStoreSize(ptrType);
        errs() << "   Pointer: \"" << *pointer << "     |       " << pointer << "\"\n";
        errs() << "     Size: " << sizePointer << " Bytes\n";

        for (auto &pointer2 : pointers)
        {
          if (pointer == pointer2)
          continue;

          auto ptrType2 = pointer2->getType();
          auto sizePointer2 = F.getParent()->getDataLayout().getTypeStoreSize(ptrType2);
          errs() << "     Pointer2: \"" << *pointer2 << "     |       " << pointer2 << "\"\n";
          errs() << "       Size: " << sizePointer2 << " Bytes\n";

          switch (aliasAnalysis.alias(pointer, sizePointer, pointer2, sizePointer2))
          {
            case NoAlias:
            errs() << "     No alias\n";
            break;

            case MayAlias:
            errs() << "     May alias\n";
            GEN[pointer].insert(pointer2);
            break;

            case PartialAlias:
            errs() << "     Partial alias\n";
            break;

            case MustAlias:
            errs() << "     Must alias\n";
            GEN[pointer].insert(pointer2);
            KILL[pointer].insert(pointer2);
            break;

            default:
            abort();
          }
        }
      }

      errs() << "\n\n";

      errs() << " ### Memory accesses\n";
      for (auto &memInst : memInsts)
      {
        GEN[memInst] = {};
        KILL[memInst] = {};

        errs() << "   Mem inst: \"" << *memInst << "    |      " << memInst << "\"\n";

        for (auto &memInst2 : memInsts)
        {
          if (memInst == memInst2)
          continue;
          errs() << "     Mem inst2: \"" << *memInst2 << "    |      " << memInst2 << "\"\n";
          if (!(memInst && memInst2))
          continue;

          switch (aliasAnalysis.alias(MemoryLocation::get(memInst), MemoryLocation::get(memInst2)))
          {
            case NoAlias:
            errs() << "     No alias\n";
            break;

            case MayAlias:
            errs() << "     May alias\n";
            GEN[memInst].insert(memInst2);
            break;

            case PartialAlias:
            errs() << "     Partial alias\n";
            break;

            case MustAlias:
            errs() << "     Must alias\n";
            GEN[memInst].insert(memInst2);
            KILL[memInst].insert(memInst2);
            break;

            default:
            abort();
          }
        }
      }

      errs() << "\n\n";

      errs() << " ### Mod/ref\n";

      for (auto &memInst : memInsts)
      {
        errs() << "   Mem inst: \"" << *memInst << "\"\n";

        for (auto &pointer : pointers)
        {

          // if (!(memInst && pointer))
          //     continue;

          auto ptrType = pointer->getType();
          auto sizePointer = F.getParent()->getDataLayout().getTypeStoreSize(ptrType);

          errs() << "   Pointer: \"" << *pointer << "\"\n";
          errs() << "     Size: " << sizePointer << " Bytes\n";

          switch (aliasAnalysis.getModRefInfo(memInst, pointer, sizePointer))
          {
            case ModRefInfo::MustMod:
            errs() << "     Must Mod\n";
            GEN[memInst].insert(pointer);
            KILL[memInst].insert(pointer);
            KILL[pointer].insert(memInst);
            break;
            case ModRefInfo::MustRef:
            errs() << "     Must Ref\n";
            break;
            case ModRefInfo::MustModRef:
            errs() << "     Must ModRef\n";
            GEN[memInst].insert(pointer);
            KILL[memInst].insert(pointer);
            KILL[pointer].insert(memInst);
            break;

            case ModRefInfo::NoModRef:
            errs() << "     NoModRef\n";
            // KILL[memInst].insert(pointer);
            // KILL[pointer].insert(memInst);

            break;

            case ModRefInfo::Mod:
            errs() << "     Mod\n";
            GEN[memInst].insert(pointer);
            KILL[memInst].insert(pointer);
            KILL[pointer].insert(memInst);
            break;
            case ModRefInfo::Ref:
            errs() << "     Ref\n";
            GEN[memInst].insert(pointer);
            break;
            case ModRefInfo::ModRef:
            errs() << "     ModRef\n";
            GEN[memInst].insert(pointer);
            KILL[memInst].insert(pointer);
            KILL[pointer].insert(memInst);
            break;
            default:
            errs() << " something else found \n";
            abort();
          }
        }
      }
      errs() << "\n\n";

      for (auto &bb : F)
      {
        for (auto &i : bb)
        {
          if (!isa<CallInst>(i))
          {
            // if we have a store instruction (test13) add its arg to ignore list too
            if (isa<StoreInst>(i))
            {
              StoreInst *storeInst = &cast<StoreInst>(i);
              Value *valueStored = storeInst->getValueOperand();
              // ignoreList.insert(valueStored);
            }
            continue;
          }
          CallInst *callInst = &cast<CallInst>(i);
          Function *callee = callInst->getCalledFunction();
          llvm::StringRef calleeName = callee->getName();

          if (calleeName == "CAT_add")
          {
            VARAPPEARANCES[callInst->getArgOperand(0)].insert(&i);
            // errs() << "CAT ADD MEMORY IS " << callInst->getArgOperand(0) << "\n";
          }
          else if (calleeName == "CAT_set")
          {
            VARAPPEARANCES[callInst->getArgOperand(0)].insert(&i);
          }
          else if (calleeName == "CAT_new")
          {
            VARAPPEARANCES[callInst].insert(&i);
          }
          else if (calleeName == "CAT_get")
          {
            continue;
          }
          else if (calleeName == "CAT_sub")
          {
            VARAPPEARANCES[callInst->getArgOperand(0)].insert(&i);
          }
          else
          {
            if (aliasAnalysis.onlyReadsMemory(callInst))
            {
              continue;
            }

            // If not a CAT_inst, add all its variables as ignore
            unsigned numArgs = callInst->getNumOperands();
            for (int i = 0; i < numArgs - 1; i++)
            {
              if (VARAPPEARANCES.find(callInst->getArgOperand(i)) != VARAPPEARANCES.end())
              {
                ignoreList.insert(callInst->getArgOperand(i));
                errs() << "Adding " << callInst->getArgOperand(i) << " to ignore list \n\n";
              }
            }
          }
        }
      }

      // Loop through again to generate GEN and KILL sets
      // GEN[INSTRUCTION*]->set{INSTRUCTION*}
      // KILL[INSTRUCTION*]->set{INSTRUCTION*}
      for (auto &bb : F)
      {
        for (auto &i : bb)
        {
          if (!isa<CallInst>(i))
          {
            // GEN[&i] = {};
            // KILL[&i] = {};
            continue;
          }

          CallInst *callInst = &cast<CallInst>(i);
          Function *callee = callInst->getCalledFunction();
          llvm::StringRef calleeName = callee->getName();

          if (calleeName == "CAT_add")
          {

            GEN[&i] = {&i};
            KILL[&i] = VARAPPEARANCES[callInst->getArgOperand(0)];
            KILL[&i].erase(&i);
          }
          else if (calleeName == "CAT_set")
          {
            GEN[&i] = {&i};
            KILL[&i] = VARAPPEARANCES[callInst->getArgOperand(0)];
            KILL[&i].erase(&i);
          }
          else if (calleeName == "CAT_new")
          {
            GEN[&i] = {&i};
            KILL[&i] = VARAPPEARANCES[callInst];
            KILL[&i].erase(&i);
          }
          else if (calleeName == "CAT_get")
          {
            GEN[&i] = {};
            KILL[&i] = {};
          }
          else if (calleeName == "CAT_sub")
          {
            GEN[&i] = {&i};
            KILL[&i] = VARAPPEARANCES[callInst->getArgOperand(0)];
            KILL[&i].erase(&i);
          }
        }
      }

      //H3 goes here

      std::map<Instruction *, std::set<Instruction *>> OUT;
      std::map<Instruction *, std::set<Instruction *>> IN;

      for (std::map<Instruction *, std::set<Instruction *>>::iterator iter = GEN.begin(); iter != GEN.end(); ++iter)
      {
        Instruction *k = iter->first;
        OUT[k] = {};
        IN[k] = {};
      }

      bool foundChange;
      do
      {
        foundChange = false;
        for (auto &bb : F)
        {
          bool first = true;
          Instruction *prevInst = NULL;
          for (auto &i : bb)
          {
            Instruction *currInst = &i;
            if (first)
            {
              for (BasicBlock *pred : llvm::predecessors(currInst->getParent()))
              {
                Instruction *terminator = pred->getTerminator();
                IN[currInst].insert(OUT[terminator].begin(), OUT[terminator].end());
              }
              first = false;
              prevInst = currInst;
            }
            else
            {
              IN[currInst].insert(OUT[prevInst].begin(), OUT[prevInst].end());
              prevInst = currInst;
            }

            std::set<Instruction *> TEMP = {};
            std::set_difference(IN[currInst].begin(),
            IN[currInst].end(),
            KILL[currInst].begin(),
            KILL[currInst].end(),
            std::inserter(TEMP, TEMP.end()));

            TEMP.insert(GEN[currInst].begin(), GEN[currInst].end());

            if (TEMP != OUT[currInst])
            {
              foundChange = true;
              OUT[currInst] = TEMP;
            }
          }
        }
      } while (foundChange);

      // Already have IN and OUT sets
      // H4
      // typedef std::vector< std::tuple<BasicBlock, Instruction*, ConstantInt*> > mytuple;
      // mytuple replace;

      std::vector<BasicBlock *> replace_bb;
      std::vector<Instruction *> replace_i;
      std::vector<ConstantInt *> replace_ci;

      ConstantInt *arg;

      for (auto &bb : F)
      {
        for (auto &i : bb)
        {
          if (!isa<CallInst>(i))
          {
            continue;
          }

          CallInst *callInst = &cast<CallInst>(i);
          Function *callee = callInst->getCalledFunction();
          llvm::StringRef calleeName = callee->getName();

          if (calleeName == "CAT_add")
          {
            errs() << callInst->getArgOperand(0) << " -- modified by CAT_add \n\n";
            continue; //TODO
          }
          else if (calleeName == "CAT_sub")
          {
            errs() << callInst->getArgOperand(0) << " -- modified by CAT_sub \n\n";
          }
          else if (calleeName == "CAT_set")
          {
            continue;
          }
          else if (calleeName == "CAT_new")
          {
            errs() << callInst << " -- defined by CAT_new \n\n";
            continue; // Nothing to do on CAT_new
          }
          else if (calleeName == "CAT_get")
          {
            std::set<Value *> varsToLookAt;
            std::set<int64_t> possibleTemps;

            auto var = callInst->getArgOperand(0);
            errs() << var << " -- fetched by CAT_get\n\n";

            // PLAYING AROUND WITH PHI NODE THING

            if (auto phi = dyn_cast<PHINode>(var))
            {
              errs() << " And it is a phi node \n\n";
              unsigned numVals;
              numVals = phi->getNumIncomingValues();
              errs() << " It has " << numVals << " number of values \n";
              errs() << " and they are : \n";

              // We breakaway / stop looking for a replacement if at least one of the phiVals is an argument or is in the ignore list
              bool breakaway = false;

              for (int i = 0; i < numVals; i++)
              {
                auto phiVal = phi->getIncomingValue(i);
                varsToLookAt.insert(phiVal);
                errs() << phiVal << "\n";
                if (isa<Argument>(phiVal))
                {
                  errs() << phiVal << " is an arg ! \n\n";
                  breakaway = true;
                  break;
                  continue;
                }
                if (ignoreList.find(phiVal) != ignoreList.end())
                {
                  breakaway = true;
                  break;
                }
                else
                {
                  varsToLookAt.insert(phiVal);
                }
              }
              if (breakaway)
              continue;
              errs() << "\n";
            }
            else
            {
              varsToLookAt.insert(var);
            }
            int64_t finaltemp;

            bool takeTheTemp = true;

            for (auto var : varsToLookAt)
            {
              errs() << "VAR VAR VAR \n\n";
              if (isa<CallInst>(*var))
              {
                errs() << "FOUND A CALL INST \n\n";
              }
              else
              {
                errs() << " WE IN HERE AT LEAST";
                takeTheTemp = false;
                break;
              }

              int64_t temp;
              bool seenMatch = false;
              errs() << "Looking at " << var << ": \n\n";
              for (std::set<Instruction *>::iterator it = IN[&i].begin(); it != IN[&i].end(); ++it)
              {
                if (!isa<CallInst>(*(*it)))
                {
                  continue;
                }

                CallInst *callInst = &cast<CallInst>(*(*it));
                Function *callee = callInst->getCalledFunction();
                llvm::StringRef calleeName = callee->getName();

                // errs() << calleeName << " are in in set\n\n";

                if (calleeName == "CAT_add")
                {
                  if (callInst->getArgOperand(0) != var)
                  continue; // Instruction does not contain variable we are looking to replace

                  if (seenMatch)
                  {
                    takeTheTemp = false;
                    break;
                  }

                  break;
                  continue; //TODO
                }
                else if (calleeName == "CAT_set")
                {
                  // errs () << var << "\n\n" << callInst->getArgOperand(0) << "\n\n";
                  if (callInst->getArgOperand(0) != var)
                  continue; // Instruction does not contain variable we are looking to replace

                  auto val = callInst->getArgOperand(1);

                  if (!isa<ConstantInt>(*val))
                  {
                    break; // Not a constant, cant swap, BYE
                  }

                  int64_t curr_temp;
                  arg = dyn_cast<ConstantInt>(val);
                  curr_temp = arg->getSExtValue();

                  if (seenMatch)
                  {
                    if (curr_temp == temp)
                    {
                      continue;
                    }
                    else
                    {
                      takeTheTemp = false;
                    }
                  }
                  else
                  {
                    seenMatch = true;
                    temp = curr_temp;
                  }
                }
                else if (calleeName == "CAT_new")
                {
                  errs() << *callInst << "\n";

                  if (callInst != var)
                  {
                    // errs() << *callInst << "\n";
                    errs() << "Call inst is not equal to the phinode var \n\n";
                    continue;
                  }
                  // errs() << "WE HAVE A MATCH -- ";

                  auto val = callInst->getArgOperand(0);

                  if (!isa<ConstantInt>(*val))
                  {
                    takeTheTemp = false;
                    errs() << "Val is not a constant int \n";
                    break; // Not a constant, cant swap, BYE
                  }

                  int64_t curr_temp;
                  arg = dyn_cast<ConstantInt>(val);
                  curr_temp = arg->getSExtValue();

                  if (seenMatch)
                  {
                    if (curr_temp == temp)
                    {
                      continue;
                    }
                    else
                    {
                      takeTheTemp = false;
                      break;
                    }
                  }
                  else
                  {
                    errs() << "Taking the currtemp: " << curr_temp << "\n\n";
                    seenMatch = true;
                    temp = curr_temp;
                  }
                }
                else if (calleeName == "CAT_get")
                {

                  continue; //CAT_get doesnt modify anything so do nothing
                }
                else if (calleeName == "CAT_sub")
                {
                  if (callInst->getArgOperand(0) != var)
                  continue; // Instruction does not contain variable we are looking to replace

                  if (seenMatch)
                  {
                    takeTheTemp = false;
                    break;
                  }
                }
              }
              if (takeTheTemp && seenMatch)
              {
                finaltemp = temp;
                possibleTemps.insert(temp);
              }
            }

            // temp holds our constant
            // val holds the variable we wish to replace
            // i is the instruction that has that variable

            if (possibleTemps.size() == 1 && takeTheTemp)
            {
              errs() << "WE HAVE A MATCH -- REPLACE THE INSTRUCTION\n";
              // errs() << arg->getType() << "\n\n";
              if (calleeName == "CAT_new")
              {
                errs() << "\n Replacing a CAT_new -- should not be run \n\n";
                errs() << &i << "\n\n";
              }
              else if (calleeName == "CAT_get")
              {
                if (ignoreList.find(callInst->getArgOperand(0)) != ignoreList.end())
                {
                  errs() << "Did not replace because " << callInst->getArgOperand(0) << " is in ignoreList\n\n";
                  continue;
                }
                errs() << callInst->getArgOperand(0) << " = " << finaltemp << "\n\n";
              }

              ConstantInt *newArg = ConstantInt::get(arg->getType(), finaltemp);
              // BasicBlock::iterator ii(i);
              // ReplaceInstWithValue(bb.getInstList(), ii, newArg);
              // replace.push_back(std::tuple<BasicBlock, Instruction*, ConstantInt*>(bb, i, newArg));
              replace_bb.push_back(&bb);
              replace_i.push_back(&i);
              replace_ci.push_back(newArg);
            }
          }
        }
      }

      for (int i = 0; i < replace_bb.size(); i++)
      {
        BasicBlock::iterator ii(*(replace_i[i]));
        ReplaceInstWithValue(replace_bb[i]->getInstList(), ii, replace_ci[i]);
      }

      return false;
    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override
    {
      // errs() << "Hello LLVM World at \"getAnalysisUsage\"\n" ;
      AU.addRequired<AAResultsWrapperPass>();
      // AU.setPreservesAll();
      AU.addRequired<AssumptionCacheTracker>();
      AU.addRequired<DominatorTreeWrapperPass>();
      AU.addRequired<LoopInfoWrapperPass>();
      AU.addRequired<ScalarEvolutionWrapperPass>();
      return;
    }

  private:
    bool analyzeLoop (
      LoopInfo &LI,
      Loop *loop,
      DominatorTree &DT,
      ScalarEvolution &SE,
      AssumptionCache &AC,
      OptimizationRemarkEmitter &ORE
      ){

      /*
       * Check if the loop has been normalized.
       */
      if (  loop->isLoopSimplifyForm()  &&
            loop->isLCSSAForm(DT)       ){

        /*
         * We found a loop that has been normalized.
         */
        errs() << " Loop: " ;
        loop->print(errs());

        /*
         * Identify the trip count.
         */
        auto tripCount = SE.getSmallConstantTripCount(loop);
        if (tripCount > 0){

          /*
           * The loop has a constant trip count.
           */
          errs() << "   Trip count: " << tripCount << "\n";

          /*
           * Try to unroll the loop
           */
          auto forceUnroll = false;
          auto allowRuntime = false;
          auto allowExpensiveTripCount = true;
          auto preserveCondBr = false;
          auto preserveOnlyFirst = false;
          auto unrolled = UnrollLoop(
            loop, 2,
            tripCount,
            forceUnroll,
            allowRuntime, allowExpensiveTripCount,
            preserveCondBr, preserveOnlyFirst,
            0, 0,
            false,
            &LI, &SE, &DT, &AC, &ORE,
            true);

          /*
           * Check if the loop unrolled.
           */
          switch (unrolled){
            case LoopUnrollResult::FullyUnrolled :
              errs() << "   Fully unrolled\n";
              return true ;

            case LoopUnrollResult::PartiallyUnrolled :
              errs() << "   Partially unrolled\n";
              return true ;

            case LoopUnrollResult::Unmodified :
              errs() << "   Not unrolled\n";
              break ;

            default:
              abort();
          }
        }
      }

      /*
       * Analyze sub-loops of the loop given as input.
       */
      auto subLoops = loop->getSubLoops();
      for (auto j : subLoops){
        auto subloop = &*j;
        if (analyzeLoop(LI, subloop, DT, SE, AC, ORE)){
          return true;
        }
      }

    return false;
  }
  };
} // namespace

// Next there is code to register your pass to "opt"
char CAT::ID = 0;
static RegisterPass<CAT> X("CAT", "Homework for the CAT class");

// Next there is code to register your pass to "clang"
static CAT *_PassMaker = NULL;
static RegisterStandardPasses _RegPass1(PassManagerBuilder::EP_OptimizerLast,
  [](const PassManagerBuilder &, legacy::PassManagerBase &PM) {
    if(!_PassMaker){ PM.add(_PassMaker = new CAT());} }); // ** for -Ox
    static RegisterStandardPasses _RegPass2(PassManagerBuilder::EP_EnabledOnOptLevel0,
      [](const PassManagerBuilder &, legacy::PassManagerBase &PM) {
        if(!_PassMaker){ PM.add(_PassMaker = new CAT()); } }); // ** for -O0
