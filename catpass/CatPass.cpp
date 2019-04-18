#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"

using namespace llvm;

namespace {
  struct CAT : public FunctionPass {
    static char ID; 

    CAT() : FunctionPass(ID) {}

    // This function is invoked once at the initialization phase of the compiler
    // The LLVM IR of functions isn't ready at this point
    bool doInitialization (Module &M) override {
      //errs() << "Hello LLVM World at \"doInitialization\"\n" ;
      return false;
    }

    // This function is invoked once per function compiled
    // The LLVM IR of the input functions is ready and it can be analyzed and/or transformed
    bool runOnFunction (Function &F) override {


      int addCount = 0;
      int setCount = 0;
      int newCount = 0;
      int getCount = 0;
      int subCount = 0;

      std::string funName = F.getName();

      for (auto &bb : F){
        for (auto &i : bb){
          if (!isa<CallInst>(i)){
            continue;
          }

          CallInst *callInst = &cast<CallInst>(i);
          Function *callee = callInst->getCalledFunction();
          llvm::StringRef calleeName = callee->getName();

          if (calleeName == "CAT_add"){
            addCount++;
          } else if (calleeName == "CAT_set"){
            setCount++;
          } else if (calleeName == "CAT_new"){
            newCount++;
          } else if (calleeName == "CAT_get"){
            getCount++;
          } else if (calleeName == "CAT_sub"){
            subCount++;
          }
        }
      }

      if (addCount){
        errs()<<"H1: \""<<funName<<"\": CAT_add: " << addCount<<"\n";
      }
      if (subCount){
        errs()<<"H1: \""<<funName<<"\": CAT_sub: " << subCount<<"\n";
      }
      if (newCount){
        errs()<<"H1: \""<<funName<<"\": CAT_new: " << newCount<<"\n";
      }
      if (getCount){
        errs()<<"H1: \""<<funName<<"\": CAT_get: " << getCount<<"\n";
      }
      if (setCount){
        errs()<<"H1: \""<<funName<<"\": CAT_set: " << setCount<<"\n";
      }
      
      return false;

    }

    // We don't modify the program, so we preserve all analyses.
    // The LLVM IR of functions isn't ready at this point
    void getAnalysisUsage(AnalysisUsage &AU) const override {
     // errs() << "Hello LLVM World at \"getAnalysisUsage\"\n" ;
      AU.setPreservesAll();
    }
  };
}

// Next there is code to register your pass to "opt"
char CAT::ID = 0;
static RegisterPass<CAT> X("CAT", "Homework for the CAT class");

// Next there is code to register your pass to "clang"
static CAT * _PassMaker = NULL;
static RegisterStandardPasses _RegPass1(PassManagerBuilder::EP_OptimizerLast,
    [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
        if(!_PassMaker){ PM.add(_PassMaker = new CAT());}}); // ** for -Ox
static RegisterStandardPasses _RegPass2(PassManagerBuilder::EP_EnabledOnOptLevel0,
    [](const PassManagerBuilder&, legacy::PassManagerBase& PM) {
        if(!_PassMaker){ PM.add(_PassMaker = new CAT()); }}); // ** for -O0
