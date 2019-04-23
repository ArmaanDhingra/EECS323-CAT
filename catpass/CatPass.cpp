#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include <set>

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
      std::string currKill = "";

      std::string funName = F.getName();
      errs()<<"START FUNCTION: " << funName << "\n";
      for (auto &bb : F){
        std::set<CallInst*> VARS;
        // std::map<int,std::vector<std::string>> OUT;
        // std::map<int,int(*)[3]> first;
        errs () << bb.size() << "\n";
        for (auto &i : bb){
          errs()<<"INSTRUCTION: " << i << "\n";
          // errs() << "***************** GEN\n{\n" << currKill <<"\n}\n**************************************\n***************** KILL\n{\n"<<currKill<<"\n}\n**************************************\n\n\n\n";
          if (!isa<CallInst>(i)){
            continue;
          }

          CallInst *callInst = &cast<CallInst>(i);
          Function *callee = callInst->getCalledFunction();
          llvm::StringRef calleeName = callee->getName();

          // if (calleeName == "CAT_add"){
          //   addCount++;
          //   errs() << "CAT_add ARG OPERAND: " << callInst->getArgOperand(0) << "\n";
          //   // errs() << callInst->getArgOperand(1) << "\n";
          //   // errs() << callInst->getArgOperand(2) << "\n";


          // } else if (calleeName == "CAT_set"){
          //   setCount++;
          //   errs() << "CAT_set ARG OPERAND: " << callInst->getArgOperand(0) << "\n";
          // } else if (calleeName == "CAT_new"){
          //   errs() << "CAT_new ARG SET: " << callInst << " | " << i << "\n";
          //   newCount++;
          // } else if (calleeName == "CAT_get"){
          //   getCount++;
          // } else if (calleeName == "CAT_sub"){
          //   subCount++;
          //   errs() << "CAT_sub ARG OPERAND: " << callInst->getArgOperand(0) << "\n";
          // }
        }
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
