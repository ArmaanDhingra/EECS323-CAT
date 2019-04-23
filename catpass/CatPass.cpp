#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include <set>
#include <map>

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
      std::map<Value*,std::set<Instruction*>> VARAPPEARANCES;

      for (auto &bb : F){
        for (auto &i : bb){
          
          if (!isa<CallInst>(i)){
            continue;
          }

          CallInst *callInst = &cast<CallInst>(i);
          Function *callee = callInst->getCalledFunction();
          llvm::StringRef calleeName = callee->getName();

          if (calleeName == "CAT_add"){
            VARAPPEARANCES[callInst->getArgOperand(0)].insert(&i);
          } else if (calleeName == "CAT_set"){
            VARAPPEARANCES[callInst->getArgOperand(0)].insert(&i);
          } else if (calleeName == "CAT_new"){
            VARAPPEARANCES[callInst].insert(&i);
          } else if (calleeName == "CAT_get"){
            getCount++;
          } else if (calleeName == "CAT_sub"){
            VARAPPEARANCES[callInst->getArgOperand(0)].insert(&i);
          }
        }
      }

      // Loop through again to generate GEN and KILL sets
      // GEN[INSTRUCTION*]->set{INSTRUCTION*}
      // KILL[INSTRUCTION*]->set{INSTRUCTION*}
      std::map<Instruction*, std::set<Instruction*>> GEN;
      std::map<Instruction*, std::set<Instruction*>> KILL;
      for (auto &bb : F){
        for (auto &i : bb){
          if (!isa<CallInst>(i)){
            GEN[&i] = {};
            KILL[&i] = {}:

            errs()<<"INSTRUCTION: " << i << "\n";
            errs() << "***************** GEN\n{\n";
            for (std::set<Instruction*>::iterator it=GEN[&i].begin(); it!=GEN[&i].end(); ++it){
              errs() << *(*it) << "\n"; 
              }
            errs() << "\n}\n**************************************\n***************** KILL\n{\n";
            for (std::set<Instruction*>::iterator it=KILL[&i].begin(); it!=KILL[&i].end(); ++it){
              errs() << *(*it) << "\n"; 
              }
            errs() << "\n}\n**************************************\n\n\n\n";

            continue;
          }

          CallInst *callInst = &cast<CallInst>(i);
          Function *callee = callInst->getCalledFunction();
          llvm::StringRef calleeName = callee->getName();

          if (calleeName == "CAT_add"){
            GEN[&i] = {&i}
            KILL[&i] = VARAPPEARANCES[callInst->getArgOperand(0)];
            KILL[&i].erase(&i);
          } else if (calleeName == "CAT_set"){
            GEN[&i] = {&i}
            KILL[&i] = VARAPPEARANCES[callInst->getArgOperand(0)];
            KILL[&i].erase(&i);
          } else if (calleeName == "CAT_new"){
            GEN[&i] = {&i}
            KILL[&i] = VARAPPEARANCES[callInst];
            KILL[&i].erase(&i);
          } else if (calleeName == "CAT_get"){
            GEN[&i] = {};
            KILL[&i] = {}:
          } else if (calleeName == "CAT_sub"){
            GEN[&i] = {&i}
            KILL[&i] = VARAPPEARANCES[callInst->getArgOperand(0)];
            KILL[&i].erase(&i);
          }

            errs()<<"INSTRUCTION: " << i << "\n";
            errs() << "***************** GEN\n{\n";
            for (std::set<Instruction*>::iterator it=GEN[&i].begin(); it!=GEN[&i].end(); ++it){
              errs() << *(*it) << "\n"; 
              }
            errs() << "\n}\n**************************************\n***************** KILL\n{\n";
            for (std::set<Instruction*>::iterator it=KILL[&i].begin(); it!=KILL[&i].end(); ++it){
              errs() << *(*it) << "\n"; 
              }
            errs() << "\n}\n**************************************\n\n\n\n";

        }
      }
      

      // for (std::map<Value*,std::set<Instruction*>>::iterator it=VARAPPEARANCES.begin(); it!=VARAPPEARANCES.end(); ++it){
      //   errs() << "VARIABLE: " << (it->first) << "\n";
      //   errs() << "Appearances: { ";
      //   for (std::set<Instruction*>::iterator nico=it->second.begin(); nico!=it->second.end(); ++nico){
      //      errs() << *(*nico) << ", "; 
      //   }
      //   errs() << "}\n\n";
      // }
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
