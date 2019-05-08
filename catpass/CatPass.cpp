#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/CFG.h"
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
                        KILL[&i] = {};
                        continue;
                    }

                    CallInst *callInst = &cast<CallInst>(i);
                    Function *callee = callInst->getCalledFunction();
                    llvm::StringRef calleeName = callee->getName();

                    if (calleeName == "CAT_add"){
                        GEN[&i] = {&i};
                        KILL[&i] = VARAPPEARANCES[callInst->getArgOperand(0)];
                        KILL[&i].erase(&i);
                    } else if (calleeName == "CAT_set"){
                        GEN[&i] = {&i};
                        KILL[&i] = VARAPPEARANCES[callInst->getArgOperand(0)];
                        KILL[&i].erase(&i);
                    } else if (calleeName == "CAT_new"){
                        GEN[&i] = {&i};
                        KILL[&i] = VARAPPEARANCES[callInst];
                        KILL[&i].erase(&i);
                    } else if (calleeName == "CAT_get"){
                        GEN[&i] = {};
                        KILL[&i] = {};
                    } else if (calleeName == "CAT_sub"){
                        GEN[&i] = {&i};
                        KILL[&i] = VARAPPEARANCES[callInst->getArgOperand(0)];
                        KILL[&i].erase(&i);
                    }
                }
            }

            //H3 goes here

            std::map<Instruction*,std::set<Instruction*>> OUT;
            std::map<Instruction*,std::set<Instruction*>> IN;

            for(std::map<Instruction*,std::set<Instruction*>>::iterator iter = GEN.begin(); iter != GEN.end(); ++iter) {
                Instruction* k =  iter->first;
                OUT[k] = {};
                IN[k] = {};
            }

            bool foundChange;
            do {
                foundChange = false;
                for (auto &bb : F){
                    bool first = true;
                    Instruction* prevInst = NULL;
                    for (auto &i : bb){
                        Instruction* currInst= &i;
                        if (first){
                            for (BasicBlock *pred : llvm::predecessors(currInst->getParent())) {
                                Instruction* terminator = pred->getTerminator();
                                IN[currInst].insert(OUT[terminator].begin(), OUT[terminator].end());
                            }
                            first = false;
                            prevInst = currInst;
                        } else {
                            IN[currInst].insert(OUT[prevInst].begin(), OUT[prevInst].end());
                            prevInst = currInst;
                        }

                    std::set<Instruction*> TEMP = {};
                    std::set_difference(IN[currInst].begin(),
                                        IN[currInst].end(),
                                        KILL[currInst].begin(),
                                        KILL[currInst].end(),
                                        std::inserter(TEMP, TEMP.end()));
                    

                    TEMP.insert(GEN[currInst].begin(), GEN[currInst].end());

                    if (TEMP != OUT[currInst]){
                        foundChange = true;
                        OUT[currInst] = TEMP;
                    }
                        
                    }
                }
            } while(foundChange);

// Already have IN and OUT sets
// H4
            for (auto &bb : F){
                for (auto &i : bb){
                    if (!isa<CallInst>(i)){
                        continue;
                    }
                    CallInst *callInst = &cast<CallInst>(i);
                    Function *callee = callInst->getCalledFunction();
                    llvm::StringRef calleeName = callee->getName();

                    if (calleeName == "CAT_add"){
                        todo
                    } else if (calleeName == "CAT_set"){
                        todo
                    } else if (calleeName == "CAT_new"){
                        continue; // Nothing to do on CAT_new
                    } else if (calleeName == "CAT_get"){
                        auto var = callInst->getArgOperand(0);
                        int64_t temp;
                        bool seenMatch = false;
                        bool takeTheTemp = true;

                        for (std::set<Instruction*>::iterator it=IN[&i].begin(); it!=IN[&i].end(); ++it){ 
                            if (!isa<CallInst>(i)){
                                continue;
                            }
                            CallInst *callInst = &cast<CallInst>(i);
                            Function *callee = callInst->getCalledFunction();
                            llvm::StringRef calleeName = callee->getName();

                            if (calleeName == "CAT_add"){
                                if (callInst->getArgOperand(0) != var) continue; // Instruction does not contain variable we are looking to replace

                                if (seenMatch){
                                    takeTheTemp = false;
                                    break;
                                }
                                
                                break;
                                continue //TODO
                            } else if (calleeName == "CAT_set"){

                                if (callInst->getArgOperand(0) != var) continue; // Instruction does not contain variable we are looking to replace
                                auto val = callInst->getArgOperand(1);

                                if !(isa<ConstantInt>(*val)){
                                    break; // Not a constant, cant swap, BYE
                                }
                                
                                int64_t curr_temp = val->getSExtValue();

                                if (seenMatch){
                                    if (curr_temp == temp){
                                        continue;
                                    } else {
                                        takeTheTemp = false;
                                        break;
                                    }
                                } else {
                                    seenMatch = true;
                                    temp = curr_temp;
                                }
                            } else if (calleeName == "CAT_new"){
                                if (callInst != var) continue;

                                auto val = callInst->getArgOperand(0);

                                if !(isa<ConstantInt>(*val)){
                                    break; // Not a constant, cant swap, BYE
                                }
                                
                                int64_t curr_temp = val->getSExtValue();

                                if (seenMatch){
                                    if (curr_temp == temp){
                                        continue;
                                    } else {
                                        takeTheTemp = false;
                                        break;
                                    }
                                } else {
                                    seenMatch = true;
                                    temp = curr_temp;
                                }
                            } else if (calleeName == "CAT_get"){
                                continue //CAT_get doesnt modify anything so do nothing
                            } else if (calleeName == "CAT_sub"){
                                if (callInst->getArgOperand(0) != var) continue; // Instruction does not contain variable we are looking to replace

                                if (seenMatch){
                                    takeTheTemp = false;
                                    break;
                                }
                                
                                break;
                                continue //TODO
                            }
                        }







                    } else if (calleeName == "CAT_sub"){
                        todo
                    }
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
