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
            errs()<<"START FUNCTION: " << funName << "\n\n";
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
                        continue;
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
            // typedef std::vector< std::tuple<BasicBlock, Instruction*, ConstantInt*> > mytuple;
            // mytuple replace;

            std::vector<BasicBlock*> replace_bb;
            std::vector<Instruction*> replace_i;
            std::vector<ConstantInt*> replace_ci;

            ConstantInt* arg;


            for (auto &bb : F){
                for (auto &i : bb){
                    if (!isa<CallInst>(i)){
                        continue;
                    }

                    CallInst *callInst = &cast<CallInst>(i);
                    Function *callee = callInst->getCalledFunction();
                    llvm::StringRef calleeName = callee->getName();

                    if (calleeName == "CAT_add"){
                        errs () << callInst->getArgOperand(0) << " -- modified by CAT_add \n\n";
                        continue; //TODO
                    }else if (calleeName == "CAT_sub"){
                        errs () << callInst->getArgOperand(0) << " -- modified by CAT_sub \n\n";
                    }else if (calleeName == "CAT_set"){
                        continue;
                    } else if (calleeName == "CAT_new"){
                        errs() << callInst << " -- defined by CAT_new \n\n";
                        continue; // Nothing to do on CAT_new
                    } else if (calleeName == "CAT_get"){
                        auto var = callInst->getArgOperand(0);
                        errs() << var << " -- fetched by CAT_get\n\n";

                        int64_t temp;
                        bool seenMatch = false;
                        bool takeTheTemp = true;

                        for (std::set<Instruction*>::iterator it=IN[&i].begin(); it!=IN[&i].end(); ++it){
                            if (!isa<CallInst>(*(*it))){
                                continue;
                            }
                            CallInst *callInst = &cast<CallInst>(*(*it));
                            Function *callee = callInst->getCalledFunction();
                            llvm::StringRef calleeName = callee->getName();

                            // errs() << calleeName << " are in in set\n\n";
                            
                            if (calleeName == "CAT_add"){
                                if (callInst->getArgOperand(0) != var) continue; // Instruction does not contain variable we are looking to replace

                                if (seenMatch){
                                    takeTheTemp = false;
                                    break;
                                }
                                
                                break;
                                continue; //TODO
                            } else if (calleeName == "CAT_set"){
                                // errs () << var << "\n\n" << callInst->getArgOperand(0) << "\n\n";
                                if (callInst->getArgOperand(0) != var) continue; // Instruction does not contain variable we are looking to replace
                                
                                auto val = callInst->getArgOperand(1);

                                if (!isa<ConstantInt>(*val)){
                                    break; // Not a constant, cant swap, BYE
                                }
                                
                                int64_t curr_temp;
                                arg = dyn_cast<ConstantInt>(val);
                                curr_temp = arg->getSExtValue();

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
                                // errs() << "WE HAVE A MATCH -- ";

                                auto val = callInst->getArgOperand(0);

                                if (!isa<ConstantInt>(*val)){
                                    break; // Not a constant, cant swap, BYE
                                }
                                
                                int64_t curr_temp;
                                arg = dyn_cast<ConstantInt>(val);
                                curr_temp = arg->getSExtValue();

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
                                continue; //CAT_get doesnt modify anything so do nothing
                            } else if (calleeName == "CAT_sub"){
                                if (callInst->getArgOperand(0) != var) continue; // Instruction does not contain variable we are looking to replace

                                if (seenMatch){
                                    takeTheTemp = false;
                                    break;
                                }
                                
                                break;
                                continue; //TODO
                            }
                        }

                        // temp holds our constant
                        // val holds the variable we wish to replace
                        // i is the instruction that has that variable

                        if (takeTheTemp && seenMatch){
                            errs() << "WE HAVE A MATCH -- REPLACE THE INSTRUCTION\n";
                            // errs() << arg->getType() << "\n\n";
                            if (calleeName == "CAT_new"){
                                errs() << &i << "\n\n";
                            } else if (calleeName == "CAT_get"){
                                errs () << callInst->getArgOperand(0) << " = " << temp << "\n\n";
                            }

                            ConstantInt *newArg = ConstantInt::get(arg->getType(), temp);
                            // BasicBlock::iterator ii(i);
                            // ReplaceInstWithValue(bb.getInstList(), ii, newArg);
                            // replace.push_back(std::tuple<BasicBlock, Instruction*, ConstantInt*>(bb, i, newArg));
                            replace_bb.push_back(&bb);
                            replace_i.push_back(&i);
                            replace_ci.push_back(newArg);
                        }
                    } else if (calleeName == "CAT_sub"){
                        continue; // TODO
                    }
                }
            }

            for (int i=0; i<replace_bb.size(); i++){
                BasicBlock::iterator ii(*(replace_i[i]));
                ReplaceInstWithValue(replace_bb[i]->getInstList(), ii, replace_ci[i]);
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
