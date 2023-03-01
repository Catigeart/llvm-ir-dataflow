//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include <cassert>

#include <llvm/Support/CommandLine.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Support/ToolOutputFile.h>

#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>

#include <llvm/Transforms/Utils.h>
#include <llvm/Transforms/Scalar.h>

#include <llvm/IR/Function.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/IntrinsicInst.h>

#include "Dataflow.h"
#include "utils.h"

using namespace llvm;
static ManagedStatic<LLVMContext> GlobalContext;
static LLVMContext &getGlobalContext() { return *GlobalContext; }

struct EnableFunctionOptPass : public FunctionPass {
    static char ID;
    EnableFunctionOptPass() :FunctionPass(ID) {}
    bool runOnFunction(Function & F) override {
        if (F.hasFnAttribute(Attribute::OptimizeNone))
        {
            F.removeFnAttr(Attribute::OptimizeNone);
        }
        return true;
    }
};

char EnableFunctionOptPass::ID = 0;

///!TODO TO BE COMPLETED BY YOU FOR ASSIGNMENT 3

class PtrInfo {
public:
    Value* alias{};
    std::set<Value *> ptoSet{};

    PtrInfo() = default;
    explicit PtrInfo(Value* alias) : alias(alias), ptoSet({}) {}

    bool operator == (const PtrInfo& ptrInfo) const {
        return alias == ptrInfo.alias && ptoSet == ptrInfo.ptoSet;
    }
};

class FuncPtrInfo {
    std::map<Value*, PtrInfo> infoTable{};

    // 带路径压缩
    Value* getAliasRoot(Value* ptr) {
        assert(infoTable.find(ptr) != infoTable.end());
        if (infoTable.find(ptr) == infoTable.end()) {
            DEBUG_LOG("ptr doesn't exist in infoTable!");
            return nullptr;
        }

        PtrInfo &ptrInfo = infoTable[ptr];
        if (ptr == ptrInfo.alias) {
            return ptr;
        } else {
            ptrInfo.alias = getAliasRoot(ptrInfo.alias);
            return ptrInfo.alias;
        }
    }

    void getAllPtoSet(Value* ptr, std::set<Value *>& s) {
        std::set<Value *> ds = getDirectPtoSet(ptr);
        for (Value* const &v : ds) {
            if (hasPointer(v)) {
                getAllPtoSet(v, s);
            } else {
                s.insert(v);
            }
        }
    }
public:
    bool hasPointer(Value* ptr) {
        return infoTable.find(ptr) != infoTable.end();
    }

    void addPointer(Value* ptr) {
        infoTable[ptr] = PtrInfo(ptr);
    }

    void addPointTo(Value* ptr, Value* val) {
        Value *root = getAliasRoot(ptr);
        infoTable[root].ptoSet.insert(val);
    }

    // 以ptr2的根节点为根
    bool mergeAlias(Value* ptr1, Value* ptr2) {
        Value *root1 = getAliasRoot(ptr1);
        Value *root2 = getAliasRoot(ptr2);
        if (root1 == root2) {
            return false;
        } else {
            auto &root1Set = infoTable[root1].ptoSet;
            infoTable[root2].ptoSet.insert(root1Set.begin(), root1Set.end());
            root1Set = {};
            infoTable[root1].alias = root2;
            return true;
        }
    }

    std::set<Value *> getDirectPtoSet(Value* ptr) {
        Value *root = getAliasRoot(ptr);
        return infoTable[root].ptoSet;
    }

    std::set<Value *> getAllPtoSet(Value* ptr) {
        std::set<Value *> s = {};
        getAllPtoSet(ptr, s);
        return s;
    }

    void clearPtoSet(Value* ptr) {
        Value *root = getAliasRoot(ptr);
        infoTable[root].ptoSet = {};
    }

    void mergeInfo(const FuncPtrInfo &src) {
        // 重新计算并查集以防出错，不差那么点计算量
        // 所以为什么要用并查集（不是

        // 保存旧的并查集关系
        std::map<Value*, Value*> oldAliasMap = {};
        for (auto &p : infoTable) {
            oldAliasMap[p.first] = p.second.alias;
        }
        // 合并指向集
        for (auto &p : src.infoTable) {
            if (infoTable.find(p.first) != infoTable.end()) {
                infoTable[p.first].ptoSet.insert(p.second.ptoSet.begin(), p.second.ptoSet.end());
            } else {
                infoTable[p.first] = p.second;
            }
        }
        // 重置并查集关系
        for (auto &p : infoTable) {
            p.second.alias = p.first;
        }
        // 合并并查集
        for (auto &p : oldAliasMap) {
            mergeAlias(p.first, p.second);
        }
        for (auto &p : src.infoTable) {
            mergeAlias(p.first, p.second.alias);
        }
    }

    void print(raw_ostream &out) {
        for (auto &p : infoTable) {
            out << "\t";
            p.first->printAsOperand(out, false, nullptr);
            out << " : {";
            std::set<Value *> s = getDirectPtoSet(p.first);
            for (auto iter = s.begin(); iter != s.end(); ++iter) {
                if (iter != s.begin()) {
                    out << ", ";
                }
                (*iter)->printAsOperand(out, false, nullptr);
            }
            out << "}\n";
        }
    }

    bool operator == (const FuncPtrInfo & fpInfo) const {
        return infoTable == fpInfo.infoTable;
    }
};

inline raw_ostream& operator << (raw_ostream& out, FuncPtrInfo& fpInfo) {
    out << "Point-to sets:\n";
    fpInfo.print(out);
    return out;
}
/*
class UnsolvedFuncInfo {
public:
    int line{};
    std::set<int> argIdxSet{};
};
*/
class FuncPtrVisitor : public DataflowVisitor<struct FuncPtrInfo> {
public:
    FuncPtrVisitor() = default;

    // 在Visitor记录整个模块（文件）的函数调用结果
    std::map<unsigned, std::set<StringRef>> fpResult;

    void merge(FuncPtrInfo *dst, const FuncPtrInfo &src) override {
        dst->mergeInfo(src);
    }

    void compDFVal(Instruction *inst, FuncPtrInfo *dfVal) override {
        if (isa<DbgInfoIntrinsic>(inst)) return;

        /*if (auto *allocaInst = dyn_cast<AllocaInst>(inst)) {
            // handleAllocaInst(allocaInst, dfVal);
            DEBUG_LOG("Unhandled: " << *inst);
        } else*/ if (auto *storeInst = dyn_cast<StoreInst>(inst)) {
            handleStoreInst(storeInst, dfVal);
        } else if (auto *loadInst = dyn_cast<LoadInst>(inst)) {
            handleLoadInst(loadInst, dfVal);
        } else if (auto *getElementPtrInst = dyn_cast<GetElementPtrInst>(inst)) {
            handleGetElementPtrInst(getElementPtrInst, dfVal);
        } else if (isa<MemSetInst>(inst)) {
            DEBUG_LOG("Memset: " << *inst);
        } else if (isa<MemCpyInst>(inst)) {
            DEBUG_LOG("MemCpy: " << *inst);
        } else if (auto *returnInst = dyn_cast<ReturnInst>(inst)) {
            handleReturnInst(returnInst, dfVal);
        } else if (auto *callInst = dyn_cast<CallInst>(inst)) {
            handleCallInst(callInst, dfVal);
        } else {
            DEBUG_LOG("Unhandled:" << *inst);
        }
    }
/*
    static void handleAllocaInst(AllocaInst* pInst, FuncPtrInfo *fpInfo) {
        //pInst->getAllocatedType()->isPointerTy()
    }
*/
    /// *x = y
    static void handleStoreInst(StoreInst *pInst, FuncPtrInfo *fpInfo) {
        Value *val = pInst->getValueOperand();
        Value *ptr = pInst->getPointerOperand();

        if (isa<ConstantData>(val)) {
            DEBUG_LOG("Skipped store const data:  " << *val);
            return;
        }

        DEBUG_LOG("Store:" << *pInst);

        if (!fpInfo->hasPointer(ptr)) {
            fpInfo->addPointer(ptr);
        }

        fpInfo->clearPtoSet(ptr); // 基本块内流敏感

        // alloca 特判，将alloca和传入的值绑定
        bool valIsArg = false;
        Function *func = pInst->getFunction();
        for (unsigned i = 0; i < func->arg_size(); ++i) {
            if (val->getValueID() == func->getArg(i)->getValueID())
                valIsArg = true;
        }
        if (isa<AllocaInst>(ptr) && valIsArg) {
            DEBUG_LOG("Alloca judge!");
            if (!fpInfo->hasPointer(val)) {
                fpInfo->addPointer(val);
            }
            fpInfo->mergeAlias(val, ptr);
            return;
        }

        if (!fpInfo->hasPointer(val)) {
            fpInfo->addPointTo(ptr, val);
        } else {
            // fpInfo->mergeAlias(ptr, val);
            for (auto &v : fpInfo->getDirectPtoSet(val)) {
                fpInfo->addPointTo(ptr, v);
            }
        }
    }

    static void handleLoadInst(LoadInst *pInst, FuncPtrInfo *fpInfo) {
        Value *ptr = pInst->getPointerOperand();
        auto *val = dyn_cast<Value>(pInst);

        // 一级指针总是指向常数
        if (!ptr->getType()->getContainedType(0)->isPointerTy()) {
            DEBUG_LOG("Skipped load const data:" << *val);
            return;
        }

        DEBUG_LOG("Load:" << *pInst);

        if (!fpInfo->hasPointer(ptr)) {
            DEBUG_LOG("Load from null ptr:" << *ptr);
        } else {
            if (!fpInfo->hasPointer(val)) {
                fpInfo->addPointer(val);
            }
            fpInfo->clearPtoSet(val); // 基本块内流敏感
            fpInfo->mergeAlias(val, ptr);
           // for (auto &v : fpInfo->getDirectPtoSet(ptr)) {
             //   fpInfo->addPointTo(val, v);
           // }
        }
    }

    // 结构体会变量重命名，因此直接绑定别名
    static void handleGetElementPtrInst(GetElementPtrInst *pInst, FuncPtrInfo *fpInfo) {
        DEBUG_LOG("GetElementPtr:" << *pInst);

        Value *ptr = pInst->getPointerOperand();
        auto *val = dyn_cast<Value>(pInst);

        if (!fpInfo->hasPointer(ptr)) {
            fpInfo->addPointer(ptr);
        }
        if (!fpInfo->hasPointer(val)) {
            fpInfo->addPointer(val);
        }
        fpInfo->mergeAlias(ptr, val);
    }
/*
    static void handleMemCpyInst(MemCpyInst *pInst, FuncPtrInfo *fpInfo) {
        DEBUG_LOG("MemCpy:" << *pInst);
    }
*/
    static void handleReturnInst(ReturnInst *pInst, FuncPtrInfo *fpInfo) {
        DEBUG_LOG("Return:" << *pInst);
        Value *retVal = pInst->getReturnValue();
        Function *currentFunc = pInst->getFunction();

        fpInfo->addPointer(currentFunc);
        if (fpInfo->hasPointer(retVal)) {
            fpInfo->mergeAlias(currentFunc, retVal);
        }

        /*
        std::set<Value *> retValPtoSet = fpInfo->getAllPtoSet(retVal);

        // 返回值与参数绑定
        for (int i = 0; i < currentFunc->arg_size(); ++i) {
            for (auto &ptr : retValPtoSet) {
                if (ptr == currentFunc->getArg(i)) {
                    UnsolvedReturnTable[currentFunc].insert(i);
                }
            }
        }
        */
    }

    // 一个假设：调用的函数要么硬编码在代码中，要么指向传入的参数
    // 因此只需要考虑指向本身为函数，或指向形参
    void handleCallInst(CallInst *pInst, FuncPtrInfo *fpInfo) {
        DEBUG_LOG("Call:" << *pInst);

        // Function *currentFunc = pInst->getFunction();
        unsigned line = pInst->getDebugLoc().getLine();
        Value *calledOp = pInst->getCalledOperand();

        if (isa<Function>(calledOp) && calledOp->getName() == "malloc") {
            fpResult[line].insert("malloc");
            return;
        }

        std::set<Function *> funcSet = {};
        if (auto* opFunc = dyn_cast<Function>(calledOp)) {
            funcSet.insert(opFunc);
        } else if (auto loadOp = dyn_cast<LoadInst>(calledOp)) {
            Value *loadPtr = loadOp->getPointerOperand();

            // fpInfo->addPointer(pInst);
            // fpInfo->mergeAlias(pInst, loadPtr);
            if (fpInfo->hasPointer(loadPtr)) {
                std::set<Value *> allPtoSet = fpInfo->getAllPtoSet(loadPtr);
                for (auto& val : allPtoSet) {
                    if (auto *loadFunc = dyn_cast<Function>(val)) {
                        funcSet.insert(loadFunc);
                    } else {
                        // 应该没用，先留个坑摆在这里
                    }
                }
            }
        } else {
            DEBUG_LOG("Unhandled calledOperand type: " << calledOp);
        }

        for (Function* const &func : funcSet) {
            fpResult[line].insert(func->getName());

            FuncPtrVisitor visitor;
            DataflowResult<FuncPtrInfo>::Type result;
            FuncPtrInfo initVal;

            // 绑定指针参数别名
            for (unsigned i = 0; i < pInst->getNumOperands() - 1; ++i) {
                Value *callerArg = pInst->getArgOperand(i);
                if (callerArg->getType()->isPointerTy()) {
                    Value *calleeParam = func->getArg(i);
                    // initVal.addPointer(callerArg);
                    initVal.addPointer(calleeParam);
                    // initVal.mergeAlias(calleeParam, callerArg);
                    // 因为作用域的问题，如果直接绑定别名，会导致函数执行结束后，指针仍然指向内部的变量
                    if (fpInfo->hasPointer(callerArg)) {
                        std::set<Value *> allSet = fpInfo->getAllPtoSet(callerArg);
                        for (auto &v : allSet) {
                            initVal.addPointTo(calleeParam, v);
                        }
                    }
                }
            }

            DEBUG_LOG("--------------------CALLED FUNCTION BEGIN--------------------");
            compForwardDataflow(func, &visitor, &result, initVal);
            DEBUG_LOG("---------------------CALLED FUNCTION END---------------------");

            // 保存递归函数中的调用信息
            for (auto &p : visitor.fpResult) {
                for (auto &str : p.second) {
                    fpResult[p.first].insert(str);
                }
            }

            FuncPtrInfo exitPtrInfo = result[&(func->back())].second;
            // 参数指向的处理
            for (unsigned i = 0; i < pInst->getNumOperands() - 1; ++i) {
                Value *callerArg = pInst->getArgOperand(i);
                if (callerArg->getType()->isPointerTy()) {
                    Value *calleeParam = func->getArg(i);
                    // 如果参数有指向的变化，需要同步修改
                    if (exitPtrInfo.hasPointer(calleeParam)) {
                        if (!fpInfo->hasPointer(callerArg)) {
                            fpInfo->addPointer(callerArg);
                        }
                        std::set<Value*> calleePtoSet = exitPtrInfo.getAllPtoSet(calleeParam);
                        fpInfo->clearPtoSet(callerArg); // 基本块内流敏感
                        for (auto &v : calleePtoSet) {
                            // 只有指向函数的指针和指向其他入参的指针允许加入指向集
                            if (isa<Function>(v)) {
                                fpInfo->addPointTo(callerArg, v);
                                continue;
                            }
                            for (unsigned ii = 0; ii < pInst->getNumOperands() - 1; ++ii) {
                                if (v == func->getArg(ii)) {
                                    fpInfo->addPointTo(callerArg, v);
                                    break;
                                }
                            }
                        }
                    }
                }
            }

            // 解析返回值
            // 如果是空的，说明不是指针变量，不用分析
            if (!exitPtrInfo.getAllPtoSet(func).empty()) {
                if (!fpInfo->hasPointer(pInst)) {
                    fpInfo->addPointer(pInst);
                }
                for (auto &v : exitPtrInfo.getAllPtoSet(func)) {
                    fpInfo->addPointTo(pInst, v);
                }
            }
        }
/*
        // std::set<Function *> funcs;
        if (auto func = dyn_cast<Function>(funcVal)) {
            // 当发现了一个真实调用的函数
            ptResult[line].insert(func->getName()); // 记录当前的调用

            for (auto &p : funcCallToLineAndArgNo[func]) {
                const auto &arg = pInst->getArgOperand(p.second);
                // arg->dump();


                // const auto ptSet = ptInfo->getDirectPtSet(arg);
                std::set<Value *> ptSet = {};
                ptInfo->getAllPtSet(arg, ptSet);
                for (auto &argPtVal : ptSet) {
                    if (auto argFunc = dyn_cast<Function>(argPtVal)) {
                        ptResult[p.first].insert(argFunc->getName());
                    }
                }
            }
            // funcs.insert(func);
        } else if (auto *loadInst = dyn_cast<LoadInst>(funcVal)) {
            // call 节点指向的内容实际上是load出来的内容
            Value *ptr = loadInst->getPointerOperand();

            ptInfo->addAlias(pInst, pInst);
            auto ptrPtSet = ptInfo->getDirectPtSet(ptr);
            for (auto &v : ptrPtSet) {
                ptInfo->addPointTo(pInst, v); // callInst 指向 loadInst 的内容
            }
            // ptInfo->ptSets[pInst] = ptInfo->ptSets[ptr];


            std::set<Value *> callAllSet = {};
            ptInfo->getAllPtSet(pInst, callAllSet);
            for (auto& val : callAllSet) {
                if (auto *loadFunc = dyn_cast<Function>(val)) {
                    // 当发现了一个真实调用的函数
                    ptResult[line].insert(loadFunc->getName()); // 记录当前的调用

                    for (auto &p : funcCallToLineAndArgNo[loadFunc]) {
                        const auto &arg = pInst->getArgOperand(p.second);
                        // arg->dump();


                        // const auto ptSet = ptInfo->getDirectPtSet(arg);
                        std::set<Value *> ptSet = {};
                        ptInfo->getAllPtSet(arg, ptSet);
                        for (auto &argPtVal : ptSet) {
                            if (auto argFunc = dyn_cast<Function>(argPtVal)) {
                                ptResult[p.first].insert(argFunc->getName());
                            }
                        }
                    }

                    // 处理参数里面调用函数的情况，先摸鱼

                    for (auto &p : funcCallToLineAndArgNo[loadFunc]) {
                        const auto &arg = pInst->getArgOperand(p.second);

                    }


                } else {
                    for (int i = 0; i < fatherFunc->arg_size(); ++i) {
                        // 暂存调用位置，待实参进来后再更新结果
                        if (val == fatherFunc->getArg(i)) {
                            funcCallToLineAndArgNo[fatherFunc][line] = i;
                        }
                    }
                }
            }
        } else {
            DEBUG_LOG("Unhandled inFunc:" << *funcVal);
        }

        for (Function *func : funcs) {
            ptResult[line].insert(func->getName());

            if (!funcRetToArgNo[func].empty()) {
                // 如果正确答案要求这里返回其实际对应返回值调用的真正函数，需要在这里补全
            }

            // 函数嵌套调用应该不会捕捉到，但不如先摸鱼吧，笑死
        }
       */
    }

    void printFuncPtrResult(raw_ostream &out) {
        for (auto &result : fpResult) {
            out << result.first << " : ";
            for (auto it = result.second.begin(); it != result.second.end(); ++it) {
                out << *it;
                it++;
                if (it != result.second.end()) {
                    out << ", ";
                }
                it--;
            }
            out << "\n";
        }
    }
};

inline raw_ostream &operator<<(raw_ostream &out, const std::map<Function*, std::set<int>>& funcRetToArgNo) {
    for (const auto& p : funcRetToArgNo) {
        out << "\t" << p.first->getName() << " : ";
        for (const auto& n : p.second) {
            out << n << " ";
        }
        out << "\n";
    }
    return out;
}

struct FuncPtrPass : public ModulePass {
    static char ID; // Pass identification, replacement for typeid
    FuncPtrPass() : ModulePass(ID) {}

    bool runOnModule(Module &M) override {
        FuncPtrVisitor visitor;
        DataflowResult<FuncPtrInfo>::Type result;
        FuncPtrInfo initVal;

        auto f = M.rbegin();
        // 跳过llvm.函数和没有函数体的函数，后者感觉应该是隐式声明，如malloc
        for (; (f->isIntrinsic() || f->empty()) && f != M.rend(); f++) {}
        DEBUG_LOG("Entry function: " << f->getName());
        compForwardDataflow(&*f, &visitor, &result, initVal);
        /*
        for (auto & f : M) { // Function Iteration
            if (f.isIntrinsic() || f.empty())
                continue;
            DEBUG_LOG("Entry function: " << f.getName());
            compForwardDataflow(&f, &visitor, &result, initVal);
            // DEBUG_LOG("Function return - parameter position map:\n" << visitor.funcRetToArgNo);
            errs() << "-----------------------------\n";
        }
        */
        visitor.printFuncPtrResult(errs());

/*
        errs() << "Hello: ";
        errs().write_escaped(M.getName()) << '\n';
        M.dump();
        errs() << "------------------------------\n";
*/
        return false;
    }

};


char FuncPtrPass::ID = 0;
static RegisterPass<FuncPtrPass> X("funcptrpass", "Print function call instruction");
/*
char Liveness::ID = 0;
static RegisterPass<Liveness> Y("liveness", "Liveness Dataflow Analysis");
*/
static cl::opt<std::string>
InputFilename(cl::Positional,
              cl::desc("<filename>.bc"),
              cl::init(""));


int main(int argc, char **argv) {
   LLVMContext &Context = getGlobalContext();
   SMDiagnostic Err;
   // Parse the command line to read the Inputfilename
   cl::ParseCommandLineOptions(argc, argv,
                              "FuncPtrPass \n My first LLVM too which does not do much.\n");


   // Load the input module
   std::unique_ptr<Module> M = parseIRFile(InputFilename, Err, Context);
   if (!M) {
      Err.print(argv[0], errs());
      return 1;
   }

   llvm::legacy::PassManager Passes;
#if LLVM_VERSION_MAJOR == 5
   Passes.add(new EnableFunctionOptPass());
#endif
   ///Transform it to SSA
   Passes.add(llvm::createPromoteMemoryToRegisterPass());

   /// Your pass to print Function and Call Instructions
   //Passes.add(new Liveness());
   Passes.add(new FuncPtrPass());
   Passes.run(*M.get());
#ifndef NDEBUG
   // system("pause");
#endif
}

