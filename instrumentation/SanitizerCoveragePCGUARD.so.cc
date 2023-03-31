//===-- SanitizerCoverage.cpp - coverage instrumentation for sanitizers ---===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Coverage instrumentation done on LLVM IR level, works with Sanitizers.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Instrumentation/SanitizerCoverage.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Triple.h"
#include "llvm/Analysis/EHPersonalities.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Mangler.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Type.h"
#include "llvm/InitializePasses.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/SpecialCaseList.h"
#include "llvm/Support/VirtualFileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/IR/PassManager.h"

#include "config.h"
#include "debug.h"
#include "afl-llvm-common.h"

extern "C" {

#include "patalog.h"

}

using namespace llvm;

#define DEBUG_TYPE "sancov"

const char SanCovTracePCIndirName[] = "__sanitizer_cov_trace_pc_indir";
const char SanCovTracePCName[] = "__sanitizer_cov_trace_pc";
const char SanCovTraceCmp1[] = "__sanitizer_cov_trace_cmp1";
const char SanCovTraceCmp2[] = "__sanitizer_cov_trace_cmp2";
const char SanCovTraceCmp4[] = "__sanitizer_cov_trace_cmp4";
const char SanCovTraceCmp8[] = "__sanitizer_cov_trace_cmp8";
const char SanCovTraceConstCmp1[] = "__sanitizer_cov_trace_const_cmp1";
const char SanCovTraceConstCmp2[] = "__sanitizer_cov_trace_const_cmp2";
const char SanCovTraceConstCmp4[] = "__sanitizer_cov_trace_const_cmp4";
const char SanCovTraceConstCmp8[] = "__sanitizer_cov_trace_const_cmp8";
const char SanCovTraceDiv4[] = "__sanitizer_cov_trace_div4";
const char SanCovTraceDiv8[] = "__sanitizer_cov_trace_div8";
const char SanCovTraceGep[] = "__sanitizer_cov_trace_gep";
const char SanCovTraceSwitchName[] = "__sanitizer_cov_trace_switch";
const char SanCovModuleCtorTracePcGuardName[] =
    "sancov.module_ctor_trace_pc_guard";
const char SanCovModuleCtor8bitCountersName[] =
    "sancov.module_ctor_8bit_counters";
const char SanCovModuleCtorBoolFlagName[] = "sancov.module_ctor_bool_flag";
/* PATA begin */
const char SanCovModuleCtorPataGuardName[] = 
    "sancov.module_ctor_pata_guard";
const char SanCovModuleCtorPataMetadataPtrName[] = 
    "sancov.module_ctor_pata_metadata_ptr";
const char SanCovModuleCtorPataMetadataName[] = 
    "sancov.module_ctor_pata_metadata";
/* PATA end */
static const uint64_t SanCtorAndDtorPriority = 2;

const char SanCovTracePCGuardName[] = "__sanitizer_cov_trace_pc_guard";
const char SanCovTracePCGuardInitName[] = "__sanitizer_cov_trace_pc_guard_init";
const char SanCov8bitCountersInitName[] = "__sanitizer_cov_8bit_counters_init";
const char SanCovBoolFlagInitName[] = "__sanitizer_cov_bool_flag_init";
const char SanCovPCsInitName[] = "__sanitizer_cov_pcs_init";
/* PATA begin */
const char SanCovPataGuardInitName[] = "__sanitizer_pata_guard_init";
const char SanCovPataMetadataInitName[] = "__sanitizer_pata_metadata_init";
const char SanCovPataMetadataPtrInitName[] = "__sanitizer_pata_metadata_ptr_init";
/* PATA end */

const char SanCovGuardsSectionName[] = "sancov_guards";
const char SanCovCountersSectionName[] = "sancov_cntrs";
const char SanCovBoolFlagSectionName[] = "sancov_bools";
const char SanCovPCsSectionName[] = "sancov_pcs";
/* PATA begin */
const char SanCovPataGuardSectionName[] = "sancov_pata_guard";
const char SanCovPataMetadataSectionName[] = "sancov_pata_metadata";
const char SanCovPataMetadataPtrSectionName[] = "sancov_pata_metadata_ptr";
/* PATA end */

const char SanCovLowestStackName[] = "__sancov_lowest_stack";

static const char *skip_nozero;
static const char *use_threadsafe_counters;

namespace {

SanitizerCoverageOptions OverrideFromCL(SanitizerCoverageOptions Options) {

  // Sets CoverageType and IndirectCalls.
  // SanitizerCoverageOptions CLOpts = getOptions(ClCoverageLevel);
  Options.CoverageType =
      SanitizerCoverageOptions::SCK_Edge;  // std::max(Options.CoverageType,
                                           // CLOpts.CoverageType);
  Options.IndirectCalls = false;           // CLOpts.IndirectCalls;
  Options.TraceCmp = false;                //|= ClCMPTracing;
  Options.TraceDiv = false;                //|= ClDIVTracing;
  Options.TraceGep = false;                //|= ClGEPTracing;
  Options.TracePC = false;                 //|= ClTracePC;
  Options.TracePCGuard = true;             // |= ClTracePCGuard;
  Options.Inline8bitCounters = 0;          //|= ClInline8bitCounters;
  // Options.InlineBoolFlag = 0; //|= ClInlineBoolFlag;
  Options.PCTable = false;     //|= ClCreatePCTable;
  Options.NoPrune = false;     //|= !ClPruneBlocks;
  Options.StackDepth = false;  //|= ClStackDepth;
  if (!Options.TracePCGuard && !Options.TracePC &&
      !Options.Inline8bitCounters && !Options.StackDepth /*&&
      !Options.InlineBoolFlag*/)
    Options.TracePCGuard = true;  // TracePCGuard is default.

  return Options;

}

using DomTreeCallback = function_ref<const DominatorTree *(Function &F)>;
using PostDomTreeCallback =
    function_ref<const PostDominatorTree *(Function &F)>;

class ModuleSanitizerCoverageAFL
    : public PassInfoMixin<ModuleSanitizerCoverageAFL> {

 public:
  ModuleSanitizerCoverageAFL(
      const SanitizerCoverageOptions &Options = SanitizerCoverageOptions())
      : Options(OverrideFromCL(Options)) {

  }

  PreservedAnalyses run(Module &M, ModuleAnalysisManager &MAM);

  bool instrumentModule(Module &M, DomTreeCallback DTCallback,
                        PostDomTreeCallback PDTCallback);

 private:
  void instrumentFunction(Function &F, DomTreeCallback DTCallback,
                          PostDomTreeCallback PDTCallback);
  void InjectCoverageForIndirectCalls(Function               &F,
                                      ArrayRef<Instruction *> IndirCalls);
  void InjectTraceForCmp(Function &F, ArrayRef<Instruction *> CmpTraceTargets);
  void InjectTraceForDiv(Function                  &F,
                         ArrayRef<BinaryOperator *> DivTraceTargets);
  void InjectTraceForGep(Function                     &F,
                         ArrayRef<GetElementPtrInst *> GepTraceTargets);
  void InjectTraceForSwitch(Function               &F,
                            ArrayRef<Instruction *> SwitchTraceTargets);
  bool InjectCoverage(Function &F, ArrayRef<BasicBlock *> AllBlocks,
                      bool IsLeafFunc = true);
  GlobalVariable *CreateFunctionLocalArrayInSection(size_t    NumElements,
                                                    Function &F, Type *Ty,
                                                    const char *Section);
  GlobalVariable *CreatePCArray(Function &F, ArrayRef<BasicBlock *> AllBlocks);
  void CreateFunctionLocalArrays(Function &F, ArrayRef<BasicBlock *> AllBlocks,
                                 uint32_t special);
  void InjectCoverageAtBlock(Function &F, BasicBlock &BB, size_t Idx,
                             bool IsLeafFunc = true);
  Function *CreateInitCallsForSections(Module &M, const char *CtorName,
                                       const char *InitFunctionName, Type *Ty,
                                       const char *Section);
  std::pair<Value *, Value *> CreateSecStartEnd(Module &M, const char *Section,
                                                Type *Ty);

  void SetNoSanitizeMetadata(Instruction *I) {

    I->setMetadata(I->getModule()->getMDKindID("nosanitize"),
                   MDNode::get(*C, None));

  }

  std::string     getSectionName(const std::string &Section) const;
  std::string     getSectionStart(const std::string &Section) const;
  std::string     getSectionEnd(const std::string &Section) const;
  FunctionCallee  SanCovTracePCIndir;
  FunctionCallee  SanCovTracePC, SanCovTracePCGuard;
  FunctionCallee  SanCovTraceCmpFunction[4];
  FunctionCallee  SanCovTraceConstCmpFunction[4];
  FunctionCallee  SanCovTraceDivFunction[2];
  FunctionCallee  SanCovTraceGepFunction;
  FunctionCallee  SanCovTraceSwitchFunction;
  GlobalVariable *SanCovLowestStack;
  Type *IntptrTy, *IntptrPtrTy, *Int64Ty, *Int64PtrTy, *Int32Ty, *Int32PtrTy,
      *Int16Ty, *Int8Ty, *Int8PtrTy, *Int1Ty, *Int1PtrTy;
  Module           *CurModule;
  std::string       CurModuleUniqueId;
  Triple            TargetTriple;
  LLVMContext      *C;
  const DataLayout *DL;

  GlobalVariable *FunctionGuardArray;        // for trace-pc-guard.
  GlobalVariable *Function8bitCounterArray;  // for inline-8bit-counters.
  GlobalVariable *FunctionBoolArray;         // for inline-bool-flag.
  GlobalVariable *FunctionPCsArray;          // for pc-table.
  SmallVector<GlobalValue *, 20> GlobalsToAppendToUsed;
  SmallVector<GlobalValue *, 20> GlobalsToAppendToCompilerUsed;

  SanitizerCoverageOptions Options;

  uint32_t        instr = 0, selects = 0, unhandled = 0;
  GlobalVariable *AFLMapPtr = NULL;
  ConstantInt    *One = NULL;
  ConstantInt    *Zero = NULL;

  /* PATA begin */
  uint8_t patalog_mode = 0;
  uint32_t pata_global_id = 0;
  DenseMap<Value*, uint32_t> value_to_type;
  DenseMap<BasicBlock*, Constant*> block_to_id;
  GlobalVariable *ModulePataMetadata, *ModulePataMetadataPtr;
  GlobalVariable *PataTmpGuardArray;

  StructType *PataMetadataTy;
  PointerType *PataMetadataPtrTy;
  Type *VoidTy;
  IntegerType *Int128Ty;
  PointerType *voidPtrTy;
  PointerType *Int32PtrPtrTy, *Int32PtrPtrPtrTy;
  Constant *Null;

  GlobalVariable *CreateModuleDataInSection(Function &F, Type *Ty,
                                            const char *Section);
  void initializePataGlobals(Module &M);
  bool hookCmps(Module &M);
  bool hookSwitches(Module &M);
  bool hookRtns(Module &M);
  Constant *collectBlockFeatures(Module &M, Instruction &I, u32 cur_id,
                                 const char *ptr_name_prefix,
                                 const char *name_prefix,
                                 u32 &num_succ, Constant *&bf);
  void InjectCoverageForPata(Function &F, BasicBlock &BB);
  /* PATA end */
};

}  // namespace

#if LLVM_VERSION_MAJOR >= 11                        /* use new pass manager */

extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {

  return {LLVM_PLUGIN_API_VERSION, "SanitizerCoveragePCGUARD", "v0.1",
          /* lambda to insert our pass into the pass pipeline. */
          [](PassBuilder &PB) {

  #if LLVM_VERSION_MAJOR <= 13
            using OptimizationLevel = typename PassBuilder::OptimizationLevel;
  #endif
            PB.registerOptimizerLastEPCallback(
                [](ModulePassManager &MPM, OptimizationLevel OL) {

                  MPM.addPass(ModuleSanitizerCoverageAFL());

                });

          }};

}

#endif

/* PATA begin */
template <class Iterator>
Iterator Unique(Iterator first, Iterator last) {

  while (first != last) {

    Iterator next(first);
    last = std::remove(++next, last, *first);
    first = next;

  }

  return last;

}

Constant* ModuleSanitizerCoverageAFL::
collectBlockFeatures(Module &M, Instruction &I, u32 cur_id,
                     const char *ptr_name_prefix, const char *name_prefix,
                     u32 &num_succ, Constant *&bf) {
  uint32_t num_successors = 0;
  std::vector<Constant*> successor_ids;
  for (auto PB : successors(I.getParent())) {
    if (block_to_id.find(PB) == block_to_id.end()) {
      // the successor is not instrumented, so let's instrument it first
      InjectCoverageForPata(*PB->getParent(), *PB);
    }
    num_successors += 1;
    successor_ids.push_back(block_to_id[PB]);
  }
  num_succ = num_successors;
  // different from LTO, we hold pointers to block ids here
  if (num_successors) {
    // Ptr array
    auto global_name = ptr_name_prefix + std::to_string(cur_id);
    auto tmp_ty = ArrayType::get(Int32PtrTy, num_successors);
    M.getOrInsertGlobal(global_name, tmp_ty);
    auto bf_ptr = M.getNamedGlobal(global_name);
    // avoid name collisions
    bf_ptr->setLinkage(llvm::GlobalValue::InternalLinkage);
    bf_ptr->setInitializer(ConstantArray::get(tmp_ty, successor_ids));

    // real array
    global_name = name_prefix + std::to_string(cur_id);
    tmp_ty = ArrayType::get(Int32Ty, num_successors);
    M.getOrInsertGlobal(global_name, tmp_ty);
    auto bf_tmp = M.getNamedGlobal(global_name);
    // avoid name collisions
    bf_tmp->setLinkage(llvm::GlobalValue::InternalLinkage);
    std::vector<Constant*> tmp(num_successors, ConstantInt::get(Int32Ty, 0));
    bf_tmp->setInitializer(ConstantArray::get(tmp_ty, tmp));
    bf = bf_tmp;

    return bf_ptr;
  } else {
    bf = ConstantPointerNull::get((PointerType*)Int32PtrTy);
    return ConstantPointerNull::get((PointerType*)Int32PtrPtrTy);
  }
}

bool ModuleSanitizerCoverageAFL::hookCmps(Module &M) {

  std::vector<Instruction *> icomps;

#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee
#else
  Constant *
#endif
      c1 = M.getOrInsertFunction("__patalog_ins_hook1", VoidTy, Int8Ty, Int8Ty,
                                 Int32Ty
#if LLVM_VERSION_MAJOR < 5
                                 ,
                                 NULL
#endif
      );
#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee patalogHookIns1 = c1;
#else
  Function *patalogHookIns1 = cast<Function>(c1);
#endif

#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee
#else
  Constant *
#endif
      c2 = M.getOrInsertFunction("__patalog_ins_hook2", VoidTy, Int16Ty, Int16Ty,
                                 Int32Ty
#if LLVM_VERSION_MAJOR < 5
                                 ,
                                 NULL
#endif
      );
#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee patalogHookIns2 = c2;
#else
  Function *patalogHookIns2 = cast<Function>(c2);
#endif

#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee
#else
  Constant *
#endif
      c4 = M.getOrInsertFunction("__patalog_ins_hook4", VoidTy, Int32Ty, Int32Ty,
                                 Int32Ty
#if LLVM_VERSION_MAJOR < 5
                                 ,
                                 NULL
#endif
      );
#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee patalogHookIns4 = c4;
#else
  Function *patalogHookIns4 = cast<Function>(c4);
#endif

#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee
#else
  Constant *
#endif
      c8 = M.getOrInsertFunction("__patalog_ins_hook8", VoidTy, Int64Ty, Int64Ty,
                                 Int32Ty
#if LLVM_VERSION_MAJOR < 5
                                 ,
                                 NULL
#endif
      );
#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee patalogHookIns8 = c8;
#else
  Function *patalogHookIns8 = cast<Function>(c8);
#endif

#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee
#else
  Constant *
#endif
      c16 = M.getOrInsertFunction("__patalog_ins_hook16", VoidTy, Int128Ty,
                                  Int128Ty, Int32Ty
#if LLVM_VERSION_MAJOR < 5
                                  ,
                                  NULL
#endif
      );
#if LLVM_VERSION_MAJOR < 9
  Function *patalogHookIns16 = cast<Function>(c16);
#else
  FunctionCallee patalogHookIns16 = c16;
#endif

#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee
#else
  Constant *
#endif
      cN = M.getOrInsertFunction("__patalog_ins_hookN", VoidTy, Int128Ty,
                                 Int128Ty, Int32Ty
#if LLVM_VERSION_MAJOR < 5
                                 ,
                                 NULL
#endif
      );
#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee patalogHookInsN = cN;
#else
  Function *patalogHookInsN = cast<Function>(cN);
#endif

  /* iterate over all functions, bbs and instruction and add suitable calls */
  for (auto &F : M) {

    if (!isInInstrumentList(&F, MNAME)) continue;

    for (auto &BB : F) {

      for (auto &IN : BB) {

        CmpInst *selectcmpInst = nullptr;
        if ((selectcmpInst = dyn_cast<CmpInst>(&IN))) {

          icomps.push_back(selectcmpInst);

        }

      }

    }

  }

  if (icomps.size()) {

    // if (!be_quiet) errs() << "Hooking " << icomps.size() <<
    //                          " cmp instructions\n";

    for (auto &selectcmpInst : icomps) {

      IRBuilder<> IRB(selectcmpInst);

      Value *op0 = selectcmpInst->getOperand(0);
      Value *op1 = selectcmpInst->getOperand(1);
      Value *op0_saved = op0, *op1_saved = op1;
      auto   ty0 = op0->getType();
      auto   ty1 = op1->getType();

      IntegerType *intTyOp0 = NULL;
      IntegerType *intTyOp1 = NULL;
      unsigned     max_size = 0, cast_size = 0;
      unsigned     vector_cnt = 0, is_fp = 0;
      CmpInst     *cmpInst = dyn_cast<CmpInst>(selectcmpInst);

      if (!cmpInst) { continue; }

      if (selectcmpInst->getOpcode() == Instruction::FCmp) {

        if (ty0->isVectorTy()) {

          VectorType *tt = dyn_cast<VectorType>(ty0);
          if (!tt) {

            fprintf(stderr, "Warning: patalog cmp vector is not a vector!\n");
            continue;

          }

#if (LLVM_VERSION_MAJOR >= 12)
          vector_cnt = tt->getElementCount().getKnownMinValue();
          ty0 = tt->getElementType();
#endif

        }

        if (ty0->isHalfTy()
#if LLVM_VERSION_MAJOR >= 11
            || ty0->isBFloatTy()
#endif
        )
          max_size = 16;
        else if (ty0->isFloatTy())
          max_size = 32;
        else if (ty0->isDoubleTy())
          max_size = 64;
        else if (ty0->isX86_FP80Ty())
          max_size = 80;
        else if (ty0->isFP128Ty() || ty0->isPPC_FP128Ty())
          max_size = 128;
#if (LLVM_VERSION_MAJOR >= 12)
        else if (ty0->getTypeID() != llvm::Type::PointerTyID && !be_quiet)
          fprintf(stderr, "Warning: unsupported cmp type for patalog: %u!\n",
                  ty0->getTypeID());
#endif

        is_fp = 1;
        // fprintf(stderr, "HAVE FP %u!\n", vector_cnt);

      } else {

        if (ty0->isVectorTy()) {

#if (LLVM_VERSION_MAJOR >= 12)
          VectorType *tt = dyn_cast<VectorType>(ty0);
          if (!tt) {

            fprintf(stderr, "Warning: patalog cmp vector is not a vector!\n");
            continue;

          }

          vector_cnt = tt->getElementCount().getKnownMinValue();
          ty1 = ty0 = tt->getElementType();
#endif

        }

        intTyOp0 = dyn_cast<IntegerType>(ty0);
        intTyOp1 = dyn_cast<IntegerType>(ty1);

        if (intTyOp0 && intTyOp1) {

          max_size = intTyOp0->getBitWidth() > intTyOp1->getBitWidth()
                         ? intTyOp0->getBitWidth()
                         : intTyOp1->getBitWidth();

        } else {

#if (LLVM_VERSION_MAJOR >= 12)
          if (ty0->getTypeID() != llvm::Type::PointerTyID && !be_quiet) {

            fprintf(stderr, "Warning: unsupported cmp type for patalog: %u\n",
                    ty0->getTypeID());

          }

#endif

        }

      }

      if (!max_size || max_size < 16) {

        // fprintf(stderr, "too small\n");
        continue;

      }

      if (max_size % 8) { max_size = (((max_size / 8) + 1) * 8); }

      if (max_size > 128) {

        if (!be_quiet) {

          fprintf(stderr,
                  "Cannot handle this compare bit size: %u (truncating)\n",
                  max_size);

        }

        max_size = 128;

      }

      // do we need to cast?
      switch (max_size) {

        case 8:
        case 16:
        case 32:
        case 64:
        case 128:
          cast_size = max_size;
          break;
        default:
          cast_size = 128;

      }

      // XXX FIXME BUG TODO
      if (is_fp && vector_cnt) { continue; }

      uint64_t cur = 0, last_val0 = 0, last_val1 = 0, cur_val;

      while (1) {

        std::vector<Value *> args;
        bool                 skip = false;
        uint8_t misc = 0;
        uint8_t predicate = cmpInst->getPredicate();

        if (vector_cnt) {

          op0 = IRB.CreateExtractElement(op0_saved, cur);
          op1 = IRB.CreateExtractElement(op1_saved, cur);
          /*
          std::string errMsg;
          raw_string_ostream os(errMsg);
          op0_saved->print(os);
          fprintf(stderr, "X: %s\n", os.str().c_str());
          */
          if (is_fp) {

            /*
                        ConstantFP *i0 = dyn_cast<ConstantFP>(op0);
                        ConstantFP *i1 = dyn_cast<ConstantFP>(op1);
                        // BUG FIXME TODO: this is null ... but why?
                        // fprintf(stderr, "%p %p\n", i0, i1);
                        if (i0) {

                          cur_val = (uint64_t)i0->getValue().convertToDouble();
                          if (last_val0 && last_val0 == cur_val) { skip = true;

               } last_val0 = cur_val;

                        }

                        if (i1) {

                          cur_val = (uint64_t)i1->getValue().convertToDouble();
                          if (last_val1 && last_val1 == cur_val) { skip = true;

               } last_val1 = cur_val;

                        }

            */
            ConstantFP *i0 = dyn_cast<ConstantFP>(op0);
            ConstantFP *i1 = dyn_cast<ConstantFP>(op1);
            if (i0) {
              misc |= 1;
            }

            if (i1) {
              misc |= 2;
            }

          } else {

            ConstantInt *i0 = dyn_cast<ConstantInt>(op0);
            ConstantInt *i1 = dyn_cast<ConstantInt>(op1);
            if (i0 && i0->uge(0xffffffffffffffff) == false) {

              cur_val = i0->getZExtValue();
              if (last_val0 && last_val0 == cur_val) { skip = true; }
              last_val0 = cur_val;
              // lhs is constant
              misc |= 1;

            }

            if (i1 && i1->uge(0xffffffffffffffff) == false) {

              cur_val = i1->getZExtValue();
              if (last_val1 && last_val1 == cur_val) { skip = true; }
              last_val1 = cur_val;
              // rhs is constant
              misc |= 2;
            }

          }

        } else {
          if (!is_fp) {
            ConstantInt *i0 = dyn_cast<ConstantInt>(op0);
            ConstantInt *i1 = dyn_cast<ConstantInt>(op1);
            if (i0 && i0->uge(0xffffffffffffffff) == false) {
              // lhs is constant
              misc |= 1;
            }

            if (i1 && i1->uge(0xffffffffffffffff) == false) {
              // rhs is constant
              misc |= 2;
            }
          } else {
            ConstantFP *i0 = dyn_cast<ConstantFP>(op0);
            ConstantFP *i1 = dyn_cast<ConstantFP>(op1);
            if (i0) {
              misc |= 1;
            }

            if (i1) {
              misc |= 2;
            }
          }
        }

        if (!skip) {

          // errs() << "[PATALOG] cmp  " << *cmpInst << "(in function " <<
          // cmpInst->getFunction()->getName() << ")\n";

          // first bitcast to integer type of the same bitsize as the original
          // type (this is a nop, if already integer)
          Value *op0_i = IRB.CreateBitCast(
              op0, IntegerType::get(*C, ty0->getPrimitiveSizeInBits()));
          // then create a int cast, which does zext, trunc or bitcast. In our
          // case usually zext to the next larger supported type (this is a nop
          // if already the right type)
          Value *V0 =
              IRB.CreateIntCast(op0_i, IntegerType::get(*C, cast_size), false);
          args.push_back(V0);
          Value *op1_i = IRB.CreateBitCast(
              op1, IntegerType::get(*C, ty1->getPrimitiveSizeInBits()));
          Value *V1 =
              IRB.CreateIntCast(op1_i, IntegerType::get(*C, cast_size), false);
          args.push_back(V1);

          // errs() << "[PATALOG] casted parameters:\n0: " << *V0 << "\n1: " <<
          // *V1
          // << "\n";

          uint32_t cur_id = (uint32_t)-1;
          bool redundant = false;
          Value *constraint_var = vector_cnt > 0 ? op0 : selectcmpInst;
          if (value_to_type.find(op0) != value_to_type.end() &&
              value_to_type[op0] == PATA_KIND_CALL) {
            errs() << "CMP LHS coming from PATA call, skipped: ";
            constraint_var->print(errs());
            Instruction *this_insn = dyn_cast<Instruction>(constraint_var);
            if (this_insn && this_insn->hasMetadata(LLVMContext::MD_dbg)) {
              errs() << ", at ";
              this_insn->getDebugLoc().print(errs());
            }
            errs() << "\n";
            redundant = true;
          } else {
            auto map_it = value_to_type.find(constraint_var);
            if (map_it != value_to_type.end()) {
              errs() << "CMP already instrumented, skipped: ";
              constraint_var->print(errs());
              Instruction *this_insn = dyn_cast<Instruction>(constraint_var);
              if (this_insn && this_insn->hasMetadata(LLVMContext::MD_dbg)) {
                errs() << ", at ";
                this_insn->getDebugLoc().print(errs());
              }
              errs() << "\n";
              redundant = true;
            } else {
              // new one
              cur_id = pata_global_id;
              value_to_type[constraint_var] = PATA_KIND_CMP;
              ++pata_global_id;
            }
          }

          if (!redundant) {
            Function &cur_func = *selectcmpInst->getFunction();
            args.push_back(IRB.CreateLoad(Int32Ty, CreateModuleDataInSection(
                cur_func, Int32Ty, SanCovPataGuardSectionName)));
            uint32_t real_size;
            switch (cast_size) {
              case 8:
                IRB.CreateCall(patalogHookIns1, args);
                real_size = 1;
                break;
              case 16:
                IRB.CreateCall(patalogHookIns2, args);
                real_size = 2;
                break;
              case 32:
                IRB.CreateCall(patalogHookIns4, args);
                real_size = 4;
                break;
              case 64:
                IRB.CreateCall(patalogHookIns8, args);
                real_size = 8;
                break;
              case 128:
                if (max_size == 128) {

                  IRB.CreateCall(patalogHookIns16, args);
                  real_size = 16;

                } else {

                  IRB.CreateCall(patalogHookInsN, args);
                  real_size = (max_size / 8) - 1;

                }

                break;

            }

            // TODO: collect block features
            u32 num_succ;
            Constant *bf;
            Constant *bf_ptr = collectBlockFeatures(
                M, *selectcmpInst, cur_id,
                "__afl_pata_cmp_bf_ptr_", "__afl_pata_cmp_bf_", num_succ, bf);
            ModulePataMetadata = CreateModuleDataInSection(
                cur_func, PataMetadataTy, SanCovPataMetadataSectionName);
            ModulePataMetadata->setInitializer(
              ConstantStruct::get(PataMetadataTy, {
                ConstantPointerNull::get(voidPtrTy),
                bf,
                ConstantInt::get(Int32Ty, num_succ),
                ConstantInt::get(Int8Ty, PATA_KIND_CMP),
                ConstantInt::get(Int8Ty, predicate),
                ConstantInt::get(Int8Ty, real_size),
                ConstantInt::get(Int8Ty, misc)
              }));
            ModulePataMetadata->setAlignment(MaybeAlign(4));
            ModulePataMetadataPtr = CreateModuleDataInSection(
                cur_func, Int32PtrPtrTy, SanCovPataMetadataPtrSectionName);
            ModulePataMetadataPtr->setInitializer(bf_ptr);
            // pata_metadata.push_back(ModulePataMetadata);
          }
        }

        /* else fprintf(stderr, "skipped\n"); */

        ++cur;
        if (cur >= vector_cnt) { break; }

      }

    }

  }

  if (icomps.size())
    return true;
  else
    return false;

}

bool ModuleSanitizerCoverageAFL::hookSwitches(Module &M) {

  std::vector<SwitchInst *> switches;

#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee
#else
  Constant *
#endif
      c1 = M.getOrInsertFunction("__patalog_switch_hook1", VoidTy, Int8Ty, Int32Ty
#if LLVM_VERSION_MAJOR < 5
                                 ,
                                 NULL
#endif
      );
#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee patalogHookIns1 = c1;
#else
  Function *patalogHookIns1 = cast<Function>(c1);
#endif

#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee
#else
  Constant *
#endif
      c2 = M.getOrInsertFunction("__patalog_switch_hook2", VoidTy, Int16Ty, Int32Ty
#if LLVM_VERSION_MAJOR < 5
                                 ,
                                 NULL
#endif
      );
#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee patalogHookIns2 = c2;
#else
  Function *patalogHookIns2 = cast<Function>(c2);
#endif

#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee
#else
  Constant *
#endif
      c4 = M.getOrInsertFunction("__patalog_switch_hook4", VoidTy, Int32Ty, Int32Ty
#if LLVM_VERSION_MAJOR < 5
                                 ,
                                 NULL
#endif
      );
#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee patalogHookIns4 = c4;
#else
  Function *patalogHookIns4 = cast<Function>(c4);
#endif

#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee
#else
  Constant *
#endif
      c8 = M.getOrInsertFunction("__patalog_switch_hook8", VoidTy, Int64Ty, Int32Ty
#if LLVM_VERSION_MAJOR < 5
                                 ,
                                 NULL
#endif
      );
#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee patalogHookIns8 = c8;
#else
  Function *patalogHookIns8 = cast<Function>(c8);
#endif

  /* iterate over all functions, bbs and instruction and add suitable calls */
  for (auto &F : M) {

    if (!isInInstrumentList(&F, MNAME)) continue;

    for (auto &BB : F) {

      SwitchInst *switchInst = nullptr;
      if ((switchInst = dyn_cast<SwitchInst>(BB.getTerminator()))) {

        if (switchInst->getNumCases() > 1) { switches.push_back(switchInst); }

      }

    }

  }

  // unique the collected switches
  switches.erase(Unique(switches.begin(), switches.end()), switches.end());

  // Instrument switch values for patalog
  if (switches.size()) {

    if (!be_quiet)
      errs() << "Hooking " << switches.size() << " switch instructions\n";

    for (auto &SI : switches) {

      Value        *Val = SI->getCondition();
      unsigned int  max_size = Val->getType()->getIntegerBitWidth(), cast_size;
      unsigned char do_cast = 0;

      if (!SI->getNumCases() || max_size < 16) {

        // if (!be_quiet) errs() << "skip trivial switch..\n";
        continue;

      }

      if (max_size % 8) {

        max_size = (((max_size / 8) + 1) * 8);
        do_cast = 1;

      }

      IRBuilder<> IRB(SI);

      if (max_size > 128) {

        if (!be_quiet) {

          fprintf(stderr,
                  "Cannot handle this switch bit size: %u (truncating)\n",
                  max_size);

        }

        max_size = 128;
        do_cast = 1;

      }

      // do we need to cast?
      switch (max_size) {

        case 8:
        case 16:
        case 32:
        case 64:
        case 128:
          cast_size = max_size;
          break;
        default:
          cast_size = 128;
          do_cast = 1;

      }

      Value *CompareTo = Val;

      if (do_cast) {

        CompareTo =
            IRB.CreateIntCast(CompareTo, IntegerType::get(*C, cast_size), false);

      }

      std::vector<Constant*> cases;

      for (SwitchInst::CaseIt i = SI->case_begin(), e = SI->case_end(); i != e;
           ++i) {

#if LLVM_VERSION_MAJOR < 5
        ConstantInt *cint = i.getCaseValue();
#else
        ConstantInt *cint = i->getCaseValue();
#endif

        if (cint) {

          std::vector<Value *> args;
          args.push_back(CompareTo);

          cases.push_back(cint);

//             args.push_back(new_param);
//             ConstantInt *attribute = ConstantInt::get(Int8Ty, 1);
//             args.push_back(attribute);
//             if (cast_size != max_size) {

//               ConstantInt *bitsize =
//                   ConstantInt::get(Int8Ty, (max_size / 8) - 1);
//               args.push_back(bitsize);

//             }

//             switch (cast_size) {

//               case 8:
//                 IRB.CreateCall(patalogHookIns1, args);
//                 break;
//               case 16:
//                 IRB.CreateCall(patalogHookIns2, args);
//                 break;
//               case 32:
//                 IRB.CreateCall(patalogHookIns4, args);
//                 break;
//               case 64:
//                 IRB.CreateCall(patalogHookIns8, args);
//                 break;
//               case 128:
// #ifdef WORD_SIZE_64
//                 if (max_size == 128) {

//                   IRB.CreateCall(patalogHookIns16, args);

//                 } else {

//                   IRB.CreateCall(patalogHookInsN, args);

//                 }

// #endif
//                 break;
//               default:
//                 break;

//             }


        }

      }

      uint32_t num_cases = cases.size();
      if (num_cases > 0xFFFF) {
          errs() << "Too many cases (" << num_cases <<  ") in a switch: ";
          SI->print(errs());
          errs() << "\n";
          num_cases = 0;
      }
      if (num_cases) {
        bool redundant = false;
        uint32_t cur_id = (uint32_t)-1;
        if (value_to_type.find(CompareTo) != value_to_type.end() &&
          value_to_type[CompareTo] == PATA_KIND_CALL) {
          errs() << "SWITCH value coming from PATA call, skipped: ";
          SI->print(errs());
          Instruction *this_insn = dyn_cast<Instruction>(SI);
          if (this_insn && this_insn->hasMetadata(LLVMContext::MD_dbg)) {
            errs() << ", at ";
            this_insn->getDebugLoc().print(errs());
          }
          errs() << "\n";
          redundant = true;
        } else {
          auto map_it = value_to_type.find(SI);
          if (map_it != value_to_type.end()) {
            errs() << "SWITCH already instrumented, skipped: ";
            SI->print(errs());
            Instruction *this_insn = dyn_cast<Instruction>(SI);
            if (this_insn && this_insn->hasMetadata(LLVMContext::MD_dbg)) {
              errs() << ", at ";
              this_insn->getDebugLoc().print(errs());
            }
            errs() << "\n";
            redundant = true;
          } else {
            // new one
            cur_id = pata_global_id;
            value_to_type[SI] = PATA_KIND_SWITCH;
            ++pata_global_id;
          }
        }

        if (!redundant) {
          std::vector<Value *> args;
          Function &cur_func = *SI->getFunction();
          args.push_back(CompareTo);
          args.push_back(IRB.CreateLoad(Int32Ty, CreateModuleDataInSection(
              cur_func, Int32Ty, SanCovPataGuardSectionName)));

          bool created = false;
          uint32_t real_size;
          Type *real_type;

          switch (cast_size) {
            case 8:
              IRB.CreateCall(patalogHookIns1, args);
              created = true;
              real_size = 1;
              real_type = Int8Ty;
              break;
            case 16:
              IRB.CreateCall(patalogHookIns2, args);
              created = true;
              real_size = 2;
              real_type = Int16Ty;
              break;
            case 32:
              IRB.CreateCall(patalogHookIns4, args);
              created = true;
              real_size = 4;
              real_type = Int32Ty;
              break;
            case 64:
              IRB.CreateCall(patalogHookIns8, args);
              created = true;
              real_size = 8;
              real_type = Int64Ty;
              break;
            default:
              FATAL("should not happen");
              break;
          }

          if (created) {
            auto global_name = "__afl_pata_switch_metadata_" + std::to_string(cur_id);
            auto tmp_ty = ArrayType::get(real_type, num_cases);
            M.getOrInsertGlobal(global_name, tmp_ty);
            auto cases_metadata = M.getNamedGlobal(global_name);

            cases_metadata->setInitializer(ConstantArray::get(tmp_ty, cases));
            // avoid name collision
            cases_metadata->setLinkage(llvm::GlobalValue::InternalLinkage);

            uint8_t size_lsb = num_cases & 0xFF;
            uint8_t size_msb = (num_cases >> 8) & 0xFF;

            // TODO: collect block features
            u32 num_succ;
            Constant *bf;
            Constant *bf_ptr = collectBlockFeatures(
                M, *SI, cur_id,
                "__afl_pata_switch_bf_ptr_", "__afl_pata_switch_bf_",
                num_succ, bf);
            ModulePataMetadata = CreateModuleDataInSection(
                cur_func, PataMetadataTy, SanCovPataMetadataSectionName);
            ModulePataMetadata->setInitializer(
              ConstantStruct::get(PataMetadataTy, {
                cases_metadata,
                bf,
                ConstantInt::get(Int32Ty, num_succ),
                ConstantInt::get(Int8Ty, PATA_KIND_SWITCH),
                ConstantInt::get(Int8Ty, size_lsb),
                ConstantInt::get(Int8Ty, real_size),
                ConstantInt::get(Int8Ty, size_msb),
              }));
            ModulePataMetadata->setAlignment(MaybeAlign(4));
            ModulePataMetadataPtr = CreateModuleDataInSection(
                cur_func, Int32PtrPtrTy, SanCovPataMetadataPtrSectionName);
            ModulePataMetadataPtr->setInitializer(bf_ptr);
          }
        }
      }

    }

  }

  if (switches.size())
    return true;
  else
    return false;

}

bool ModuleSanitizerCoverageAFL::hookRtns(Module &M) {

  std::vector<CallInst *> Memcmp, Strcmp, Strncmp, Strstr, Memmem;

#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee
#else
  Constant *
#endif
      c = M.getOrInsertFunction("__patalog_memcmp_hook", VoidTy, Int8PtrTy,
                                 Int8PtrTy, Int64Ty, Int32Ty
#if LLVM_VERSION_MAJOR < 5
                                 ,
                                 NULL
#endif
      );
#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee patalogHookMemcmp = c;
#else
  Function *patalogHookMemcmp = cast<Function>(c);
#endif

#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee
#else
  Constant *
#endif
      c1 = M.getOrInsertFunction("__patalog_strncmp_hook", VoidTy, Int8PtrTy,
                                 Int8PtrTy, Int64Ty, Int32Ty
#if LLVM_VERSION_MAJOR < 5
                                 ,
                                 NULL
#endif
      );
#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee patalogHookStrncmp = c1;
#else
  Function *patalogHookStrncmp = cast<Function>(c1);
#endif

#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee
#else
  Constant *
#endif
      c2 = M.getOrInsertFunction("__patalog_strcmp_hook", VoidTy, Int8PtrTy,
                                 Int8PtrTy, Int32Ty
#if LLVM_VERSION_MAJOR < 5
                                 ,
                                 NULL
#endif
      );
#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee patalogHookStrcmp = c2;
#else
  Function *patalogHookStrcmp = cast<Function>(c2);
#endif

#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee
#else
  Constant *
#endif
      c3 = M.getOrInsertFunction("__patalog_memmem_hook", VoidTy, Int8PtrTy,
                                 Int64Ty, Int8PtrTy, Int64Ty, Int32Ty
#if LLVM_VERSION_MAJOR < 5
                                 ,
                                 NULL
#endif
      );
#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee patalogHookMemmem = c3;
#else
  Function *patalogHookMemmem = cast<Function>(c3);
#endif

#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee
#else
  Constant *
#endif
      c4 = M.getOrInsertFunction("__patalog_strstr_hook", VoidTy, Int8PtrTy,
                                 Int8PtrTy, Int32Ty
#if LLVM_VERSION_MAJOR < 5
                                 ,
                                 NULL
#endif
      );
#if LLVM_VERSION_MAJOR >= 9
  FunctionCallee patalogHookStrstr = c4;
#else
  Function *patalogHookStrstr = cast<Function>(c4);
#endif

  /* iterate over all functions, bbs and instruction and add suitable calls */
  for (auto &F : M) {

    if (!isInInstrumentList(&F, MNAME)) continue;

    for (auto &BB : F) {

      for (auto &IN : BB) {

        CallInst *callInst = nullptr;

        if ((callInst = dyn_cast<CallInst>(&IN))) {

          Function *Callee = callInst->getCalledFunction();
          if (!Callee) continue;
          if (callInst->getCallingConv() != llvm::CallingConv::C) continue;

          FunctionType *FT = Callee->getFunctionType();
          std::string   FuncName = Callee->getName().str();

          bool isPtrRtn = FT->getNumParams() >= 2 &&
                          !FT->getReturnType()->isVoidTy() &&
                          FT->getParamType(0) == FT->getParamType(1) &&
                          FT->getParamType(0)->isPointerTy();

          bool isPtrRtnN = FT->getNumParams() >= 3 &&
                           !FT->getReturnType()->isVoidTy() &&
                           FT->getParamType(0) == FT->getParamType(1) &&
                           FT->getParamType(0)->isPointerTy() &&
                           FT->getParamType(2)->isIntegerTy();
          if (isPtrRtnN) {

            auto intTyOp =
                dyn_cast<IntegerType>(callInst->getArgOperand(2)->getType());
            if (intTyOp) {

              if (intTyOp->getBitWidth() != 32 &&
                  intTyOp->getBitWidth() != 64) {

                isPtrRtnN = false;

              }

            }

          }

          bool isMemcmp =
              (!FuncName.compare("memcmp") || !FuncName.compare("bcmp"));
          isMemcmp &= FT->getNumParams() == 3 &&
                      FT->getReturnType()->isIntegerTy(32) &&
                      FT->getParamType(0)->isPointerTy() &&
                      FT->getParamType(1)->isPointerTy() &&
                      FT->getParamType(2)->isIntegerTy();

          bool isStrcmp =
              (!FuncName.compare("strcmp") || !FuncName.compare("strcasecmp"));
          isStrcmp &=
              FT->getNumParams() == 2 && FT->getReturnType()->isIntegerTy(32) &&
              FT->getParamType(0) == FT->getParamType(1) &&
              FT->getParamType(0) == IntegerType::getInt8PtrTy(M.getContext());

          bool isStrstr = 
            (!FuncName.compare("strstr") || !FuncName.compare("strcasestr"));
          isStrstr &=
              FT->getNumParams() == 2 && FT->getReturnType()->isPointerTy() &&
              FT->getParamType(0) == FT->getParamType(1) &&
              FT->getParamType(0) == IntegerType::getInt8PtrTy(M.getContext());
          
          bool isStrncmp = (!FuncName.compare("strncmp") ||
                            !FuncName.compare("strncasecmp"));
          isStrncmp &= FT->getNumParams() == 3 &&
                       FT->getReturnType()->isIntegerTy(32) &&
                       FT->getParamType(0) == FT->getParamType(1) &&
                       FT->getParamType(0) ==
                           IntegerType::getInt8PtrTy(M.getContext()) &&
                       FT->getParamType(2)->isIntegerTy();
          
          bool isMemmem = !FuncName.compare("memmem");
          isMemmem &= FT->getNumParams() == 4 &&
                      FT->getReturnType()->isPointerTy() &&
                      FT->getParamType(0) == FT->getParamType(2) &&
                      FT->getParamType(1) == FT->getParamType(3) &&
                      FT->getParamType(0)->isPointerTy() &&
                      FT->getParamType(2)->isIntegerTy();

          /*
                    {

                       fprintf(stderr, "F:%s C:%s argc:%u\n",
                       F.getName().str().c_str(),
             Callee->getName().str().c_str(), FT->getNumParams());
                       fprintf(stderr, "ptr0:%u ptr1:%u ptr2:%u\n",
                              FT->getParamType(0)->isPointerTy(),
                              FT->getParamType(1)->isPointerTy(),
                              FT->getNumParams() > 2 ?
             FT->getParamType(2)->isPointerTy() : 22 );

                    }

          */

          if (isMemcmp || isStrcmp || isStrncmp || isStrstr || isMemmem) {

            isPtrRtnN = isPtrRtn = false;

          }


          if (isMemcmp) { Memcmp.push_back(callInst); }
          if (isStrcmp) { Strcmp.push_back(callInst); }
          if (isStrncmp) { Strncmp.push_back(callInst); }
          if (isStrstr) { Strstr.push_back(callInst); }
          if (isMemmem) { Memmem.push_back(callInst); }

        }

      }

    }

  }

  if (!Memcmp.size() && !Strcmp.size() &&
      !Strncmp.size() && !Strstr.size() && !Memmem.size())
    return false;

  /*
    if (!be_quiet)
      errs() << "Hooking " << calls.size()
             << " calls with pointers as arguments\n";
  */

  u32 num_succ;
  Constant *bf;
  Constant *bf_ptr;
  Function *cur_func;
  for (auto &callInst : Memcmp) {

    Value *v1P = callInst->getArgOperand(0), *v2P = callInst->getArgOperand(1),
          *v3P = callInst->getArgOperand(2);

    IRBuilder<> IRB(callInst);

    uint32_t cur_id = (uint32_t)-1;
    bool redundant = false;
    auto map_it = value_to_type.find(callInst);
    if (map_it != value_to_type.end()) {
      errs() << "CALL already instrumented, skipped: ";
      callInst->print(errs());
      errs() << "\n";
      redundant = true;
    } else {
      // new one
      cur_id = pata_global_id;
      value_to_type[callInst] = PATA_KIND_CALL;
      ++pata_global_id;
    }
    
    if (!redundant) {
      cur_func = callInst->getFunction();
      std::vector<Value *> args;
      Value               *v1Pcasted = IRB.CreatePointerCast(v1P, Int8PtrTy);
      Value               *v2Pcasted = IRB.CreatePointerCast(v2P, Int8PtrTy);
      Value               *v3Pbitcast = IRB.CreateBitCast(
                        v3P, IntegerType::get(*C, v3P->getType()->getPrimitiveSizeInBits()));
      Value *v3Pcasted =
          IRB.CreateIntCast(v3Pbitcast, IntegerType::get(*C, 64), false);
      args.push_back(v1Pcasted);
      args.push_back(v2Pcasted);
      args.push_back(v3Pcasted);
      args.push_back(IRB.CreateLoad(Int32Ty, CreateModuleDataInSection(
          *cur_func, Int32Ty, SanCovPataGuardSectionName)));

      IRB.CreateCall(patalogHookMemcmp, args);

      bf_ptr = collectBlockFeatures(
          M, *callInst, cur_id,
          "__afl_pata_call_bf_ptr_", "__afl_pata_call_bf_", num_succ, bf);
      ModulePataMetadata = CreateModuleDataInSection(
          *cur_func, PataMetadataTy, SanCovPataMetadataSectionName);
      ModulePataMetadata->setInitializer(
        ConstantStruct::get(PataMetadataTy, {
          ConstantPointerNull::get(voidPtrTy),
          bf,
          ConstantInt::get(Int32Ty, num_succ),
          ConstantInt::get(Int8Ty, PATA_KIND_CALL),
          ConstantInt::get(Int8Ty, PATA_CALL_MEMCMP),
          ConstantInt::get(Int8Ty, 0),
          ConstantInt::get(Int8Ty, 0),
        }));
      ModulePataMetadata->setAlignment(MaybeAlign(4));
      ModulePataMetadataPtr = CreateModuleDataInSection(
          *cur_func, Int32PtrPtrTy, SanCovPataMetadataPtrSectionName);
      ModulePataMetadataPtr->setInitializer(bf_ptr);
    }

    // errs() << callInst->getCalledFunction()->getName() << "\n";

  }

  for (auto &callInst : Strcmp) {

    Value *v1P = callInst->getArgOperand(0), *v2P = callInst->getArgOperand(1);

    IRBuilder<> IRB(callInst);

    uint32_t cur_id = (uint32_t)-1;
    bool redundant = false;
    auto map_it = value_to_type.find(callInst);
    if (map_it != value_to_type.end()) {
      errs() << "CALL already instrumented, skipped: ";
      callInst->print(errs());
      errs() << "\n";
      redundant = true;
    } else {
      // new one
      cur_id = pata_global_id;
      value_to_type[callInst] = PATA_KIND_CALL;
      ++pata_global_id;
    }

    if (!redundant) {
      cur_func = callInst->getFunction();
      std::vector<Value *> args;
      Value               *v1Pcasted = IRB.CreatePointerCast(v1P, Int8PtrTy);
      Value               *v2Pcasted = IRB.CreatePointerCast(v2P, Int8PtrTy);
      args.push_back(v1Pcasted);
      args.push_back(v2Pcasted);
      args.push_back(IRB.CreateLoad(Int32Ty, CreateModuleDataInSection(
          *cur_func, Int32Ty, SanCovPataGuardSectionName)));

      IRB.CreateCall(patalogHookStrcmp, args);

      bf_ptr = collectBlockFeatures(
          M, *callInst, cur_id,
          "__afl_pata_call_bf_ptr_", "__afl_pata_call_bf_", num_succ, bf);
      ModulePataMetadata = CreateModuleDataInSection(
          *cur_func, PataMetadataTy, SanCovPataMetadataSectionName);
      ModulePataMetadata->setInitializer(
        ConstantStruct::get(PataMetadataTy, {
          ConstantPointerNull::get(voidPtrTy),
          bf,
          ConstantInt::get(Int32Ty, num_succ),
          ConstantInt::get(Int8Ty, PATA_KIND_CALL),
          ConstantInt::get(Int8Ty, PATA_CALL_STRCMP),
          ConstantInt::get(Int8Ty, 0),
          ConstantInt::get(Int8Ty, 0),
        }));
      ModulePataMetadata->setAlignment(MaybeAlign(4));
      ModulePataMetadataPtr = CreateModuleDataInSection(
          *cur_func, Int32PtrPtrTy, SanCovPataMetadataPtrSectionName);
      ModulePataMetadataPtr->setInitializer(bf_ptr);
    }

    // errs() << callInst->getCalledFunction()->getName() << "\n";

  }

  for (auto &callInst : Strncmp) {

    Value *v1P = callInst->getArgOperand(0), *v2P = callInst->getArgOperand(1),
          *v3P = callInst->getArgOperand(2);

    IRBuilder<> IRB(callInst);

    uint32_t cur_id = (uint32_t)-1;
    bool redundant = false;
    auto map_it = value_to_type.find(callInst);
    if (map_it != value_to_type.end()) {
      errs() << "CALL already instrumented, skipped: ";
      callInst->print(errs());
      errs() << "\n";
      redundant = true;
    } else {
      // new one
      cur_id = pata_global_id;
      value_to_type[callInst] = PATA_KIND_CALL;
      ++pata_global_id;
    }

    if (!redundant) {
      cur_func = callInst->getFunction();
      std::vector<Value *> args;
      Value               *v1Pcasted = IRB.CreatePointerCast(v1P, Int8PtrTy);
      Value               *v2Pcasted = IRB.CreatePointerCast(v2P, Int8PtrTy);
      Value               *v3Pbitcast = IRB.CreateBitCast(
                        v3P, IntegerType::get(*C, v3P->getType()->getPrimitiveSizeInBits()));
      Value *v3Pcasted =
          IRB.CreateIntCast(v3Pbitcast, IntegerType::get(*C, 64), false);
      args.push_back(v1Pcasted);
      args.push_back(v2Pcasted);
      args.push_back(v3Pcasted);
      args.push_back(IRB.CreateLoad(Int32Ty, CreateModuleDataInSection(
          *cur_func, Int32Ty, SanCovPataGuardSectionName)));

      IRB.CreateCall(patalogHookStrncmp, args);

      bf_ptr = collectBlockFeatures(
          M, *callInst, cur_id,
          "__afl_pata_call_bf_ptr_", "__afl_pata_call_bf_", num_succ, bf);
      ModulePataMetadata = CreateModuleDataInSection(
          *cur_func, PataMetadataTy, SanCovPataMetadataSectionName);
      ModulePataMetadata->setInitializer(
        ConstantStruct::get(PataMetadataTy, {
          ConstantPointerNull::get(voidPtrTy),
          bf,
          ConstantInt::get(Int32Ty, num_succ),
          ConstantInt::get(Int8Ty, PATA_KIND_CALL),
          ConstantInt::get(Int8Ty, PATA_CALL_STRNCMP),
          ConstantInt::get(Int8Ty, 0),
          ConstantInt::get(Int8Ty, 0),
        }));
      ModulePataMetadata->setAlignment(MaybeAlign(4));
      ModulePataMetadataPtr = CreateModuleDataInSection(
          *cur_func, Int32PtrPtrTy, SanCovPataMetadataPtrSectionName);
      ModulePataMetadataPtr->setInitializer(bf_ptr);
    }

    // errs() << callInst->getCalledFunction()->getName() << "\n";

  }

  for (auto &callInst : Strstr) {
    Value *v1P = callInst->getArgOperand(0), *v2P = callInst->getArgOperand(1);

    IRBuilder<> IRB(callInst);

    uint32_t cur_id = (uint32_t)-1;
    bool redundant = false;
    auto map_it = value_to_type.find(callInst);
    if (map_it != value_to_type.end()) {
      errs() << "CALL already instrumented, skipped: ";
      callInst->print(errs());
      errs() << "\n";
      redundant = true;
    } else {
      // new one
      cur_id = pata_global_id;
      value_to_type[callInst] = PATA_KIND_CALL;
      ++pata_global_id;
    }

    if (!redundant) {
      cur_func = callInst->getFunction();
      std::vector<Value *> args;
      Value               *v1Pcasted = IRB.CreatePointerCast(v1P, Int8PtrTy);
      Value               *v2Pcasted = IRB.CreatePointerCast(v2P, Int8PtrTy);
      args.push_back(v1Pcasted);
      args.push_back(v2Pcasted);
      args.push_back(IRB.CreateLoad(Int32Ty, CreateModuleDataInSection(
          *cur_func, Int32Ty, SanCovPataGuardSectionName)));

      IRB.CreateCall(patalogHookStrstr, args);

      bf_ptr = collectBlockFeatures(
          M, *callInst, cur_id,
          "__afl_pata_call_bf_ptr_", "__afl_pata_call_bf_", num_succ, bf);
      ModulePataMetadata = CreateModuleDataInSection(
          *cur_func, PataMetadataTy, SanCovPataMetadataSectionName);
      ModulePataMetadata->setInitializer(
        ConstantStruct::get(PataMetadataTy, {
          ConstantPointerNull::get(voidPtrTy),
          bf,
          ConstantInt::get(Int32Ty, num_succ),
          ConstantInt::get(Int8Ty, PATA_KIND_CALL),
          ConstantInt::get(Int8Ty, PATA_CALL_STRSTR),
          ConstantInt::get(Int8Ty, 0),
          ConstantInt::get(Int8Ty, 0),
        }));
      ModulePataMetadata->setAlignment(MaybeAlign(4));
      ModulePataMetadataPtr = CreateModuleDataInSection(
          *cur_func, Int32PtrPtrTy, SanCovPataMetadataPtrSectionName);
      ModulePataMetadataPtr->setInitializer(bf_ptr);
    }
  }

  for (auto &callInst : Memmem) {
    Value *v1P = callInst->getArgOperand(0), *v2P = callInst->getArgOperand(1),
          *v3P = callInst->getArgOperand(2), *v4P = callInst->getArgOperand(3);

    IRBuilder<> IRB(callInst);

    uint32_t cur_id = (uint32_t)-1;
    bool redundant = false;
    auto map_it = value_to_type.find(callInst);
    if (map_it != value_to_type.end()) {
      errs() << "CALL already instrumented, skipped: ";
      callInst->print(errs());
      errs() << "\n";
      redundant = true;
    } else {
      // new one
      cur_id = pata_global_id;
      value_to_type[callInst] = PATA_KIND_CALL;
      ++pata_global_id;
    }
    
    if (!redundant) {
      cur_func = callInst->getFunction();
      std::vector<Value *> args;
      Value               *v1Pcasted = IRB.CreatePointerCast(v1P, Int8PtrTy);
      Value               *v3Pcasted = IRB.CreatePointerCast(v3P, Int8PtrTy);
      Value               *v2Pbitcast = IRB.CreateBitCast(
                        v2P, IntegerType::get(*C, v2P->getType()->getPrimitiveSizeInBits()));
      Value               *v4Pbitcast = IRB.CreateBitCast(
                        v4P, IntegerType::get(*C, v4P->getType()->getPrimitiveSizeInBits()));
      Value *v2Pcasted =
          IRB.CreateIntCast(v2Pbitcast, IntegerType::get(*C, 64), false);
      Value *v4Pcasted =
          IRB.CreateIntCast(v4Pbitcast, IntegerType::get(*C, 64), false);
      args.push_back(v1Pcasted);
      args.push_back(v2Pcasted);
      args.push_back(v3Pcasted);
      args.push_back(v4Pcasted);
      args.push_back(IRB.CreateLoad(Int32Ty, CreateModuleDataInSection(
          *cur_func, Int32Ty, SanCovPataGuardSectionName)));

      IRB.CreateCall(patalogHookMemmem, args);

      bf_ptr = collectBlockFeatures(
          M, *callInst, cur_id,
          "__afl_pata_call_bf_ptr_", "__afl_pata_call_bf_", num_succ, bf);
      ModulePataMetadata = CreateModuleDataInSection(
          *cur_func, PataMetadataTy, SanCovPataMetadataSectionName);
      ModulePataMetadata->setInitializer(
        ConstantStruct::get(PataMetadataTy, {
          ConstantPointerNull::get(voidPtrTy),
          bf,
          ConstantInt::get(Int32Ty, num_succ),
          ConstantInt::get(Int8Ty, PATA_KIND_CALL),
          ConstantInt::get(Int8Ty, PATA_CALL_MEMMEM),
          ConstantInt::get(Int8Ty, 0),
          ConstantInt::get(Int8Ty, 0),
        }));
      ModulePataMetadata->setAlignment(MaybeAlign(4));
      ModulePataMetadataPtr = CreateModuleDataInSection(
          *cur_func, Int32PtrPtrTy, SanCovPataMetadataPtrSectionName);
      ModulePataMetadataPtr->setInitializer(bf_ptr);
    }
  }

  return true;

}

void ModuleSanitizerCoverageAFL::initializePataGlobals(Module &M) {
  Int128Ty = IntegerType::getInt128Ty(*C);
  voidPtrTy = PointerType::get(VoidTy, 0);
  Int32PtrPtrTy = PointerType::get(Int32PtrTy, 0);
  Int32PtrPtrPtrTy = PointerType::get(Int32PtrPtrTy, 0);

  PataMetadataTy = StructType::create(*C);
  PataMetadataTy->setBody(
      {voidPtrTy, Int32PtrTy, Int32Ty, Int8Ty, Int8Ty, Int8Ty, Int8Ty}, true);
  
  PataMetadataPtrTy = PointerType::get(PataMetadataTy, 0);

  Null = Constant::getNullValue(PointerType::get(Int8Ty, 0));
}
/* PATA end */

PreservedAnalyses ModuleSanitizerCoverageAFL::run(Module                &M,
                                                  ModuleAnalysisManager &MAM) {

  ModuleSanitizerCoverageAFL ModuleSancov(Options);
  auto &FAM = MAM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();
  auto  DTCallback = [&FAM](Function &F) -> const DominatorTree  *{

    return &FAM.getResult<DominatorTreeAnalysis>(F);

  };

  auto PDTCallback = [&FAM](Function &F) -> const PostDominatorTree * {

    return &FAM.getResult<PostDominatorTreeAnalysis>(F);

  };

  if (ModuleSancov.instrumentModule(M, DTCallback, PDTCallback))
    return PreservedAnalyses::none();
  return PreservedAnalyses::all();

}

std::pair<Value *, Value *> ModuleSanitizerCoverageAFL::CreateSecStartEnd(
    Module &M, const char *Section, Type *Ty) {

  GlobalVariable *SecStart =
      new GlobalVariable(M,
#if LLVM_VERSION_MAJOR >= 15
                         Ty,
#else
                         Ty->getPointerElementType(),
#endif
                         false, GlobalVariable::ExternalWeakLinkage, nullptr,
                         getSectionStart(Section));
  SecStart->setVisibility(GlobalValue::HiddenVisibility);
  GlobalVariable *SecEnd =
      new GlobalVariable(M,
#if LLVM_VERSION_MAJOR >= 15
                         Ty,
#else
                         Ty->getPointerElementType(),
#endif
                         false, GlobalVariable::ExternalWeakLinkage, nullptr,
                         getSectionEnd(Section));
  SecEnd->setVisibility(GlobalValue::HiddenVisibility);
  IRBuilder<> IRB(M.getContext());
  if (!TargetTriple.isOSBinFormatCOFF())
    return std::make_pair(SecStart, SecEnd);

  // Account for the fact that on windows-msvc __start_* symbols actually
  // point to a uint64_t before the start of the array.
  auto SecStartI8Ptr = IRB.CreatePointerCast(SecStart, Int8PtrTy);
  auto GEP = IRB.CreateGEP(Int8Ty, SecStartI8Ptr,
                           ConstantInt::get(IntptrTy, sizeof(uint64_t)));
  return std::make_pair(IRB.CreatePointerCast(GEP, Ty), SecEnd);

}

Function *ModuleSanitizerCoverageAFL::CreateInitCallsForSections(
    Module &M, const char *CtorName, const char *InitFunctionName, Type *Ty,
    const char *Section) {

  auto      SecStartEnd = CreateSecStartEnd(M, Section, Ty);
  auto      SecStart = SecStartEnd.first;
  auto      SecEnd = SecStartEnd.second;
  Function *CtorFunc;
  std::tie(CtorFunc, std::ignore) = createSanitizerCtorAndInitFunctions(
      M, CtorName, InitFunctionName, {Ty, Ty}, {SecStart, SecEnd});
  assert(CtorFunc->getName() == CtorName);

  if (TargetTriple.supportsCOMDAT()) {

    // Use comdat to dedup CtorFunc.
    CtorFunc->setComdat(M.getOrInsertComdat(CtorName));
    appendToGlobalCtors(M, CtorFunc, SanCtorAndDtorPriority, CtorFunc);

  } else {

    appendToGlobalCtors(M, CtorFunc, SanCtorAndDtorPriority);

  }

  if (TargetTriple.isOSBinFormatCOFF()) {

    // In COFF files, if the contructors are set as COMDAT (they are because
    // COFF supports COMDAT) and the linker flag /OPT:REF (strip unreferenced
    // functions and data) is used, the constructors get stripped. To prevent
    // this, give the constructors weak ODR linkage and ensure the linker knows
    // to include the sancov constructor. This way the linker can deduplicate
    // the constructors but always leave one copy.
    CtorFunc->setLinkage(GlobalValue::WeakODRLinkage);
    appendToUsed(M, CtorFunc);

  }

  return CtorFunc;

}

bool ModuleSanitizerCoverageAFL::instrumentModule(
    Module &M, DomTreeCallback DTCallback, PostDomTreeCallback PDTCallback) {

  setvbuf(stdout, NULL, _IONBF, 0);
  if (getenv("AFL_DEBUG")) debug = 1;

  if ((isatty(2) && !getenv("AFL_QUIET")) || debug) {

    SAYF(cCYA "SanitizerCoveragePCGUARD" VERSION cRST "\n");

  } else

    be_quiet = 1;

  skip_nozero = getenv("AFL_LLVM_SKIP_NEVERZERO");
  use_threadsafe_counters = getenv("AFL_LLVM_THREADSAFE_INST");

  initInstrumentList();
  scanForDangerousFunctions(&M);

  if (debug) {

    fprintf(stderr,
            "SANCOV: covtype:%u indirect:%d stack:%d noprune:%d "
            "createtable:%d tracepcguard:%d tracepc:%d\n",
            Options.CoverageType, Options.IndirectCalls == true ? 1 : 0,
            Options.StackDepth == true ? 1 : 0, Options.NoPrune == true ? 1 : 0,
            // Options.InlineBoolFlag == true ? 1 : 0,
            Options.PCTable == true ? 1 : 0,
            Options.TracePCGuard == true ? 1 : 0,
            Options.TracePC == true ? 1 : 0);

  }

  if (Options.CoverageType == SanitizerCoverageOptions::SCK_None) return false;
  C = &(M.getContext());
  DL = &M.getDataLayout();
  CurModule = &M;
  CurModuleUniqueId = getUniqueModuleId(CurModule);
  TargetTriple = Triple(M.getTargetTriple());
  FunctionGuardArray = nullptr;
  Function8bitCounterArray = nullptr;
  FunctionBoolArray = nullptr;
  FunctionPCsArray = nullptr;
  IntptrTy = Type::getIntNTy(*C, DL->getPointerSizeInBits());
  IntptrPtrTy = PointerType::getUnqual(IntptrTy);
  VoidTy = Type::getVoidTy(*C);
  IRBuilder<> IRB(*C);
  Int64PtrTy = PointerType::getUnqual(IRB.getInt64Ty());
  Int32PtrTy = PointerType::getUnqual(IRB.getInt32Ty());
  Int8PtrTy = PointerType::getUnqual(IRB.getInt8Ty());
  Int1PtrTy = PointerType::getUnqual(IRB.getInt1Ty());
  Int64Ty = IRB.getInt64Ty();
  Int32Ty = IRB.getInt32Ty();
  Int16Ty = IRB.getInt16Ty();
  Int8Ty = IRB.getInt8Ty();
  Int1Ty = IRB.getInt1Ty();
  LLVMContext &Ctx = M.getContext();

  AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");
  One = ConstantInt::get(IntegerType::getInt8Ty(Ctx), 1);
  Zero = ConstantInt::get(IntegerType::getInt8Ty(Ctx), 0);

  SanCovTracePCIndir =
      M.getOrInsertFunction(SanCovTracePCIndirName, VoidTy, IntptrTy);
  // Make sure smaller parameters are zero-extended to i64 if required by the
  // target ABI.
  AttributeList SanCovTraceCmpZeroExtAL;
  SanCovTraceCmpZeroExtAL =
      SanCovTraceCmpZeroExtAL.addParamAttribute(*C, 0, Attribute::ZExt);
  SanCovTraceCmpZeroExtAL =
      SanCovTraceCmpZeroExtAL.addParamAttribute(*C, 1, Attribute::ZExt);

  SanCovTraceCmpFunction[0] =
      M.getOrInsertFunction(SanCovTraceCmp1, SanCovTraceCmpZeroExtAL, VoidTy,
                            IRB.getInt8Ty(), IRB.getInt8Ty());
  SanCovTraceCmpFunction[1] =
      M.getOrInsertFunction(SanCovTraceCmp2, SanCovTraceCmpZeroExtAL, VoidTy,
                            IRB.getInt16Ty(), IRB.getInt16Ty());
  SanCovTraceCmpFunction[2] =
      M.getOrInsertFunction(SanCovTraceCmp4, SanCovTraceCmpZeroExtAL, VoidTy,
                            IRB.getInt32Ty(), IRB.getInt32Ty());
  SanCovTraceCmpFunction[3] =
      M.getOrInsertFunction(SanCovTraceCmp8, VoidTy, Int64Ty, Int64Ty);

  SanCovTraceConstCmpFunction[0] = M.getOrInsertFunction(
      SanCovTraceConstCmp1, SanCovTraceCmpZeroExtAL, VoidTy, Int8Ty, Int8Ty);
  SanCovTraceConstCmpFunction[1] = M.getOrInsertFunction(
      SanCovTraceConstCmp2, SanCovTraceCmpZeroExtAL, VoidTy, Int16Ty, Int16Ty);
  SanCovTraceConstCmpFunction[2] = M.getOrInsertFunction(
      SanCovTraceConstCmp4, SanCovTraceCmpZeroExtAL, VoidTy, Int32Ty, Int32Ty);
  SanCovTraceConstCmpFunction[3] =
      M.getOrInsertFunction(SanCovTraceConstCmp8, VoidTy, Int64Ty, Int64Ty);

  {

    AttributeList AL;
    AL = AL.addParamAttribute(*C, 0, Attribute::ZExt);
    SanCovTraceDivFunction[0] =
        M.getOrInsertFunction(SanCovTraceDiv4, AL, VoidTy, IRB.getInt32Ty());

  }

  SanCovTraceDivFunction[1] =
      M.getOrInsertFunction(SanCovTraceDiv8, VoidTy, Int64Ty);
  SanCovTraceGepFunction =
      M.getOrInsertFunction(SanCovTraceGep, VoidTy, IntptrTy);
  SanCovTraceSwitchFunction =
      M.getOrInsertFunction(SanCovTraceSwitchName, VoidTy, Int64Ty, Int64PtrTy);

  Constant *SanCovLowestStackConstant =
      M.getOrInsertGlobal(SanCovLowestStackName, IntptrTy);
  SanCovLowestStack = dyn_cast<GlobalVariable>(SanCovLowestStackConstant);
  if (!SanCovLowestStack) {

    C->emitError(StringRef("'") + SanCovLowestStackName +
                 "' should not be declared by the user");
    return true;

  }

  SanCovLowestStack->setThreadLocalMode(
      GlobalValue::ThreadLocalMode::InitialExecTLSModel);
  if (Options.StackDepth && !SanCovLowestStack->isDeclaration())
    SanCovLowestStack->setInitializer(Constant::getAllOnesValue(IntptrTy));

  SanCovTracePC = M.getOrInsertFunction(SanCovTracePCName, VoidTy);
  SanCovTracePCGuard =
      M.getOrInsertFunction(SanCovTracePCGuardName, VoidTy, Int32PtrTy);

  /* PATA begin */
  patalog_mode = 0;
  if (getenv("AFL_LLVM_PATALOG") || getenv("AFL_PATALOG")) { patalog_mode = 1; }
  if (patalog_mode) { initializePataGlobals(M); }
  /* PATA end */
  
  for (auto &F : M)
    instrumentFunction(F, DTCallback, PDTCallback);

  /* PATA begin */
  if (patalog_mode) {
    pata_global_id = 0;
    hookRtns(M);
    hookSwitches(M);
    hookCmps(M);
  }
  /* PATA end*/

  Function *Ctor = nullptr;

  if (FunctionGuardArray)
    Ctor = CreateInitCallsForSections(M, SanCovModuleCtorTracePcGuardName,
                                      SanCovTracePCGuardInitName, Int32PtrTy,
                                      SanCovGuardsSectionName);
  if (Function8bitCounterArray)
    Ctor = CreateInitCallsForSections(M, SanCovModuleCtor8bitCountersName,
                                      SanCov8bitCountersInitName, Int8PtrTy,
                                      SanCovCountersSectionName);
  if (FunctionBoolArray) {

    Ctor = CreateInitCallsForSections(M, SanCovModuleCtorBoolFlagName,
                                      SanCovBoolFlagInitName, Int1PtrTy,
                                      SanCovBoolFlagSectionName);

  }

  if (patalog_mode) {
    Ctor = CreateInitCallsForSections(M, SanCovModuleCtorPataGuardName,
                                    SanCovPataGuardInitName, Int32PtrTy,
                                    SanCovPataGuardSectionName);
    Ctor = CreateInitCallsForSections(M, SanCovModuleCtorPataMetadataPtrName,
                                    SanCovPataMetadataPtrInitName,
                                    Int32PtrPtrPtrTy,
                                    SanCovPataMetadataPtrSectionName);
    Ctor = CreateInitCallsForSections(M, SanCovModuleCtorPataMetadataName,
                                    SanCovPataMetadataInitName,
                                    PataMetadataPtrTy,
                                    SanCovPataMetadataSectionName);
  }

  if (Ctor && Options.PCTable) {

    auto SecStartEnd = CreateSecStartEnd(M, SanCovPCsSectionName, IntptrPtrTy);
    FunctionCallee InitFunction = declareSanitizerInitFunction(
        M, SanCovPCsInitName, {IntptrPtrTy, IntptrPtrTy});
    IRBuilder<> IRBCtor(Ctor->getEntryBlock().getTerminator());
    IRBCtor.CreateCall(InitFunction, {SecStartEnd.first, SecStartEnd.second});

  }

  // We don't reference these arrays directly in any of our runtime functions,
  // so we need to prevent them from being dead stripped.
  if (TargetTriple.isOSBinFormatMachO()) appendToUsed(M, GlobalsToAppendToUsed);
  appendToCompilerUsed(M, GlobalsToAppendToCompilerUsed);

  if (!be_quiet) {

    if (!instr)
      WARNF("No instrumentation targets found.");
    else {

      char modeline[100];
      snprintf(modeline, sizeof(modeline), "%s%s%s%s%s%s",
               getenv("AFL_HARDEN") ? "hardened" : "non-hardened",
               getenv("AFL_USE_ASAN") ? ", ASAN" : "",
               getenv("AFL_USE_MSAN") ? ", MSAN" : "",
               getenv("AFL_USE_TSAN") ? ", TSAN" : "",
               getenv("AFL_USE_CFISAN") ? ", CFISAN" : "",
               getenv("AFL_USE_UBSAN") ? ", UBSAN" : "");
      OKF("Instrumented %u locations with no collisions (%s mode) of which are "
          "%u handled and %u unhandled selects.",
          instr, modeline, selects, unhandled);

    }

  }

  return true;

}

// True if block has successors and it dominates all of them.
bool isFullDominator(const BasicBlock *BB, const DominatorTree *DT) {

  if (succ_begin(BB) == succ_end(BB)) return false;

  for (const BasicBlock *SUCC : make_range(succ_begin(BB), succ_end(BB))) {

    if (!DT->dominates(BB, SUCC)) return false;

  }

  return true;

}

// True if block has predecessors and it postdominates all of them.
bool isFullPostDominator(const BasicBlock *BB, const PostDominatorTree *PDT) {

  if (pred_begin(BB) == pred_end(BB)) return false;

  for (const BasicBlock *PRED : make_range(pred_begin(BB), pred_end(BB))) {

    if (!PDT->dominates(BB, PRED)) return false;

  }

  return true;

}

bool shouldInstrumentBlock(const Function &F, const BasicBlock *BB,
                           const DominatorTree            *DT,
                           const PostDominatorTree        *PDT,
                           const SanitizerCoverageOptions &Options) {

  // Don't insert coverage for blocks containing nothing but unreachable: we
  // will never call __sanitizer_cov() for them, so counting them in
  // NumberOfInstrumentedBlocks() might complicate calculation of code coverage
  // percentage. Also, unreachable instructions frequently have no debug
  // locations.
  if (isa<UnreachableInst>(BB->getFirstNonPHIOrDbgOrLifetime())) return false;

  // Don't insert coverage into blocks without a valid insertion point
  // (catchswitch blocks).
  if (BB->getFirstInsertionPt() == BB->end()) return false;

  if (Options.NoPrune || &F.getEntryBlock() == BB) return true;

  if (Options.CoverageType == SanitizerCoverageOptions::SCK_Function &&
      &F.getEntryBlock() != BB)
    return false;

  // Do not instrument full dominators, or full post-dominators with multiple
  // predecessors.
  return !isFullDominator(BB, DT) &&
         !(isFullPostDominator(BB, PDT) && !BB->getSinglePredecessor());

}

// Returns true iff From->To is a backedge.
// A twist here is that we treat From->To as a backedge if
//   * To dominates From or
//   * To->UniqueSuccessor dominates From
bool IsBackEdge(BasicBlock *From, BasicBlock *To, const DominatorTree *DT) {

  if (DT->dominates(To, From)) return true;
  if (auto Next = To->getUniqueSuccessor())
    if (DT->dominates(Next, From)) return true;
  return false;

}

// Prunes uninteresting Cmp instrumentation:
//   * CMP instructions that feed into loop backedge branch.
//
// Note that Cmp pruning is controlled by the same flag as the
// BB pruning.
bool IsInterestingCmp(ICmpInst *CMP, const DominatorTree *DT,
                      const SanitizerCoverageOptions &Options) {

  if (!Options.NoPrune)
    if (CMP->hasOneUse())
      if (auto BR = dyn_cast<BranchInst>(CMP->user_back()))
        for (BasicBlock *B : BR->successors())
          if (IsBackEdge(BR->getParent(), B, DT)) return false;
  return true;

}

void ModuleSanitizerCoverageAFL::instrumentFunction(
    Function &F, DomTreeCallback DTCallback, PostDomTreeCallback PDTCallback) {

  if (F.empty()) return;
  if (!isInInstrumentList(&F, FMNAME)) return;

  if (F.getName().find(".module_ctor") != std::string::npos)
    return;  // Should not instrument sanitizer init functions.
  if (F.getName().startswith("__sanitizer_"))
    return;  // Don't instrument __sanitizer_* callbacks.
  // Don't touch available_externally functions, their actual body is elewhere.
  if (F.getLinkage() == GlobalValue::AvailableExternallyLinkage) return;
  // Don't instrument MSVC CRT configuration helpers. They may run before normal
  // initialization.
  if (F.getName() == "__local_stdio_printf_options" ||
      F.getName() == "__local_stdio_scanf_options")
    return;
  if (isa<UnreachableInst>(F.getEntryBlock().getTerminator())) return;
  // Don't instrument functions using SEH for now. Splitting basic blocks like
  // we do for coverage breaks WinEHPrepare.
  // FIXME: Remove this when SEH no longer uses landingpad pattern matching.
  if (F.hasPersonalityFn() &&
      isAsynchronousEHPersonality(classifyEHPersonality(F.getPersonalityFn())))
    return;
  if (Options.CoverageType >= SanitizerCoverageOptions::SCK_Edge)
    SplitAllCriticalEdges(
        F, CriticalEdgeSplittingOptions().setIgnoreUnreachableDests());
  SmallVector<Instruction *, 8>       IndirCalls;
  SmallVector<BasicBlock *, 16>       BlocksToInstrument;
  SmallVector<Instruction *, 8>       CmpTraceTargets;
  SmallVector<Instruction *, 8>       SwitchTraceTargets;
  SmallVector<BinaryOperator *, 8>    DivTraceTargets;
  SmallVector<GetElementPtrInst *, 8> GepTraceTargets;

  const DominatorTree     *DT = DTCallback(F);
  const PostDominatorTree *PDT = PDTCallback(F);
  bool                     IsLeafFunc = true;

  for (auto &BB : F) {

    if (shouldInstrumentBlock(F, &BB, DT, PDT, Options))
      BlocksToInstrument.push_back(&BB);
    for (auto &Inst : BB) {

      if (Options.IndirectCalls) {

        CallBase *CB = dyn_cast<CallBase>(&Inst);
        if (CB && !CB->getCalledFunction()) IndirCalls.push_back(&Inst);

      }

      if (Options.TraceCmp) {

        if (ICmpInst *CMP = dyn_cast<ICmpInst>(&Inst))
          if (IsInterestingCmp(CMP, DT, Options))
            CmpTraceTargets.push_back(&Inst);
        if (isa<SwitchInst>(&Inst)) SwitchTraceTargets.push_back(&Inst);

      }

      if (Options.TraceDiv)
        if (BinaryOperator *BO = dyn_cast<BinaryOperator>(&Inst))
          if (BO->getOpcode() == Instruction::SDiv ||
              BO->getOpcode() == Instruction::UDiv)
            DivTraceTargets.push_back(BO);
      if (Options.TraceGep)
        if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(&Inst))
          GepTraceTargets.push_back(GEP);
      if (Options.StackDepth)
        if (isa<InvokeInst>(Inst) ||
            (isa<CallInst>(Inst) && !isa<IntrinsicInst>(Inst)))
          IsLeafFunc = false;

    }

  }

  InjectCoverage(F, BlocksToInstrument, IsLeafFunc);
  InjectCoverageForIndirectCalls(F, IndirCalls);
  InjectTraceForCmp(F, CmpTraceTargets);
  InjectTraceForSwitch(F, SwitchTraceTargets);
  InjectTraceForDiv(F, DivTraceTargets);
  InjectTraceForGep(F, GepTraceTargets);

}

GlobalVariable *ModuleSanitizerCoverageAFL::CreateFunctionLocalArrayInSection(
    size_t NumElements, Function &F, Type *Ty, const char *Section) {

  ArrayType *ArrayTy = ArrayType::get(Ty, NumElements);
  auto       Array = new GlobalVariable(
            *CurModule, ArrayTy, false, GlobalVariable::PrivateLinkage,
            Constant::getNullValue(ArrayTy), "__sancov_gen_");

#if LLVM_VERSION_MAJOR >= 13
  if (TargetTriple.supportsCOMDAT() &&
      (TargetTriple.isOSBinFormatELF() || !F.isInterposable()))
    if (auto Comdat = getOrCreateFunctionComdat(F, TargetTriple))
      Array->setComdat(Comdat);
#else
  if (TargetTriple.supportsCOMDAT() && !F.isInterposable())
    if (auto Comdat =
            GetOrCreateFunctionComdat(F, TargetTriple, CurModuleUniqueId))
      Array->setComdat(Comdat);
#endif

  Array->setSection(getSectionName(Section));
#if (LLVM_VERSION_MAJOR >= 11) || \
    (LLVM_VERSION_MAJOR == 10 && LLVM_VERSION_MINOR >= 1)
  #if LLVM_VERSION_MAJOR >= 16
  Array->setAlignment(Align(DL->getTypeStoreSize(Ty).getFixedValue()));
  #else
  Array->setAlignment(Align(DL->getTypeStoreSize(Ty).getFixedSize()));
  #endif
#else
  Array->setAlignment(Align(4));  // cheating
#endif
  GlobalsToAppendToUsed.push_back(Array);
  GlobalsToAppendToCompilerUsed.push_back(Array);
  MDNode *MD = MDNode::get(F.getContext(), ValueAsMetadata::get(&F));
  Array->addMetadata(LLVMContext::MD_associated, *MD);

  return Array;

}

/* PATA start */
GlobalVariable *ModuleSanitizerCoverageAFL::
CreateModuleDataInSection(Function &F, Type *Ty, const char *Section) {
  auto       Data = new GlobalVariable(
            *CurModule, Ty, false, GlobalVariable::PrivateLinkage,
            Constant::getNullValue(Ty), "__sancov_pata_gen_");

#if LLVM_VERSION_MAJOR >= 13
  if (TargetTriple.supportsCOMDAT() &&
      (TargetTriple.isOSBinFormatELF() || !F.isInterposable()))
    if (auto Comdat = getOrCreateFunctionComdat(F, TargetTriple))
      Data->setComdat(Comdat);
#else
  if (TargetTriple.supportsCOMDAT() && !F.isInterposable())
    if (auto Comdat =
            GetOrCreateFunctionComdat(F, TargetTriple, CurModuleUniqueId))
      Data->setComdat(Comdat);
#endif

  Data->setSection(getSectionName(Section));
  GlobalsToAppendToUsed.push_back(Data);
  GlobalsToAppendToCompilerUsed.push_back(Data);
  MDNode *MD = MDNode::get(F.getContext(), ValueAsMetadata::get(&F));
  Data->addMetadata(LLVMContext::MD_associated, *MD);

  return Data;
}
/* PATA end */

GlobalVariable *ModuleSanitizerCoverageAFL::CreatePCArray(
    Function &F, ArrayRef<BasicBlock *> AllBlocks) {

  size_t N = AllBlocks.size();
  assert(N);
  SmallVector<Constant *, 32> PCs;
  IRBuilder<>                 IRB(&*F.getEntryBlock().getFirstInsertionPt());
  for (size_t i = 0; i < N; i++) {

    if (&F.getEntryBlock() == AllBlocks[i]) {

      PCs.push_back((Constant *)IRB.CreatePointerCast(&F, IntptrPtrTy));
      PCs.push_back((Constant *)IRB.CreateIntToPtr(
          ConstantInt::get(IntptrTy, 1), IntptrPtrTy));

    } else {

      PCs.push_back((Constant *)IRB.CreatePointerCast(
          BlockAddress::get(AllBlocks[i]), IntptrPtrTy));
      PCs.push_back((Constant *)IRB.CreateIntToPtr(
          ConstantInt::get(IntptrTy, 0), IntptrPtrTy));

    }

  }

  auto *PCArray = CreateFunctionLocalArrayInSection(N * 2, F, IntptrPtrTy,
                                                    SanCovPCsSectionName);
  PCArray->setInitializer(
      ConstantArray::get(ArrayType::get(IntptrPtrTy, N * 2), PCs));
  PCArray->setConstant(true);

  return PCArray;

}

void ModuleSanitizerCoverageAFL::CreateFunctionLocalArrays(
    Function &F, ArrayRef<BasicBlock *> AllBlocks, uint32_t special) {

  if (Options.TracePCGuard)
    FunctionGuardArray = CreateFunctionLocalArrayInSection(
        AllBlocks.size() + special, F, Int32Ty, SanCovGuardsSectionName);

  if (Options.Inline8bitCounters)
    Function8bitCounterArray = CreateFunctionLocalArrayInSection(
        AllBlocks.size(), F, Int8Ty, SanCovCountersSectionName);
  /*
    if (Options.InlineBoolFlag)
      FunctionBoolArray = CreateFunctionLocalArrayInSection(
          AllBlocks.size(), F, Int1Ty, SanCovBoolFlagSectionName);
  */
  if (Options.PCTable) FunctionPCsArray = CreatePCArray(F, AllBlocks);

}

bool ModuleSanitizerCoverageAFL::InjectCoverage(
    Function &F, ArrayRef<BasicBlock *> AllBlocks, bool IsLeafFunc) {

  uint32_t        cnt_cov = 0, cnt_sel = 0, cnt_sel_inc = 0;
  static uint32_t first = 1;

  for (auto &BB : F) {

    for (auto &IN : BB) {

      CallInst *callInst = nullptr;

      if ((callInst = dyn_cast<CallInst>(&IN))) {

        Function *Callee = callInst->getCalledFunction();
        if (!Callee) continue;
        if (callInst->getCallingConv() != llvm::CallingConv::C) continue;
        StringRef FuncName = Callee->getName();
        if (!FuncName.compare(StringRef("dlopen")) ||
            !FuncName.compare(StringRef("_dlopen"))) {

          fprintf(stderr,
                  "WARNING: dlopen() detected. To have coverage for a library "
                  "that your target dlopen()'s this must either happen before "
                  "__AFL_INIT() or you must use AFL_PRELOAD to preload all "
                  "dlopen()'ed libraries!\n");
          continue;

        }

        if (!FuncName.compare(StringRef("__afl_coverage_interesting"))) {

          cnt_cov++;

        }

      }

      SelectInst *selectInst = nullptr;

      if ((selectInst = dyn_cast<SelectInst>(&IN))) {

        Value *c = selectInst->getCondition();
        auto   t = c->getType();
        if (t->getTypeID() == llvm::Type::IntegerTyID) {

          cnt_sel++;
          cnt_sel_inc += 2;

        }

#if (LLVM_VERSION_MAJOR >= 12)
        else if (t->getTypeID() == llvm::Type::FixedVectorTyID) {

          FixedVectorType *tt = dyn_cast<FixedVectorType>(t);
          if (tt) {

            cnt_sel++;
            cnt_sel_inc += (tt->getElementCount().getKnownMinValue() * 2);

          }

        }

#endif

      }

    }

  }

  /* Create PCGUARD array */
  CreateFunctionLocalArrays(F, AllBlocks, first + cnt_cov + cnt_sel_inc);
  if (first) { first = 0; }
  selects += cnt_sel;

  uint32_t special = 0, local_selects = 0, skip_next = 0;

  for (auto &BB : F) {

    for (auto &IN : BB) {

      CallInst *callInst = nullptr;

      /*
                                std::string errMsg;
                                raw_string_ostream os(errMsg);
                            IN.print(os);
                            fprintf(stderr, "X: %s\n", os.str().c_str());
      */
      if ((callInst = dyn_cast<CallInst>(&IN))) {

        Function *Callee = callInst->getCalledFunction();
        if (!Callee) continue;
        if (callInst->getCallingConv() != llvm::CallingConv::C) continue;
        StringRef FuncName = Callee->getName();
        if (FuncName.compare(StringRef("__afl_coverage_interesting"))) continue;

        IRBuilder<> IRB(callInst);

        if (!FunctionGuardArray) {

          fprintf(stderr,
                  "SANCOV: FunctionGuardArray is NULL, failed to emit "
                  "instrumentation.");
          continue;

        }

        Value *GuardPtr = IRB.CreateIntToPtr(
            IRB.CreateAdd(
                IRB.CreatePointerCast(FunctionGuardArray, IntptrTy),
                ConstantInt::get(IntptrTy, (++special + AllBlocks.size()) * 4)),
            Int32PtrTy);

        LoadInst *Idx = IRB.CreateLoad(IRB.getInt32Ty(), GuardPtr);
        ModuleSanitizerCoverageAFL::SetNoSanitizeMetadata(Idx);

        callInst->setOperand(1, Idx);

      }

      SelectInst *selectInst = nullptr;

      if (!skip_next && (selectInst = dyn_cast<SelectInst>(&IN))) {

        uint32_t    vector_cnt = 0;
        Value      *condition = selectInst->getCondition();
        Value      *result;
        auto        t = condition->getType();
        IRBuilder<> IRB(selectInst->getNextNode());

        if (t->getTypeID() == llvm::Type::IntegerTyID) {

          if (!FunctionGuardArray) {

            fprintf(stderr,
                    "SANCOV: FunctionGuardArray is NULL, failed to emit "
                    "instrumentation.");
            continue;

          }

          auto GuardPtr1 = IRB.CreateIntToPtr(
              IRB.CreateAdd(
                  IRB.CreatePointerCast(FunctionGuardArray, IntptrTy),
                  ConstantInt::get(
                      IntptrTy,
                      (cnt_cov + ++local_selects + AllBlocks.size()) * 4)),
              Int32PtrTy);

          auto GuardPtr2 = IRB.CreateIntToPtr(
              IRB.CreateAdd(
                  IRB.CreatePointerCast(FunctionGuardArray, IntptrTy),
                  ConstantInt::get(
                      IntptrTy,
                      (cnt_cov + ++local_selects + AllBlocks.size()) * 4)),
              Int32PtrTy);

          result = IRB.CreateSelect(condition, GuardPtr1, GuardPtr2);

        } else

#if LLVM_VERSION_MAJOR >= 14
            if (t->getTypeID() == llvm::Type::FixedVectorTyID) {

          FixedVectorType *tt = dyn_cast<FixedVectorType>(t);
          if (tt) {

            uint32_t elements = tt->getElementCount().getFixedValue();
            vector_cnt = elements;
            if (elements) {

              FixedVectorType *GuardPtr1 =
                  FixedVectorType::get(Int32PtrTy, elements);
              FixedVectorType *GuardPtr2 =
                  FixedVectorType::get(Int32PtrTy, elements);
              Value *x, *y;

              if (!FunctionGuardArray) {

                fprintf(stderr,
                        "SANCOV: FunctionGuardArray is NULL, failed to emit "
                        "instrumentation.");
                continue;

              }

              Value *val1 = IRB.CreateIntToPtr(
                  IRB.CreateAdd(
                      IRB.CreatePointerCast(FunctionGuardArray, IntptrTy),
                      ConstantInt::get(
                          IntptrTy,
                          (cnt_cov + ++local_selects + AllBlocks.size()) * 4)),
                  Int32PtrTy);
              x = IRB.CreateInsertElement(GuardPtr1, val1, (uint64_t)0);

              Value *val2 = IRB.CreateIntToPtr(
                  IRB.CreateAdd(
                      IRB.CreatePointerCast(FunctionGuardArray, IntptrTy),
                      ConstantInt::get(
                          IntptrTy,
                          (cnt_cov + ++local_selects + AllBlocks.size()) * 4)),
                  Int32PtrTy);
              y = IRB.CreateInsertElement(GuardPtr2, val2, (uint64_t)0);

              for (uint64_t i = 1; i < elements; i++) {

                val1 = IRB.CreateIntToPtr(
                    IRB.CreateAdd(
                        IRB.CreatePointerCast(FunctionGuardArray, IntptrTy),
                        ConstantInt::get(IntptrTy, (cnt_cov + ++local_selects +
                                                    AllBlocks.size()) *
                                                       4)),
                    Int32PtrTy);
                x = IRB.CreateInsertElement(x, val1, i);

                val2 = IRB.CreateIntToPtr(
                    IRB.CreateAdd(
                        IRB.CreatePointerCast(FunctionGuardArray, IntptrTy),
                        ConstantInt::get(IntptrTy, (cnt_cov + ++local_selects +
                                                    AllBlocks.size()) *
                                                       4)),
                    Int32PtrTy);
                y = IRB.CreateInsertElement(y, val2, i);

              }

              /*
                          std::string errMsg;
                          raw_string_ostream os(errMsg);
                      x->print(os);
                      fprintf(stderr, "X: %s\n", os.str().c_str());
              */
              result = IRB.CreateSelect(condition, x, y);

            }

          }

        } else

#endif
        {

          unhandled++;
          continue;

        }

        uint32_t vector_cur = 0;

        /* Load SHM pointer */

        LoadInst *MapPtr =
            IRB.CreateLoad(PointerType::get(Int8Ty, 0), AFLMapPtr);
        ModuleSanitizerCoverageAFL::SetNoSanitizeMetadata(MapPtr);

        /*
                    std::string errMsg;
                    raw_string_ostream os(errMsg);
                    result->print(os);
                    fprintf(stderr, "X: %s\n", os.str().c_str());
        */

        while (1) {

          /* Get CurLoc */
          LoadInst *CurLoc = nullptr;
          Value    *MapPtrIdx = nullptr;

          /* Load counter for CurLoc */
          if (!vector_cnt) {

            CurLoc = IRB.CreateLoad(IRB.getInt32Ty(), result);
            ModuleSanitizerCoverageAFL::SetNoSanitizeMetadata(CurLoc);
            MapPtrIdx = IRB.CreateGEP(Int8Ty, MapPtr, CurLoc);

          } else {

            auto element = IRB.CreateExtractElement(result, vector_cur++);
            auto elementptr = IRB.CreateIntToPtr(element, Int32PtrTy);
            auto elementld = IRB.CreateLoad(IRB.getInt32Ty(), elementptr);
            ModuleSanitizerCoverageAFL::SetNoSanitizeMetadata(elementld);
            MapPtrIdx = IRB.CreateGEP(Int8Ty, MapPtr, elementld);

          }

          if (use_threadsafe_counters) {

            IRB.CreateAtomicRMW(llvm::AtomicRMWInst::BinOp::Add, MapPtrIdx, One,
#if LLVM_VERSION_MAJOR >= 13
                                llvm::MaybeAlign(1),
#endif
                                llvm::AtomicOrdering::Monotonic);

          } else {

            LoadInst *Counter = IRB.CreateLoad(IRB.getInt8Ty(), MapPtrIdx);
            ModuleSanitizerCoverageAFL::SetNoSanitizeMetadata(Counter);

            /* Update bitmap */

            Value *Incr = IRB.CreateAdd(Counter, One);

            if (skip_nozero == NULL) {

              auto cf = IRB.CreateICmpEQ(Incr, Zero);
              auto carry = IRB.CreateZExt(cf, Int8Ty);
              Incr = IRB.CreateAdd(Incr, carry);

            }

            StoreInst *StoreCtx = IRB.CreateStore(Incr, MapPtrIdx);
            ModuleSanitizerCoverageAFL::SetNoSanitizeMetadata(StoreCtx);

          }

          if (!vector_cnt) {

            vector_cnt = 2;
            break;

          } else if (vector_cnt == vector_cur) {

            break;

          }

        }

        skip_next = 1;
        instr += vector_cnt;

      } else {

        skip_next = 0;

      }

    }

  }

  if (AllBlocks.empty() && !special && !local_selects) return false;

  if (!AllBlocks.empty())
    for (size_t i = 0, N = AllBlocks.size(); i < N; i++)
      InjectCoverageAtBlock(F, *AllBlocks[i], i, IsLeafFunc);

  return true;

}

// On every indirect call we call a run-time function
// __sanitizer_cov_indir_call* with two parameters:
//   - callee address,
//   - global cache array that contains CacheSize pointers (zero-initialized).
//     The cache is used to speed up recording the caller-callee pairs.
// The address of the caller is passed implicitly via caller PC.
// CacheSize is encoded in the name of the run-time function.
void ModuleSanitizerCoverageAFL::InjectCoverageForIndirectCalls(
    Function &F, ArrayRef<Instruction *> IndirCalls) {

  if (IndirCalls.empty()) return;
  for (auto I : IndirCalls) {

    IRBuilder<> IRB(I);
    CallBase   &CB = cast<CallBase>(*I);
    Value      *Callee = CB.getCalledOperand();
    if (isa<InlineAsm>(Callee)) continue;
    IRB.CreateCall(SanCovTracePCIndir, IRB.CreatePointerCast(Callee, IntptrTy));

  }

}

// For every switch statement we insert a call:
// __sanitizer_cov_trace_switch(CondValue,
//      {NumCases, ValueSizeInBits, Case0Value, Case1Value, Case2Value, ... })

void ModuleSanitizerCoverageAFL::InjectTraceForSwitch(
    Function &, ArrayRef<Instruction *> SwitchTraceTargets) {

  for (auto I : SwitchTraceTargets) {

    if (SwitchInst *SI = dyn_cast<SwitchInst>(I)) {

      IRBuilder<>                 IRB(I);
      SmallVector<Constant *, 16> Initializers;
      Value                      *Cond = SI->getCondition();
      if (Cond->getType()->getScalarSizeInBits() >
          Int64Ty->getScalarSizeInBits())
        continue;
      Initializers.push_back(ConstantInt::get(Int64Ty, SI->getNumCases()));
      Initializers.push_back(
          ConstantInt::get(Int64Ty, Cond->getType()->getScalarSizeInBits()));
      if (Cond->getType()->getScalarSizeInBits() <
          Int64Ty->getScalarSizeInBits())
        Cond = IRB.CreateIntCast(Cond, Int64Ty, false);
      for (auto It : SI->cases()) {

        Constant *C = It.getCaseValue();
        if (C->getType()->getScalarSizeInBits() <
            Int64Ty->getScalarSizeInBits())
          C = ConstantExpr::getCast(CastInst::ZExt, It.getCaseValue(), Int64Ty);
        Initializers.push_back(C);

      }

      llvm::sort(drop_begin(Initializers, 2),
                 [](const Constant *A, const Constant *B) {

                   return cast<ConstantInt>(A)->getLimitedValue() <
                          cast<ConstantInt>(B)->getLimitedValue();

                 });

      ArrayType *ArrayOfInt64Ty = ArrayType::get(Int64Ty, Initializers.size());
      GlobalVariable *GV = new GlobalVariable(
          *CurModule, ArrayOfInt64Ty, false, GlobalVariable::InternalLinkage,
          ConstantArray::get(ArrayOfInt64Ty, Initializers),
          "__sancov_gen_cov_switch_values");
      IRB.CreateCall(SanCovTraceSwitchFunction,
                     {Cond, IRB.CreatePointerCast(GV, Int64PtrTy)});

    }

  }

}

void ModuleSanitizerCoverageAFL::InjectTraceForDiv(
    Function &, ArrayRef<BinaryOperator *> DivTraceTargets) {

  for (auto BO : DivTraceTargets) {

    IRBuilder<> IRB(BO);
    Value      *A1 = BO->getOperand(1);
    if (isa<ConstantInt>(A1)) continue;
    if (!A1->getType()->isIntegerTy()) continue;
    uint64_t TypeSize = DL->getTypeStoreSizeInBits(A1->getType());
    int      CallbackIdx = TypeSize == 32 ? 0 : TypeSize == 64 ? 1 : -1;
    if (CallbackIdx < 0) continue;
    auto Ty = Type::getIntNTy(*C, TypeSize);
    IRB.CreateCall(SanCovTraceDivFunction[CallbackIdx],
                   {IRB.CreateIntCast(A1, Ty, true)});

  }

}

void ModuleSanitizerCoverageAFL::InjectTraceForGep(
    Function &, ArrayRef<GetElementPtrInst *> GepTraceTargets) {

  for (auto GEP : GepTraceTargets) {

    IRBuilder<> IRB(GEP);
    for (Use &Idx : GEP->indices())
      if (!isa<ConstantInt>(Idx) && Idx->getType()->isIntegerTy())
        IRB.CreateCall(SanCovTraceGepFunction,
                       {IRB.CreateIntCast(Idx, IntptrTy, true)});

  }

}

void ModuleSanitizerCoverageAFL::InjectTraceForCmp(
    Function &, ArrayRef<Instruction *> CmpTraceTargets) {

  for (auto I : CmpTraceTargets) {

    if (ICmpInst *ICMP = dyn_cast<ICmpInst>(I)) {

      IRBuilder<> IRB(ICMP);
      Value      *A0 = ICMP->getOperand(0);
      Value      *A1 = ICMP->getOperand(1);
      if (!A0->getType()->isIntegerTy()) continue;
      uint64_t TypeSize = DL->getTypeStoreSizeInBits(A0->getType());
      int      CallbackIdx = TypeSize == 8    ? 0
                             : TypeSize == 16 ? 1
                             : TypeSize == 32 ? 2
                             : TypeSize == 64 ? 3
                                              : -1;
      if (CallbackIdx < 0) continue;
      // __sanitizer_cov_trace_cmp((type_size << 32) | predicate, A0, A1);
      auto CallbackFunc = SanCovTraceCmpFunction[CallbackIdx];
      bool FirstIsConst = isa<ConstantInt>(A0);
      bool SecondIsConst = isa<ConstantInt>(A1);
      // If both are const, then we don't need such a comparison.
      if (FirstIsConst && SecondIsConst) continue;
      // If only one is const, then make it the first callback argument.
      if (FirstIsConst || SecondIsConst) {

        CallbackFunc = SanCovTraceConstCmpFunction[CallbackIdx];
        if (SecondIsConst) std::swap(A0, A1);

      }

      auto Ty = Type::getIntNTy(*C, TypeSize);
      IRB.CreateCall(CallbackFunc, {IRB.CreateIntCast(A0, Ty, true),
                                    IRB.CreateIntCast(A1, Ty, true)});

    }

  }

}

void ModuleSanitizerCoverageAFL::InjectCoverageAtBlock(Function   &F,
                                                       BasicBlock &BB,
                                                       size_t      Idx,
                                                       bool        IsLeafFunc) {

  BasicBlock::iterator IP = BB.getFirstInsertionPt();
  bool                 IsEntryBB = &BB == &F.getEntryBlock();

  if (IsEntryBB) {

    // Keep allocas and llvm.localescape calls in the entry block.  Even
    // if we aren't splitting the block, it's nice for allocas to be before
    // calls.
    IP = PrepareToSplitEntryBlock(BB, IP);

  }

  IRBuilder<> IRB(&*IP);

  if (Options.TracePC) {

    IRB.CreateCall(SanCovTracePC);
    //        ->setCannotMerge();  // gets the PC using GET_CALLER_PC.

  }

  if (Options.TracePCGuard) {

    /* Get CurLoc */

    Value *GuardPtr = IRB.CreateIntToPtr(
        IRB.CreateAdd(IRB.CreatePointerCast(FunctionGuardArray, IntptrTy),
                      ConstantInt::get(IntptrTy, Idx * 4)),
        Int32PtrTy);

    LoadInst *CurLoc = IRB.CreateLoad(IRB.getInt32Ty(), GuardPtr);
    ModuleSanitizerCoverageAFL::SetNoSanitizeMetadata(CurLoc);

    /* Load SHM pointer */

    LoadInst *MapPtr = IRB.CreateLoad(PointerType::get(Int8Ty, 0), AFLMapPtr);
    ModuleSanitizerCoverageAFL::SetNoSanitizeMetadata(MapPtr);

    /* Load counter for CurLoc */

    Value *MapPtrIdx = IRB.CreateGEP(Int8Ty, MapPtr, CurLoc);

    if (use_threadsafe_counters) {

      IRB.CreateAtomicRMW(llvm::AtomicRMWInst::BinOp::Add, MapPtrIdx, One,
#if LLVM_VERSION_MAJOR >= 13
                          llvm::MaybeAlign(1),
#endif
                          llvm::AtomicOrdering::Monotonic);

    } else {

      LoadInst *Counter = IRB.CreateLoad(IRB.getInt8Ty(), MapPtrIdx);
      ModuleSanitizerCoverageAFL::SetNoSanitizeMetadata(Counter);

      /* Update bitmap */

      Value *Incr = IRB.CreateAdd(Counter, One);

      if (skip_nozero == NULL) {

        auto cf = IRB.CreateICmpEQ(Incr, Zero);
        auto carry = IRB.CreateZExt(cf, Int8Ty);
        Incr = IRB.CreateAdd(Incr, carry);

      }

      StoreInst *StoreCtx = IRB.CreateStore(Incr, MapPtrIdx);
      ModuleSanitizerCoverageAFL::SetNoSanitizeMetadata(StoreCtx);

    }

    // done :)

    //    IRB.CreateCall(SanCovTracePCGuard, Offset)->setCannotMerge();
    //    IRB.CreateCall(SanCovTracePCGuard, GuardPtr)->setCannotMerge();
    ++instr;

    /* PATA start */
    if (patalog_mode) {
      block_to_id[&BB] = ConstantExpr::getIntToPtr(ConstantExpr::getAdd(
          ConstantExpr::getPointerCast(FunctionGuardArray, IntptrTy),
          ConstantInt::get(IntptrTy, Idx * 4)), Int32PtrTy);
    }
    /* PATA end */

  }

  if (Options.Inline8bitCounters) {

    auto CounterPtr = IRB.CreateGEP(
        Function8bitCounterArray->getValueType(), Function8bitCounterArray,
        {ConstantInt::get(IntptrTy, 0), ConstantInt::get(IntptrTy, Idx)});
    auto Load = IRB.CreateLoad(Int8Ty, CounterPtr);
    auto Inc = IRB.CreateAdd(Load, ConstantInt::get(Int8Ty, 1));
    auto Store = IRB.CreateStore(Inc, CounterPtr);
    SetNoSanitizeMetadata(Load);
    SetNoSanitizeMetadata(Store);

  }

  /*
    if (Options.InlineBoolFlag) {

      auto FlagPtr = IRB.CreateGEP(
          FunctionBoolArray->getValueType(), FunctionBoolArray,
          {ConstantInt::get(IntptrTy, 0), ConstantInt::get(IntptrTy, Idx)});
      auto Load = IRB.CreateLoad(Int1Ty, FlagPtr);
      auto ThenTerm =
          SplitBlockAndInsertIfThen(IRB.CreateIsNull(Load), &*IP, false);
      IRBuilder<> ThenIRB(ThenTerm);
      auto Store = ThenIRB.CreateStore(ConstantInt::getTrue(Int1Ty), FlagPtr);
      SetNoSanitizeMetadata(Load);
      SetNoSanitizeMetadata(Store);

    }

  */

  if (Options.StackDepth && IsEntryBB && !IsLeafFunc) {

    // Check stack depth.  If it's the deepest so far, record it.
    Module   *M = F.getParent();
    Function *GetFrameAddr = Intrinsic::getDeclaration(
        M, Intrinsic::frameaddress,
        IRB.getInt8PtrTy(M->getDataLayout().getAllocaAddrSpace()));
    auto FrameAddrPtr =
        IRB.CreateCall(GetFrameAddr, {Constant::getNullValue(Int32Ty)});
    auto        FrameAddrInt = IRB.CreatePtrToInt(FrameAddrPtr, IntptrTy);
    auto        LowestStack = IRB.CreateLoad(IntptrTy, SanCovLowestStack);
    auto        IsStackLower = IRB.CreateICmpULT(FrameAddrInt, LowestStack);
    auto        ThenTerm = SplitBlockAndInsertIfThen(IsStackLower, &*IP, false);
    IRBuilder<> ThenIRB(ThenTerm);
    auto        Store = ThenIRB.CreateStore(FrameAddrInt, SanCovLowestStack);
    SetNoSanitizeMetadata(LowestStack);
    SetNoSanitizeMetadata(Store);

  }

}

/* PATA start */
void ModuleSanitizerCoverageAFL::InjectCoverageForPata(Function   &F,
                                                       BasicBlock &BB) {

  BasicBlock::iterator IP = BB.getFirstInsertionPt();
  bool                 IsEntryBB = &BB == &F.getEntryBlock();

  if (IsEntryBB) {

    // Keep allocas and llvm.localescape calls in the entry block.  Even
    // if we aren't splitting the block, it's nice for allocas to be before
    // calls.
    IP = PrepareToSplitEntryBlock(BB, IP);

  }

  IRBuilder<> IRB(&*IP);

  if (Options.TracePC) {

    IRB.CreateCall(SanCovTracePC);
    //        ->setCannotMerge();  // gets the PC using GET_CALLER_PC.

  }

  if (Options.TracePCGuard) {

    /* Get CurLoc */

    PataTmpGuardArray = CreateFunctionLocalArrayInSection(
        1, F, Int32Ty, SanCovGuardsSectionName);

    Value *GuardPtr = IRB.CreateIntToPtr(
        IRB.CreateAdd(IRB.CreatePointerCast(PataTmpGuardArray, IntptrTy),
                      ConstantInt::get(IntptrTy, 0)),
        Int32PtrTy);

    LoadInst *CurLoc = IRB.CreateLoad(IRB.getInt32Ty(), GuardPtr);
    ModuleSanitizerCoverageAFL::SetNoSanitizeMetadata(CurLoc);

    /* Load SHM pointer */

    LoadInst *MapPtr = IRB.CreateLoad(PointerType::get(Int8Ty, 0), AFLMapPtr);
    ModuleSanitizerCoverageAFL::SetNoSanitizeMetadata(MapPtr);

    /* Load counter for CurLoc */

    Value *MapPtrIdx = IRB.CreateGEP(Int8Ty, MapPtr, CurLoc);

    if (use_threadsafe_counters) {

      IRB.CreateAtomicRMW(llvm::AtomicRMWInst::BinOp::Add, MapPtrIdx, One,
#if LLVM_VERSION_MAJOR >= 13
                          llvm::MaybeAlign(1),
#endif
                          llvm::AtomicOrdering::Monotonic);

    } else {

      LoadInst *Counter = IRB.CreateLoad(IRB.getInt8Ty(), MapPtrIdx);
      ModuleSanitizerCoverageAFL::SetNoSanitizeMetadata(Counter);

      /* Update bitmap */

      Value *Incr = IRB.CreateAdd(Counter, One);

      if (skip_nozero == NULL) {

        auto cf = IRB.CreateICmpEQ(Incr, Zero);
        auto carry = IRB.CreateZExt(cf, Int8Ty);
        Incr = IRB.CreateAdd(Incr, carry);

      }

      StoreInst *StoreCtx = IRB.CreateStore(Incr, MapPtrIdx);
      ModuleSanitizerCoverageAFL::SetNoSanitizeMetadata(StoreCtx);

    }

    // done :)
    block_to_id[&BB] = ConstantExpr::getIntToPtr(
        ConstantExpr::getAdd(
            ConstantExpr::getPointerCast(PataTmpGuardArray, IntptrTy),
            ConstantInt::get(IntptrTy, 0)),
        Int32PtrTy);
    

    //    IRB.CreateCall(SanCovTracePCGuard, Offset)->setCannotMerge();
    //    IRB.CreateCall(SanCovTracePCGuard, GuardPtr)->setCannotMerge();
    ++instr;

  }
}
/* PATA end */

std::string ModuleSanitizerCoverageAFL::getSectionName(
    const std::string &Section) const {

  if (TargetTriple.isOSBinFormatCOFF()) {

    if (Section == SanCovCountersSectionName) return ".SCOV$CM";
    if (Section == SanCovBoolFlagSectionName) return ".SCOV$BM";
    if (Section == SanCovPCsSectionName) return ".SCOVP$M";
    return ".SCOV$GM";  // For SanCovGuardsSectionName.

  }

  if (TargetTriple.isOSBinFormatMachO()) return "__DATA,__" + Section;
  return "__" + Section;

}

std::string ModuleSanitizerCoverageAFL::getSectionStart(
    const std::string &Section) const {

  if (TargetTriple.isOSBinFormatMachO())
    return "\1section$start$__DATA$__" + Section;
  return "__start___" + Section;

}

std::string ModuleSanitizerCoverageAFL::getSectionEnd(
    const std::string &Section) const {

  if (TargetTriple.isOSBinFormatMachO())
    return "\1section$end$__DATA$__" + Section;
  return "__stop___" + Section;

}

