-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixLoop
import TrustIr.Proofs.GenericCoroPrefixGraph
import TrustIr.Proofs.GenericCoroPrefixInference

namespace TrustIr.GenericCoro.Prefix

/-- The selected source block executes its actual resolved prefix before the
    held-value intrinsic. The callback, prefix and every failure stay opaque. -/
theorem evalLayer_sourceEntry_eq (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (pc : BlockId) (params : List (ValueId × Ty)) (args : List Value)
    (bodyPrefix : List Inst) (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int) (strategy : PanicStrategy)
    (entry : cfg pc = some {
      params := params
      body := bodyPrefix
      bodyResultDests := bodyDests
      terminator := .CoroSuspend frame slot next value
      terminatorResultDests := termDests }) :
    evalLayer recurse ctx depth cfg pc args strategy = (do
      let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx (params.map (·.snd)) args)
      bindBlockParamsChecked params args
      evalBody recurse ctx depth strategy
        (bodyInstsWithResultDests (bodyPrefix.map ctx.resolveDrop) bodyDests)
      let values ← suspendValues ctx.byteModel frame value slot next
      checkedReturn ctx values) := by
  cases strategy <;>
    simp only [evalLayer, entry, EvalContext.resolveBlock, EvalContext.resolveDrop,
      stepTermWithContext, closureTermWithContext, stepTermUnwind, stepInst,
      semCoroSuspend, semReturn, suspendValues, checkedReturn, List.mapM, List.mapM.loop,
      List.reverse_nil, List.reverse_cons, List.nil_append, List.append_nil,
      pure_bind, bind_pure, bind_assoc] <;> rfl

private theorem expandedEntry_resolvedRows (ctx : EvalContext) (names : Names)
    (bodyPrefix : List Inst) (bodyDests : List (List ValueId))
    (frame : ValueId) (slot : Nat) (next : Int) :
    bodyInstsWithResultDests
      ((bodyPrefix ++ [Inst.Const .I64 (.int slot), Inst.GEP .I64 frame [names.index] false,
        Inst.Const .I64 (.int next), Inst.Store .I64 names.pointer names.state false none]).map ctx.resolveDrop)
      ((bodyInstsWithResultDests bodyPrefix bodyDests).map Prod.snd ++
        [[names.index], [names.pointer], [names.state], []]) =
      bodyInstsWithResultDests (bodyPrefix.map ctx.resolveDrop) bodyDests ++
        [(.Const .I64 (.int slot), [names.index]),
         (.GEP .I64 frame [names.index] false, [names.pointer]),
         (.Const .I64 (.int next), [names.state]),
         (.Store .I64 names.pointer names.state false none, [])] := by
  rw [bodyInsts_resolve, bodyInsts_normalized_append, List.map_append,
    ← bodyInsts_resolve]
  rfl

/-- Exact normalization of the target's selected entry. Its three generated
    result types are the actual inferred associations. No prefix, parameter,
    address, store, return, callback or resource success is assumed. -/
theorem evalLayer_targetEntry_eq (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (pc : BlockId) (names : Names)
    (params : List (ValueId × Ty)) (args : List Value)
    (bodyPrefix : List Inst) (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int) (strategy : PanicStrategy)
    (table : LocalTypeTable) (types : ctx.localTypes = some table)
    (indexType : table names.index = some .I64) (pointerType : table names.pointer = some .Ptr)
    (stateType : table names.state = some .I64)
    (entry : cfg pc = some (expandedEntry names {
      params := params
      body := bodyPrefix
      bodyResultDests := bodyDests
      terminator := .CoroSuspend frame slot next value
      terminatorResultDests := termDests })) :
    evalLayer recurse ctx depth cfg pc args strategy = (do
      let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx (params.map (·.snd)) args)
      bindBlockParamsChecked params args
      evalBody recurse ctx depth strategy
        (bodyInstsWithResultDests (bodyPrefix.map ctx.resolveDrop) bodyDests)
      let values ← expandedValues ctx names frame value slot next
      checkedReturn ctx values) := by
  trustIrCompilerProof {
    have slotBind (result : ValueId) := bindInstructionResults_single_nonChar
      ctx (.Const .I64 (.int slot)) names.index result .I64
        (instructionResultTypes_declared ctx table _ _ _ types indexType rfl) (by intro h; cases h)
    have pointerBind (result : ValueId) := bindInstructionResults_single_nonChar
      ctx (.GEP .I64 frame [names.index] false) names.pointer result .Ptr
        (instructionResultTypes_declared ctx table _ _ _ types pointerType rfl) (by intro h; cases h)
    have stateBind (result : ValueId) := bindInstructionResults_single_nonChar
      ctx (.Const .I64 (.int next)) names.state result .I64
        (instructionResultTypes_declared ctx table _ _ _ types stateType rfl) (by intro h; cases h)
    simp only [evalLayer, entry, expandedEntry, EvalContext.resolveBlock]
    rw [expandedEntry_resolvedRows, evalBody_append]
    cases strategy <;>
      simp only [EvalContext.resolveDrop, evalBody_cons, evalBody_nil, evalBodyStep,
        stepTermWithContext, closureTermWithContext, stepTermUnwind, stepInstWithContext,
        stepInst, semStoreUsing,
        EvalContext.semGEPUsing_canonical, EvalContext.memoryServiceFor, Ty.hasCanonicalMemoryLayout,
        encodeMemoryWithFunctions_i64,
        slotBind, pointerBind, stateBind, bindInstructionResults_store,
        Constant.hasSymbolAddr, constValueAtChecked_i64, constWidthAmbiguous,
        constHasInexactFloat, constPointerFormsSupported, Ty.isInteger,
        Bool.not_true, Bool.false_eq_true, if_false,
        semReturn, expandedValues, checkedReturn, publishFresh, List.mapM, List.mapM.loop,
        List.reverse_nil, List.reverse_cons, List.nil_append, List.append_nil,
        pure_bind, bind_pure, bind_assoc] <;> rfl
  } {
    have slotBind (result : ValueId) := bindInstructionResults_single_nonChar
      ctx (.Const .I64 (.int slot)) names.index result .I64
        (instructionResultTypes_declared ctx table _ _ _ types indexType rfl) (by intro h; cases h)
    have pointerBind (result : ValueId) := bindInstructionResults_single_nonChar
      ctx (.GEP .I64 frame [names.index] false) names.pointer result .Ptr
        (instructionResultTypes_declared ctx table _ _ _ types pointerType rfl) (by intro h; cases h)
    have stateBind (result : ValueId) := bindInstructionResults_single_nonChar
      ctx (.Const .I64 (.int next)) names.state result .I64
        (instructionResultTypes_declared ctx table _ _ _ types stateType rfl) (by intro h; cases h)
    simp only [evalLayer, entry, expandedEntry, EvalContext.resolveBlock]
    rw [expandedEntry_resolvedRows, evalBody_append]
    cases strategy <;>
      simp only [EvalContext.resolveDrop, evalBody_cons, evalBody_nil, evalBodyStep,
        stepTermWithContext, closureTermWithContext, stepTermUnwind, stepInstWithContext,
        stepInst, semStoreUsing,
        EvalContext.semGEPUsing_canonical, EvalContext.memoryServiceFor, Ty.hasCanonicalMemoryLayout,
        encodeMemoryWithFunctions_i64,
        slotBind, pointerBind, stateBind, bindInstructionResults_store,
        Constant.hasSymbolAddr, constValueAtChecked_i64, constWidthAmbiguous,
        constHasInexactFloat, constPointerFormsSupported, Ty.isInteger,
        Bool.not_true, Bool.false_eq_true, if_false, if_true,
        semReturn, expandedValues, checkedReturn, publishFresh, List.mapM, List.mapM.loop,
        List.reverse_nil, List.reverse_cons, List.nil_append, List.append_nil,
        pure_bind, bind_pure, bind_assoc] <;> rfl
  }

end TrustIr.GenericCoro.Prefix
