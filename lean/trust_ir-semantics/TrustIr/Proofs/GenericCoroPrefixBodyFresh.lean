-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixFresh
import TrustIr.Proofs.GenericCoroPrefixIndirect
import TrustIr.Proofs.GenericCoroPrefixBody
import TrustIr.Proofs.GenericCoroPrefixSeqMapFresh
import TrustIr.Proofs.SSAFreshLoops
import TrustIr.Proofs.SSAFreshContext

namespace TrustIr.GenericCoro.Prefix
open SSAFreshFrames SSAFreshStep SSAFreshInstructions SSAFreshDispatch

private theorem lookupDirectCallee_fresh (ctx : EvalContext) (id : FuncId)
    (declaredMessage missingMessage : String) :
    KeepsFresh (ctx.lookupDirectCallee id declaredMessage missingMessage) := by
  cases found : ctx.functions id with
  | some callee =>
    simp only [EvalContext.lookupDirectCallee, found]
    exact pure_fresh _
  | none =>
    cases declared : ctx.declared id <;>
      simp only [EvalContext.lookupDirectCallee, found, declared, Bool.false_eq_true, ↓reduceIte] <;>
      first | exact throwUnsupported_fresh _ _ | exact throwTypeError_fresh _

private theorem requireUntypedAbi_fresh (abi : Option SignatureAbi) :
    KeepsFresh (requireUntypedAbi abi) := by
  cases abi with
  | none => exact pure_fresh _
  | some descriptor => exact throwUnsupported_fresh _ _

private theorem directCallHeader_fresh (body : FuncBody) (args : List Value) :
    KeepsFresh (directCallHeader body args) := by
  unfold directCallHeader
  apply bind_fresh _ _ (requireUntypedAbi_fresh body.abi)
  intro unit
  cases unit
  cases arity : checkCallArity args body.paramTys with
  | error message =>
    simp only [arity]
    exact throwTypeError_fresh _
  | ok unit =>
    cases unit
    simp only [arity]
    change KeepsFresh (Sem.rejectPoisonValues args "Call arguments")
    cases poisoned : args.any Value.isPoison <;>
      simp only [Sem.rejectPoisonValues, poisoned, Bool.false_eq_true, ↓reduceIte] <;>
      first | exact pure_fresh _ | exact throwUB_fresh _

/-- Exactly the arity and poison checks in the operational direct-call
return tail; it does not invoke a generalized closure validator. -/
private def directFrameReturnCheck (returnTys : List Ty) (values : List Value) : Sem Unit := do
  match checkReturnArity values returnTys with
  | .ok () => pure ()
  | .error message => Sem.throwTypeError ("Call: " ++ message)
  Sem.rejectPoisonValues values "Call returns"

private theorem callFrame_directReturnCheck (returnTys : List Ty) (callee : Sem (List Value)) :
    callFrame returnTys callee = callFrameWith (directFrameReturnCheck returnTys) callee := by
  simp only [callFrame, finishCall, callFrameWith, finishCalleeWith,
    directFrameReturnCheck, bind_assoc, pure_bind, bind_match_unit]
  apply bind_same
  intro caller
  apply bind_same
  intro unit
  apply bind_same
  intro values
  cases arity : checkReturnArity values returnTys with
  | error message => simp only [arity, bind_assoc]
  | ok unit => cases unit; simp only [arity, pure_bind]

private theorem directCallFrame_fresh (returnTys : List Ty) (callee : Sem (List Value)) :
    KeepsFresh (callFrame returnTys callee) := by
  rw [callFrame_directReturnCheck]
  exact callFrameWith_fresh _ _

/-- Calls preserve a fresh caller even when the abstract recursive callback
    has arbitrary state effects. The saved frame supplies the invariant. -/
theorem bodyCall_fresh (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (id : FuncId) (args dests : List ValueId) :
    KeepsFresh (bodyCall recurse ctx depth strat id args dests) := by
  unfold bodyCall
  with_reducible (repeat' (first
    | exact mapM_fresh Sem.lookupValue _ lookup_fresh
    | exact lookupDirectCallee_fresh _ _ _ _
    | exact directCallHeader_fresh _ _
    | exact directCallFrame_fresh _ _
    | exact bindCallResults_fresh _ _ _ _
    | exact pure_fresh _
    | exact throw_fresh _
    | refine bind_fresh _ _ ?_ (fun value => ?_)
    | intro value
    | (split <;> try dsimp only)))

private theorem indirectAddress_fresh (value : Value) : KeepsFresh (indirectAddress value) := by
  cases value <;> first | exact pure_fresh _ | exact throwTypeError_fresh _

private theorem rawIndirectArguments_fresh (ctx : EvalContext) (address : Addr) (sig : FuncTyId)
    (args : List Value) : KeepsFresh (rawIndirectArguments ctx address sig args) := by
  unfold rawIndirectArguments
  with_reducible (repeat' (first
    | exact requireUntypedAbi_fresh _
    | exact throwTypeError_fresh _
    | exact throwUB_fresh _
    | exact pure_fresh _
    | refine bind_fresh _ _ ?_ (fun value => ?_)
    | intro value
    | (split <;> try dsimp only)))

private theorem indirectArguments_fresh (ctx : EvalContext) (value : Value) (address : Addr)
    (sig : FuncTyId) (args : List Value) (conv : CallingConv) :
    KeepsFresh (indirectArguments ctx value address sig args conv) := by
  cases value
  case fnDef held fn =>
    cases found : functionCallWithConvention ctx held fn sig conv <;>
      simp only [indirectArguments, found] <;>
      first | exact pure_fresh _ | exact throw_fresh _
  case typedClosure cid fn captures =>
    cases found : closureCall ctx cid fn captures sig args conv <;>
      simp only [indirectArguments, found] <;>
      first | exact pure_fresh _ | exact throw_fresh _
  all_goals exact rawIndirectArguments_fresh ctx address sig args

private theorem deferredIndirectArguments_fresh (ctx : EvalContext) (value : Value) (address : Addr)
    (sig : FuncTyId) (argIds : List ValueId) (args : List Value) (conv : CallingConv) :
    KeepsFresh (deferredIndirectArguments ctx value address sig argIds args conv) := by
  cases value
  case fnItem target =>
    cases found : functionItemCall ctx target sig conv with
    | error error =>
      simp only [deferredIndirectArguments, found]
      exact throw_fresh error
    | ok fn =>
      simp only [deferredIndirectArguments, found]
      exact bind_fresh _ _ (mapM_fresh Sem.lookupValue argIds lookup_fresh)
        (fun _ => pure_fresh _)
  all_goals
    simp only [deferredIndirectArguments]
    apply indirectArguments_fresh

theorem bodyIndirect_fresh (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (id : ValueId) (sig : FuncTyId) (args : List ValueId)
    (conv : CallingConv) (dests : List ValueId) :
    KeepsFresh (bodyIndirect recurse ctx depth strat id sig args conv dests) := by
  unfold bodyIndirect
  with_reducible (repeat' (first
    | exact lookup_fresh _
    | exact SSAFreshMemory.fromMemoryExcept_fresh _
    | exact indirectAddress_fresh _
    | exact mapM_fresh Sem.lookupValue _ lookup_fresh
    | exact deferredIndirectArguments_fresh _ _ _ _ _ _ _
    | exact requireUntypedAbi_fresh _
    | exact rejectPoisonValues_fresh _ _
    | exact callFrameWith_fresh _ _
    | exact bindCallResults_fresh _ _ _ _
    | exact pure_fresh _
    | exact throw_fresh _
    | exact throwTypeError_fresh _
    | refine bind_fresh _ _ ?_ (fun value => ?_)
    | intro value
    | (split <;> try dsimp only)))

private theorem bodyDispatch_fresh (inst : Inst)
    (onCall : FuncId → List ValueId → Sem (ForInStep Unit))
    (onIndirect : ValueId → FuncTyId → List ValueId → CallingConv → Sem (ForInStep Unit))
    (onAssert : Sem (ForInStep Unit)) (onPad : Bool → List Nat → Sem (ForInStep Unit))
    (onOther : Sem (ForInStep Unit))
    (calls : ∀ id args, KeepsFresh (onCall id args))
    (indirect : ∀ id sig args conv, KeepsFresh (onIndirect id sig args conv))
    (assertion : KeepsFresh onAssert)
    (pad : ∀ cleanup clauses, KeepsFresh (onPad cleanup clauses))
    (other : KeepsFresh onOther) :
    KeepsFresh (bodyDispatch onCall onIndirect onAssert onPad onOther inst) := by
  cases inst
  case Call id args => exact calls id args
  case CallIndirect id sig args conv => exact indirect id sig args conv
  case Assert condition kind site => exact assertion
  case LandingPad cleanup clauses => exact pad cleanup clauses
  all_goals exact other

theorem producedStep_fresh (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (inst : Inst) (dests : List ValueId) (result : InstrResult) :
    KeepsFresh (producedStep recurse ctx depth strat inst dests result) := by
  cases result with
  | value value =>
    exact bind_fresh _ _ (bindInstructionResults_fresh ctx inst (.value value) dests)
      (fun _ => pure_fresh _)
  | values values =>
    exact bind_fresh _ _ (bindInstructionResults_fresh ctx inst (.values values) dests)
      (fun _ => pure_fresh _)
  | terminator result =>
    cases result <;> first
      | exact seqMapStep_fresh recurse ctx depth strat inst dests _ _
      | exact bind_fresh _ _ (throwTypeError_fresh _) (fun _ => pure_fresh _)

theorem evalBodyStep_fresh (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (inst : Inst) (dests : List ValueId) :
    KeepsFresh (evalBodyStep recurse ctx depth strat (inst, dests)) := by
  rw [evalBodyStep_dispatch]
  apply bodyDispatch_fresh
  · intro id args
    exact bodyCall_fresh recurse ctx depth strat id args dests
  · intro id sig args conv
    exact bodyIndirect_fresh recurse ctx depth strat id sig args conv dests
  · exact bind_fresh _ _
      (SSAFreshUnwindBody.raiseIfUnwind_fresh strat (stepInstWithContext ctx inst) ctx.byteModel
        (SSAFreshContext.stepInstWithContext_fresh ctx inst))
      (fun result => bind_fresh _ _ (bindInstructionResults_fresh ctx inst result dests)
        (fun _ => pure_fresh _))
  · intro cleanup clauses
    exact bind_fresh _ _ (SSAFreshUnwindBody.semLandingPadWith_fresh strat ctx (.LandingPad cleanup clauses) dests)
      (fun _ => pure_fresh _)
  · exact bind_fresh _ _ (SSAFreshContext.stepInstWithContext_fresh ctx inst)
      (fun result => producedStep_fresh recurse ctx depth strat inst dests result)

theorem evalBody_fresh (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (rows : List (Inst × List ValueId)) :
    KeepsFresh (evalBody recurse ctx depth strat rows) := by
  apply SSAFreshLoops.forIn_fresh
  intro row member unit
  exact evalBodyStep_fresh recurse ctx depth strat row.1 row.2

end TrustIr.GenericCoro.Prefix
