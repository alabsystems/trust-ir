-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroAllBlocksEffect
import TrustIr.Proofs.GenericCoroPadViews

namespace TrustIr.GenericCoro.AllBlocksKept
open Prefix

-- Preserve the original universe-polymorphic eliminator and constructor order.
run_cmd do
  if Lean.versionString == "4.8.0" then pure ()
  else if Lean.versionString == "4.30.0-rc2" then
    let originalName := Lean.mkIdent
      (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "evalLayer_effect") "match_1")
    Lean.Elab.Command.elabCommand (← `(command|
      def $originalName:ident.{u_1} (motive : InstrResult → Sort u_1)
          (termResult : InstrResult)
          (h_1 : (result : StepResult) → motive (.terminator result))
          (h_2 : (value : Option ValueId) → motive (.value value))
          (h_3 : (values : List ValueId) → motive (.values values)) : motive termResult := by
        cases termResult with
        | terminator result => exact h_1 result
        | value value => exact h_2 value
        | values values => exact h_3 values))
  else throwError "unsupported compiler for original kept matcher"

/-- An unchanged block in a changed graph executes its actual prefix and
    terminator checks before the paired terminal transfer. The different CFGs
    agree only on pad observations; their recursive continuations may differ.
    No successful body, terminator, argument or transfer outcome is assumed. -/
theorem evalLayer_effect (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (depth : Nat)
    (sourceCFG targetCFG : CFG) (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (block : BasicBlock) (sourceFound : sourceCFG pc = some block)
    (targetFound : targetCFG pc = some block)
    (views : PadViews.PadViewsAgree sourceCFG targetCFG)
    (rowTypes : ∀ row ∈ bodyInstsWithResultDests (base.resolveBlock block).body
      (base.resolveBlock block).bodyResultDests,
      TypesAgreeOn (row.2 ++ operandIds row.1) sourceTypes targetTypes)
    (transfers : ∀ result state, SSAFreshFrames.FreshState state →
      EffectRelation
        (Sem.run (evalTransfer sourceRecurse (scopedContext base source sourceTypes) depth
          sourceCFG (base.resolveBlock block) strategy result) state)
        (Sem.run (evalTransfer targetRecurse (scopedContext base target targetTypes) depth
          targetCFG (base.resolveBlock block) strategy result) state))
    (state : MachineState) (fresh : SSAFreshFrames.FreshState state) :
    EffectRelation
      (Sem.run (evalLayer sourceRecurse (scopedContext base source sourceTypes) depth
        sourceCFG pc args strategy) state)
      (Sem.run (evalLayer targetRecurse (scopedContext base target targetTypes) depth
        targetCFG pc args strategy) state) := by
  let resolved := base.resolveBlock block
  let rows := bodyInstsWithResultDests resolved.body resolved.bodyResultDests
  have body := evalBody_congrOn sourceRecurse targetRecurse base source target headers effects
    sourceTypes targetTypes depth strategy rows rowTypes
  have term := PadViews.stepTermWithContext_congr
    (scopedContext base source sourceTypes) (scopedContext base target targetTypes)
    depth sourceCFG targetCFG resolved.terminator strategy rfl
    (functionCall_congr base source target headers sourceTypes targetTypes)
    (closureCall_congr base source target headers sourceTypes targetTypes) views
  have paramsFresh : SSAFreshStep.KeepsFresh (bindBlockParamsChecked resolved.params args) := by
    intro current result currentFresh ran
    rcases result with ⟨unit, after⟩
    cases unit
    exact SSAFreshFrames.bindBlockParamsChecked_preserves_fresh resolved.params args
      current after currentFresh ran
  have firstFresh : SSAFreshStep.KeepsFresh (do
      (do
        bindBlockParamsChecked resolved.params args
        evalBody targetRecurse (scopedContext base target targetTypes) depth strategy rows)
      stepTermWithContext (scopedContext base target targetTypes) depth targetCFG
        resolved.terminator strategy) :=
    SSAFreshStep.bind_fresh _ _
      (SSAFreshStep.bind_fresh _ _ paramsFresh (fun _ => evalBody_fresh _ _ _ _ _))
      (fun _ => PadViews.stepTermWithContext_fresh _ _ _ _ _)
  rw [evalLayer_eq_transfer, evalLayer_eq_transfer]
  simp only [sourceFound, targetFound, resolveBlock_scoped]
  change EffectRelation
    (Sem.run (do
      bindBlockParamsChecked resolved.params args
      evalBody sourceRecurse (scopedContext base source sourceTypes) depth strategy rows
      let termResult ← stepTermWithContext (scopedContext base source sourceTypes) depth
        sourceCFG resolved.terminator strategy
      let result ← match termResult with
        | .terminator result => pure result
        | .value _ => Sem.throwTypeError "basic block does not end with a terminator"
        | .values _ => Sem.throwTypeError "basic block does not end with a terminator"
      evalTransfer sourceRecurse (scopedContext base source sourceTypes) depth sourceCFG
        resolved strategy result) state)
    (Sem.run (do
      bindBlockParamsChecked resolved.params args
      evalBody targetRecurse (scopedContext base target targetTypes) depth strategy rows
      let termResult ← stepTermWithContext (scopedContext base target targetTypes) depth
        targetCFG resolved.terminator strategy
      let result ← match termResult with
        | .terminator result => pure result
        | .value _ => Sem.throwTypeError "basic block does not end with a terminator"
        | .values _ => Sem.throwTypeError "basic block does not end with a terminator"
      evalTransfer targetRecurse (scopedContext base target targetTypes) depth targetCFG
        resolved strategy result) state)
  rw [body, term, ← bind_assoc, ← bind_assoc, ← bind_assoc, ← bind_assoc]
  apply AllBlocksEffect.bind_effect _ _ _ firstFresh _ state fresh
  intro termResult after afterFresh
  trustIrCompilerProof {
    cases termResult with
    | terminator result =>
      simpa only [pure_bind] using transfers result after afterFresh
    | value _ => exact .error (.typeError "basic block does not end with a terminator")
    | values _ => exact .error (.typeError "basic block does not end with a terminator")
  } {
    refine evalLayer_effect.match_1 (fun termResult => EffectRelation
        (Sem.run (do
          let result ← match termResult with
            | .terminator result => pure result
            | .value _ => Sem.throwTypeError "basic block does not end with a terminator"
            | .values _ => Sem.throwTypeError "basic block does not end with a terminator"
          evalTransfer sourceRecurse (scopedContext base source sourceTypes) depth sourceCFG
            resolved strategy result) after)
        (Sem.run (do
          let result ← match termResult with
            | .terminator result => pure result
            | .value _ => Sem.throwTypeError "basic block does not end with a terminator"
            | .values _ => Sem.throwTypeError "basic block does not end with a terminator"
          evalTransfer targetRecurse (scopedContext base target targetTypes) depth targetCFG
            resolved strategy result) after)) termResult ?_ ?_ ?_
    · intro result
      simpa only [pure_bind] using transfers result after afterFresh
    · intro value
      exact .error (.typeError "basic block does not end with a terminator")
    · intro values
      exact .error (.typeError "basic block does not end with a terminator")
  }

end TrustIr.GenericCoro.AllBlocksKept

#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksKept.evalLayer_effect.match_1 == []
