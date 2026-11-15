-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixInduction

namespace TrustIr.GenericCoro.AllBlocksInduction
open Prefix

/-- The selected graph pair is related at every program counter and every
    fresh input state, including nonempty SSA frames after earlier blocks. -/
def PairedEffects (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (sourceFunction targetFunction : EvalFunction) : Prop :=
  ∀ depth pc args strategy state, SSAFreshFrames.FreshState state →
    EffectRelation
      (Sem.run (sourceRecurse (scopedContext base source sourceFunction.localTypes)
        depth sourceFunction.cfg pc args strategy) state)
      (Sem.run (targetRecurse (scopedContext base target targetFunction.localTypes)
        depth targetFunction.cfg pc args strategy) state)

theorem selected_of_paired (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (sourceFunction targetFunction : EvalFunction)
    (entry : sourceFunction.entryBlock = targetFunction.entryBlock)
    (paired : PairedEffects sourceRecurse targetRecurse base source target sourceFunction targetFunction) :
    SelectedEffects sourceRecurse targetRecurse base source target sourceFunction targetFunction := by
  intro depth args strategy world
  rw [← entry]
  exact paired depth sourceFunction.entryBlock args strategy (callerWorld world)
    (SSAFreshFrames.cleared_fresh world)

/-- Simultaneous induction over the actual production block-fuel budget.
    Unchanged CFGs use exact equality; the selected pair uses full errors,
    returned values and non-SSA worlds. Calls are classified by function id,
    so recursive, mutually recursive and aliased CFGs follow the same rule.
    The paired one-layer obligation must still be discharged for the actual
    planner output; this induction theorem alone is not a pass proof. -/
theorem evaluator_simulation (base : EvalContext) (selected : FuncId)
    (sourceFunction targetFunction : EvalFunction)
    (body : sourceFunction.body = targetFunction.body)
    (convention : sourceFunction.callingConv = targetFunction.callingConv)
    (entry : sourceFunction.entryBlock = targetFunction.entryBlock)
    (pairedLayer : ∀ sourceRecurse targetRecurse,
      CalleeEffects sourceRecurse targetRecurse base
        (withFunction base selected sourceFunction).functions
        (withFunction base selected targetFunction).functions →
      PairedEffects sourceRecurse targetRecurse base
        (withFunction base selected sourceFunction).functions
        (withFunction base selected targetFunction).functions sourceFunction targetFunction →
      PairedEffects
        (fun ctx depth cfg pc args strategy => evalLayer sourceRecurse ctx depth cfg pc args strategy)
        (fun ctx depth cfg pc args strategy => evalLayer targetRecurse ctx depth cfg pc args strategy)
        base (withFunction base selected sourceFunction).functions
        (withFunction base selected targetFunction).functions sourceFunction targetFunction)
    (fuel : Nat) :
    SameGraphs (evaluatorAt fuel) (evaluatorAt fuel) base
      (withFunction base selected sourceFunction).functions
      (withFunction base selected targetFunction).functions ∧
    PairedEffects (evaluatorAt fuel) (evaluatorAt fuel) base
      (withFunction base selected sourceFunction).functions
      (withFunction base selected targetFunction).functions sourceFunction targetFunction := by
  induction fuel with
  | zero =>
    constructor
    · intro types depth cfg pc args strategy
      rfl
    · intro depth pc args strategy state fresh
      exact .error .outOfFuel
  | succ fuel ih =>
    have selectedEffects := selected_of_paired (evaluatorAt fuel) (evaluatorAt fuel) base
      _ _ sourceFunction targetFunction entry ih.2
    have effects := calleeEffects_of_update (evaluatorAt fuel) (evaluatorAt fuel) base selected
      sourceFunction targetFunction ih.1 selectedEffects
    have headers := headerAgreement_withFunction base selected sourceFunction targetFunction body convention
    constructor
    · intro types depth cfg pc args strategy
      simp only [evaluatorAt, stepNWithContext_succ_layer]
      apply evalLayer_congr _ _ base _ _ headers effects types depth cfg pc args strategy
      intro block result
      exact evalTransfer_congr _ _ base _ _ headers effects ih.1 types depth cfg block strategy result
    · intro depth pc args strategy state fresh
      simpa only [evaluatorAt, stepNWithContext_succ_layer] using
        pairedLayer (evaluatorAt fuel) (evaluatorAt fuel) effects ih.2 depth pc args strategy state fresh

end TrustIr.GenericCoro.AllBlocksInduction
