-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixLayerEq

namespace TrustIr.GenericCoro.Prefix

theorem effectRelation_refl (outcome : Except SemError (List Value × MachineState)) :
    EffectRelation outcome outcome := by
  cases outcome with
  | error error => exact .error error
  | ok result => exact .returned result.1 result.2 result.2 rfl

/-- The callback at exactly the predecessor block-fuel budget. -/
def evaluatorAt (fuel : Nat) : Recurse :=
  fun ctx depth cfg pc args strategy => stepNWithContext ctx fuel depth cfg pc args strategy

/-- Equality for an unchanged graph and identical active declarations. This
    includes graphs whose representation happens to equal the selected graph. -/
def SameGraphs (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) : Prop :=
  ∀ types depth cfg pc args strategy,
    sourceRecurse (scopedContext base source types) depth cfg pc args strategy =
      targetRecurse (scopedContext base target types) depth cfg pc args strategy

/-- The selected function enters with its own source-derived declarations
    and a cleared caller frame. Every error and every non-SSA field remains
    part of the relation. -/
def SelectedEffects (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (sourceFunction targetFunction : EvalFunction) : Prop :=
  ∀ depth args strategy world,
    EffectRelation
      (Sem.run (sourceRecurse (scopedContext base source sourceFunction.localTypes)
        depth sourceFunction.cfg sourceFunction.entryBlock args strategy) (callerWorld world))
      (Sem.run (targetRecurse (scopedContext base target targetFunction.localTypes)
        depth targetFunction.cfg targetFunction.entryBlock args strategy) (callerWorld world))

/-- Classify callees by their actual function-table key. No CFG-identity
    assumption is used for unrelated functions. -/
theorem calleeEffects_of_update (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (selected : FuncId) (sourceFunction targetFunction : EvalFunction)
    (same : SameGraphs sourceRecurse targetRecurse base
      (withFunction base selected sourceFunction).functions
      (withFunction base selected targetFunction).functions)
    (selectedEffects : SelectedEffects sourceRecurse targetRecurse base
      (withFunction base selected sourceFunction).functions
      (withFunction base selected targetFunction).functions sourceFunction targetFunction) :
    CalleeEffects sourceRecurse targetRecurse base
      (withFunction base selected sourceFunction).functions
      (withFunction base selected targetFunction).functions := by
  intro id sourceCallee targetCallee sourceFound targetFound depth args strategy world
  cases equality : id == selected with
  | true =>
    simp only [withFunction, equality, if_true, Option.some.injEq] at sourceFound targetFound
    subst sourceCallee
    subst targetCallee
    exact selectedEffects depth args strategy world
  | false =>
    simp only [withFunction, equality, Bool.false_eq_true, if_false] at sourceFound targetFound
    have callees : sourceCallee = targetCallee := Option.some.inj (sourceFound.symm.trans targetFound)
    subst targetCallee
    rw [same sourceCallee.localTypes depth sourceCallee.cfg sourceCallee.entryBlock args strategy]
    exact effectRelation_refl _

/-- Simultaneous resource induction. The selected-entry premise is a local
    one-layer proof consuming only predecessor callee effects; recursive and
    mutually recursive prefixes therefore use the same fuel induction as
    unchanged graphs and terminal continuations. -/
theorem evaluator_simulation (base : EvalContext) (selected : FuncId)
    (sourceFunction targetFunction : EvalFunction)
    (body : sourceFunction.body = targetFunction.body)
    (convention : sourceFunction.callingConv = targetFunction.callingConv)
    (selectedLayer : ∀ sourceRecurse targetRecurse,
      CalleeEffects sourceRecurse targetRecurse base
        (withFunction base selected sourceFunction).functions
        (withFunction base selected targetFunction).functions →
      SelectedEffects
        (fun ctx depth cfg pc args strategy => evalLayer sourceRecurse ctx depth cfg pc args strategy)
        (fun ctx depth cfg pc args strategy => evalLayer targetRecurse ctx depth cfg pc args strategy)
        base (withFunction base selected sourceFunction).functions
        (withFunction base selected targetFunction).functions sourceFunction targetFunction)
    (fuel : Nat) :
    SameGraphs (evaluatorAt fuel) (evaluatorAt fuel) base
      (withFunction base selected sourceFunction).functions
      (withFunction base selected targetFunction).functions ∧
    SelectedEffects (evaluatorAt fuel) (evaluatorAt fuel) base
      (withFunction base selected sourceFunction).functions
      (withFunction base selected targetFunction).functions sourceFunction targetFunction := by
  induction fuel with
  | zero =>
    constructor
    · intro types depth cfg pc args strategy
      rfl
    · intro depth args strategy world
      exact .error .outOfFuel
  | succ fuel ih =>
    have effects := calleeEffects_of_update (evaluatorAt fuel) (evaluatorAt fuel) base selected
      sourceFunction targetFunction ih.1 ih.2
    have headers := headerAgreement_withFunction base selected sourceFunction targetFunction body convention
    constructor
    · intro types depth cfg pc args strategy
      simp only [evaluatorAt, stepNWithContext_succ_layer]
      apply evalLayer_congr _ _ base _ _ headers effects types depth cfg pc args strategy
      intro block result
      exact evalTransfer_congr _ _ base _ _ headers effects ih.1 types depth cfg block strategy result
    · intro depth args strategy world
      simpa only [evaluatorAt, stepNWithContext_succ_layer] using
        selectedLayer (evaluatorAt fuel) (evaluatorAt fuel) effects depth args strategy world

end TrustIr.GenericCoro.Prefix
