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

/-- Classify genuine callees at their actual header return declarations.
    The two supplied families are derived by the uniform fuel induction,
    not by assuming successful evaluation or any well-typed argument. -/
theorem calleeEffects_of_update (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (selected : FuncId) (sourceFunction targetFunction : EvalFunction)
    (body : sourceFunction.body = targetFunction.body)
    (sourceIdentity : sourceFunction.sourceId = targetFunction.sourceId)
    (same : ∀ metadata, SameGraphs sourceRecurse targetRecurse (callerContext base metadata)
      (withFunction base selected sourceFunction).functions
      (withFunction base selected targetFunction).functions)
    (selectedEffects : ∀ metadata, SelectedEffects sourceRecurse targetRecurse (callerContext base metadata)
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
    simpa only [calleeContext, body, sourceIdentity] using
      selectedEffects ⟨some sourceFunction.body.returnTys, sourceFunction.sourceId⟩ depth args strategy world
  | false =>
    simp only [withFunction, equality, Bool.false_eq_true, if_false] at sourceFound targetFound
    have callees : sourceCallee = targetCallee := Option.some.inj (sourceFound.symm.trans targetFound)
    subst targetCallee
    change EffectRelation
      (Sem.run (sourceRecurse
        (scopedContext (callerContext base ⟨some sourceCallee.body.returnTys, sourceCallee.sourceId⟩)
          (withFunction base selected sourceFunction).functions sourceCallee.localTypes)
        depth sourceCallee.cfg sourceCallee.entryBlock args strategy) (callerWorld world))
      (Sem.run (targetRecurse
        (scopedContext (callerContext base ⟨some sourceCallee.body.returnTys, sourceCallee.sourceId⟩)
          (withFunction base selected targetFunction).functions sourceCallee.localTypes)
        depth sourceCallee.cfg sourceCallee.entryBlock args strategy) (callerWorld world))
    rw [same ⟨some sourceCallee.body.returnTys, sourceCallee.sourceId⟩ sourceCallee.localTypes depth
      sourceCallee.cfg sourceCallee.entryBlock args strategy]
    exact effectRelation_refl _

/-- Uniformity in inherited return and owner metadata is required by actual recursive
    calls: entering a function replaces that metadata with its own header.
    The local layer proof is still consumed at every context in the family. -/
theorem evaluator_simulation_uniform (base : EvalContext) (selected : FuncId)
    (sourceFunction targetFunction : EvalFunction)
    (body : sourceFunction.body = targetFunction.body)
    (convention : sourceFunction.callingConv = targetFunction.callingConv)
    (sourceIdentity : sourceFunction.sourceId = targetFunction.sourceId)
    (selectedLayer : ∀ metadata sourceRecurse targetRecurse,
      CalleeEffects sourceRecurse targetRecurse (callerContext base metadata)
        (withFunction base selected sourceFunction).functions
        (withFunction base selected targetFunction).functions →
      SelectedEffects
        (fun ctx depth cfg pc args strategy => evalLayer sourceRecurse ctx depth cfg pc args strategy)
        (fun ctx depth cfg pc args strategy => evalLayer targetRecurse ctx depth cfg pc args strategy)
        (callerContext base metadata) (withFunction base selected sourceFunction).functions
        (withFunction base selected targetFunction).functions sourceFunction targetFunction)
    (fuel : Nat) :
    (∀ metadata, SameGraphs (evaluatorAt fuel) (evaluatorAt fuel) (callerContext base metadata)
      (withFunction base selected sourceFunction).functions
      (withFunction base selected targetFunction).functions) ∧
    (∀ metadata, SelectedEffects (evaluatorAt fuel) (evaluatorAt fuel) (callerContext base metadata)
      (withFunction base selected sourceFunction).functions
      (withFunction base selected targetFunction).functions sourceFunction targetFunction) := by
  induction fuel with
  | zero =>
    constructor
    · intro metadata types depth cfg pc args strategy
      rfl
    · intro metadata depth args strategy world
      exact .error .outOfFuel
  | succ fuel ih =>
    have effects := calleeEffects_of_update (evaluatorAt fuel) (evaluatorAt fuel) base selected
      sourceFunction targetFunction body sourceIdentity ih.1 ih.2
    have headers := headerAgreement_withFunction base selected sourceFunction targetFunction body convention
    constructor
    · intro metadata types depth cfg pc args strategy
      simp only [evaluatorAt, stepNWithContext_succ_layer]
      apply evalLayer_congr _ _ (callerContext base metadata) _ _ headers effects types depth cfg pc args strategy
      intro block result
      exact evalTransfer_congr _ _ (callerContext base metadata) _ _ headers effects (ih.1 metadata)
        types depth cfg block strategy result
    · intro metadata depth args strategy world
      simpa only [evaluatorAt, stepNWithContext_succ_layer] using
        selectedLayer metadata (evaluatorAt fuel) (evaluatorAt fuel) effects depth args strategy world

/-- Specialize the uniform induction back to the caller's original lexical metadata.
    The unchanged-graph and selected-entry conclusions retain their complete
    original domains. -/
theorem evaluator_simulation (base : EvalContext) (selected : FuncId)
    (sourceFunction targetFunction : EvalFunction)
    (body : sourceFunction.body = targetFunction.body)
    (convention : sourceFunction.callingConv = targetFunction.callingConv)
    (sourceIdentity : sourceFunction.sourceId = targetFunction.sourceId)
    (selectedLayer : ∀ metadata sourceRecurse targetRecurse,
      CalleeEffects sourceRecurse targetRecurse (callerContext base metadata)
        (withFunction base selected sourceFunction).functions
        (withFunction base selected targetFunction).functions →
      SelectedEffects
        (fun ctx depth cfg pc args strategy => evalLayer sourceRecurse ctx depth cfg pc args strategy)
        (fun ctx depth cfg pc args strategy => evalLayer targetRecurse ctx depth cfg pc args strategy)
        (callerContext base metadata) (withFunction base selected sourceFunction).functions
        (withFunction base selected targetFunction).functions sourceFunction targetFunction)
    (fuel : Nat) :
    SameGraphs (evaluatorAt fuel) (evaluatorAt fuel) base
      (withFunction base selected sourceFunction).functions
      (withFunction base selected targetFunction).functions ∧
    SelectedEffects (evaluatorAt fuel) (evaluatorAt fuel) base
      (withFunction base selected sourceFunction).functions
      (withFunction base selected targetFunction).functions sourceFunction targetFunction := by
  have uniform := evaluator_simulation_uniform base selected sourceFunction targetFunction
    body convention sourceIdentity selectedLayer fuel
  simpa only [callerContext_self] using
    And.intro (uniform.1 (CallerMetadata.ofContext base)) (uniform.2 (CallerMetadata.ofContext base))

end TrustIr.GenericCoro.Prefix
