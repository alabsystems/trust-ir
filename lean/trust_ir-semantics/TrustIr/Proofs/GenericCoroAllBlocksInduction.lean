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

/-- Simultaneous induction is uniform in the caller's inherited return
    declarations. Genuine recursive entries replace them from actual headers;
    every error, fresh-state argument and non-SSA world is retained. -/
theorem evaluator_simulation_uniform (base : EvalContext) (selected : FuncId)
    (sourceFunction targetFunction : EvalFunction)
    (body : sourceFunction.body = targetFunction.body)
    (convention : sourceFunction.callingConv = targetFunction.callingConv)
    (entry : sourceFunction.entryBlock = targetFunction.entryBlock)
    (sourceIdentity : sourceFunction.sourceId = targetFunction.sourceId)
    (pairedLayer : ∀ metadata sourceRecurse targetRecurse,
      CalleeEffects sourceRecurse targetRecurse (callerContext base metadata)
        (withFunction base selected sourceFunction).functions
        (withFunction base selected targetFunction).functions →
      PairedEffects sourceRecurse targetRecurse (callerContext base metadata)
        (withFunction base selected sourceFunction).functions
        (withFunction base selected targetFunction).functions sourceFunction targetFunction →
      PairedEffects
        (fun ctx depth cfg pc args strategy => evalLayer sourceRecurse ctx depth cfg pc args strategy)
        (fun ctx depth cfg pc args strategy => evalLayer targetRecurse ctx depth cfg pc args strategy)
        (callerContext base metadata) (withFunction base selected sourceFunction).functions
        (withFunction base selected targetFunction).functions sourceFunction targetFunction)
    (fuel : Nat) :
    (∀ metadata, SameGraphs (evaluatorAt fuel) (evaluatorAt fuel) (callerContext base metadata)
      (withFunction base selected sourceFunction).functions
      (withFunction base selected targetFunction).functions) ∧
    (∀ metadata, PairedEffects (evaluatorAt fuel) (evaluatorAt fuel) (callerContext base metadata)
      (withFunction base selected sourceFunction).functions
      (withFunction base selected targetFunction).functions sourceFunction targetFunction) := by
  induction fuel with
  | zero =>
    constructor
    · intro metadata types depth cfg pc args strategy
      rfl
    · intro metadata depth pc args strategy state fresh
      exact .error .outOfFuel
  | succ fuel ih =>
    have selectedEffects := fun metadata => selected_of_paired (evaluatorAt fuel) (evaluatorAt fuel)
      (callerContext base metadata) _ _ sourceFunction targetFunction entry (ih.2 metadata)
    have effects := calleeEffects_of_update (evaluatorAt fuel) (evaluatorAt fuel) base selected
      sourceFunction targetFunction body sourceIdentity ih.1 selectedEffects
    have headers := headerAgreement_withFunction base selected sourceFunction targetFunction body convention
    constructor
    · intro metadata types depth cfg pc args strategy
      simp only [evaluatorAt, stepNWithContext_succ_layer]
      apply evalLayer_congr _ _ (callerContext base metadata) _ _ headers effects types depth cfg pc args strategy
      intro block result
      exact evalTransfer_congr _ _ (callerContext base metadata) _ _ headers effects (ih.1 metadata)
        types depth cfg block strategy result
    · intro metadata depth pc args strategy state fresh
      simpa only [evaluatorAt, stepNWithContext_succ_layer] using
        pairedLayer metadata (evaluatorAt fuel) (evaluatorAt fuel) effects (ih.2 metadata)
          depth pc args strategy state fresh

/-- Recover the original fixed-context observations from the uniform family.
    Public transformation consumers derive the family from their universal
    context input, without additional source or execution premises. -/
theorem evaluator_simulation (base : EvalContext) (selected : FuncId)
    (sourceFunction targetFunction : EvalFunction)
    (body : sourceFunction.body = targetFunction.body)
    (convention : sourceFunction.callingConv = targetFunction.callingConv)
    (entry : sourceFunction.entryBlock = targetFunction.entryBlock)
    (sourceIdentity : sourceFunction.sourceId = targetFunction.sourceId)
    (pairedLayer : ∀ metadata sourceRecurse targetRecurse,
      CalleeEffects sourceRecurse targetRecurse (callerContext base metadata)
        (withFunction base selected sourceFunction).functions
        (withFunction base selected targetFunction).functions →
      PairedEffects sourceRecurse targetRecurse (callerContext base metadata)
        (withFunction base selected sourceFunction).functions
        (withFunction base selected targetFunction).functions sourceFunction targetFunction →
      PairedEffects
        (fun ctx depth cfg pc args strategy => evalLayer sourceRecurse ctx depth cfg pc args strategy)
        (fun ctx depth cfg pc args strategy => evalLayer targetRecurse ctx depth cfg pc args strategy)
        (callerContext base metadata) (withFunction base selected sourceFunction).functions
        (withFunction base selected targetFunction).functions sourceFunction targetFunction)
    (fuel : Nat) :
    SameGraphs (evaluatorAt fuel) (evaluatorAt fuel) base
      (withFunction base selected sourceFunction).functions
      (withFunction base selected targetFunction).functions ∧
    PairedEffects (evaluatorAt fuel) (evaluatorAt fuel) base
      (withFunction base selected sourceFunction).functions
      (withFunction base selected targetFunction).functions sourceFunction targetFunction := by
  have uniform := evaluator_simulation_uniform base selected sourceFunction targetFunction
    body convention entry sourceIdentity pairedLayer fuel
  simpa only [callerContext_self] using
    And.intro (uniform.1 (CallerMetadata.ofContext base)) (uniform.2 (CallerMetadata.ofContext base))

end TrustIr.GenericCoro.AllBlocksInduction
