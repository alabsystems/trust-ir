-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroAllBlocksLayer
import TrustIr.Proofs.GenericCoroAllBlocksTransfer
import TrustIr.Proofs.GenericCoroAllBlocksInduction
import TrustIr.Proofs.GenericCoroPrefixCallBoundary

namespace TrustIr.GenericCoro.AllBlocksSimulation
open Prefix GenericCoroAllBlocksPlanner

/-- The complete actual transfer proof discharges the layer's retained-block
    obligation. The only recursive premises are predecessor callee effects and
    the predecessor paired-CFG simulation from the block-fuel induction. -/
theorem lowerRows_layer_effect (sourceRecurse targetRecurse : Recurse)
    (base : EvalContext) (source target : FuncId → Option EvalFunction)
    (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (blocks : Rows) (ready : Ready (planAllBlocks blocks))
    (sourceTypes targetTypes : LocalTypeTable)
    (preserved : ∀ id ∈ graphValueIds blocks, sourceTypes id = targetTypes id)
    (typed : AllBlocksInference.TraceTyped targetTypes (planAllBlocks blocks).trace)
    (paired : GenericCoroAllBlocksTransfer.PairedCallbacks sourceRecurse targetRecurse base source target
      (some sourceTypes) (some targetTypes) (cfgOf blocks) (cfgOf (planAllBlocks blocks).rows))
    (depth : Nat) (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (fresh : SSAFreshFrames.FreshState state) :
    EffectRelation
      (Sem.run (evalLayer sourceRecurse (scopedContext base source (some sourceTypes)) depth
        (cfgOf blocks) pc args strategy) state)
      (Sem.run (evalLayer targetRecurse (scopedContext base target (some targetTypes)) depth
        (cfgOf (planAllBlocks blocks).rows) pc args strategy) state) := by
  apply AllBlocksLayer.lowerRows_layer_of_transfer sourceRecurse targetRecurse base source target
    headers effects blocks ready sourceTypes targetTypes preserved typed _ depth pc args strategy state fresh
  intro callDepth block panic result types after afterFresh
  exact GenericCoroAllBlocksTransfer.evalTransfer_effect sourceRecurse targetRecurse base source target
    headers effects (some sourceTypes) (some targetTypes) (cfgOf blocks)
    (cfgOf (planAllBlocks blocks).rows)
    (GenericCoroAllBlocksViews.planAllBlocks_ready_padViews blocks ready) paired block types
    callDepth panic result after afterFresh

/-- Every suspend TERMINATOR occurrence in the selected finite function is
    lowered. The entry may be any block shape, and arbitrary prefixes and
    recursive/mutually recursive callees use the actual evaluator induction.
    Complete caller-state equality holds at the actual shared Call helper,
    for every caller context/state, fuel, depth, argument list and strategy.
    No caller freshness, frame validity, successful prefix or no-call premise
    is part of this public call-equivalence statement. -/
theorem lowerRows_runCallEquivalent (header : EvalFunction) (blocks : Rows)
    (ready : Ready (planAllBlocks blocks)) (sourceTypes targetTypes : LocalTypeTable)
    (preserved : ∀ id ∈ graphValueIds blocks, sourceTypes id = targetTypes id)
    (typed : AllBlocksInference.TraceTyped targetTypes (planAllBlocks blocks).trace) :
    RunCallEquivalent {header with cfg := cfgOf blocks, localTypes := some sourceTypes}
      {header with cfg := cfgOf (planAllBlocks blocks).rows, localTypes := some targetTypes} := by
  let sourceFunction : EvalFunction := {header with cfg := cfgOf blocks, localTypes := some sourceTypes}
  let targetFunction : EvalFunction :=
    {header with cfg := cfgOf (planAllBlocks blocks).rows, localTypes := some targetTypes}
  apply runCallEquivalent_of_selectedEffects sourceFunction targetFunction rfl
  intro ctx selected fuel
  have simulated := AllBlocksInduction.evaluator_simulation ctx selected sourceFunction targetFunction
    rfl rfl rfl ?_ fuel
  · exact AllBlocksInduction.selected_of_paired (evaluatorAt fuel) (evaluatorAt fuel) ctx
      _ _ sourceFunction targetFunction rfl simulated.2
  · intro sourceRecurse targetRecurse effects paired depth pc args strategy state fresh
    exact lowerRows_layer_effect sourceRecurse targetRecurse ctx
      (withFunction ctx selected sourceFunction).functions
      (withFunction ctx selected targetFunction).functions
      (headerAgreement_withFunction ctx selected sourceFunction targetFunction rfl rfl) effects
      blocks ready sourceTypes targetTypes preserved typed paired depth pc args strategy state fresh

end TrustIr.GenericCoro.AllBlocksSimulation
