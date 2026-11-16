-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroAllBlocksEntry
import TrustIr.Proofs.GenericCoroPrefixEntry
import TrustIr.Proofs.GenericCoroAllBlocksKept
import TrustIr.Proofs.GenericCoroAllBlocksViews
import TrustIr.Proofs.GenericCoroAllBlocksTrace
import TrustIr.Proofs.GenericCoroAllBlocksInference

namespace TrustIr.GenericCoro.AllBlocksLayer
open Prefix GenericCoroAllBlocksPlanner

private theorem term_mem_graphNodes (blocks : Rows) (pc : BlockId) (block : BasicBlock)
    (found : cfgOf blocks pc = some block) :
    (block.terminator, block.terminatorResultDests) ∈ graphNodes blocks := by
  obtain ⟨before, id, after, decomposition, selected, noMatch⟩ :=
    cfgOf_decompose blocks pc block found
  rw [decomposition, graphNodes_append, graphNodes_cons]
  exact trustIrListMemAppendRight _
    (trustIrListMemAppendLeft _ (trustIrListMemAppendRight _ ((trustIrListMemConsSelf _ _))))

private theorem expandedBlock_effect (sourceRecurse targetRecurse : Recurse)
    (base : EvalContext) (source target : FuncId → Option EvalFunction)
    (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (blocks : Rows) (targetCFG : CFG) (pc : BlockId) (names : GraphNames blocks)
    (sourceTypes targetTypes : LocalTypeTable)
    (params : List (ValueId × Ty)) (bodyPrefix : List Inst)
    (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int)
    (sourceFound : cfgOf blocks pc = some {
      params := params, body := bodyPrefix, bodyResultDests := bodyDests,
      terminator := .CoroSuspend frame slot next value, terminatorResultDests := termDests })
    (targetFound : targetCFG pc = some (expandedEntry (Names.ofTriple names) {
      params := params, body := bodyPrefix, bodyResultDests := bodyDests,
      terminator := .CoroSuspend frame slot next value, terminatorResultDests := termDests }))
    (indexType : targetTypes (Names.ofTriple names).index = some .I64)
    (pointerType : targetTypes (Names.ofTriple names).pointer = some .Ptr)
    (stateType : targetTypes (Names.ofTriple names).state = some .I64)
    (preserved : ∀ id ∈ graphValueIds blocks, sourceTypes id = targetTypes id)
    (depth : Nat) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (fresh : SSAFreshFrames.FreshState state) :
    EffectRelation
      (Sem.run (evalLayer sourceRecurse (scopedContext base source (some sourceTypes)) depth
        (cfgOf blocks) pc args strategy) state)
      (Sem.run (evalLayer targetRecurse (scopedContext base target (some targetTypes)) depth
        targetCFG pc args strategy) state) := by
  let temps := Names.ofTriple names
  let block : BasicBlock := {
    params := params, body := bodyPrefix, bodyResultDests := bodyDests,
    terminator := .CoroSuspend frame slot next value, terminatorResultDests := termDests }
  rw [evalLayer_sourceEntry_eq sourceRecurse (scopedContext base source (some sourceTypes)) depth
      (cfgOf blocks) pc params args bodyPrefix bodyDests termDests
      frame value slot next strategy sourceFound,
    evalLayer_targetEntry_eq targetRecurse (scopedContext base target (some targetTypes)) depth
      targetCFG pc temps params args bodyPrefix bodyDests termDests
      frame value slot next strategy targetTypes rfl indexType pointerType stateType targetFound]
  have operands := suspend_prefix_operands blocks pc params bodyPrefix bodyDests termDests
    frame value slot next sourceFound
  have frameFree := GraphNames.different_original blocks names frame operands.1
  have valueFree := GraphNames.different_original blocks names value operands.2
  have pointerState : temps.pointer ≠ temps.state := by
    intro same
    exact names.secondThird (congrArg ValueId.index same)
  apply AllBlocksEntry.expandedPrefix_effect_fresh sourceRecurse targetRecurse base source target
    headers effects sourceTypes targetTypes _ _ params args depth strategy temps frame value
    slot next indexType pointerState frameFree.1 valueFree.1 valueFree.2.1 valueFree.2.2 state fresh
  intro row member
  exact resolvedEntry_typesAgree base blocks pc block sourceFound sourceTypes targetTypes
    preserved row member

/-- The literal ready planner, rather than a supplied CFG relation, decides
    the missing/kept/expanded cases at every program counter. The only remaining
    evaluator obligation is the paired terminal transfer on a retained block;
    its complete proof is supplied separately from the predecessor simulation. -/
theorem lowerRows_layer_of_transfer (sourceRecurse targetRecurse : Recurse)
    (base : EvalContext) (source target : FuncId → Option EvalFunction)
    (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (blocks : Rows) (ready : Ready (planAllBlocks blocks))
    (sourceTypes targetTypes : LocalTypeTable)
    (preserved : ∀ id ∈ graphValueIds blocks, sourceTypes id = targetTypes id)
    (typed : AllBlocksInference.TraceTyped targetTypes (planAllBlocks blocks).trace)
    (transfers : ∀ depth block strategy result,
      TypesAgreeOn (block.terminatorResultDests ++ operandIds block.terminator)
        (some sourceTypes) (some targetTypes) →
      ∀ state, SSAFreshFrames.FreshState state → EffectRelation
        (Sem.run (evalTransfer sourceRecurse (scopedContext base source (some sourceTypes)) depth
          (cfgOf blocks) block strategy result) state)
        (Sem.run (evalTransfer targetRecurse (scopedContext base target (some targetTypes)) depth
          (cfgOf (planAllBlocks blocks).rows) block strategy result) state))
    (depth : Nat) (pc : BlockId) (args : List Value) (strategy : PanicStrategy)
    (state : MachineState) (fresh : SSAFreshFrames.FreshState state) :
    EffectRelation
      (Sem.run (evalLayer sourceRecurse (scopedContext base source (some sourceTypes)) depth
        (cfgOf blocks) pc args strategy) state)
      (Sem.run (evalLayer targetRecurse (scopedContext base target (some targetTypes)) depth
        (cfgOf (planAllBlocks blocks).rows) pc args strategy) state) := by
  have views := GenericCoroAllBlocksViews.planAllBlocks_ready_padViews blocks ready
  have lookup := GenericCoroAllBlocksViews.planAllBlocks_ready_lookup blocks ready pc
  generalize sourceEq : cfgOf blocks pc = sourceBlock at lookup
  generalize targetEq : cfgOf (planAllBlocks blocks).rows pc = targetBlock at lookup
  cases lookup with
  | missing =>
    rw [evalLayer_eq_transfer, evalLayer_eq_transfer]
    simp only [sourceEq, targetEq]
    exact .error (.typeError s!"undefined block: {repr pc}")
  | kept block notSuspend =>
    apply AllBlocksKept.evalLayer_effect sourceRecurse targetRecurse base source target headers effects
      (some sourceTypes) (some targetTypes) depth (cfgOf blocks) (cfgOf (planAllBlocks blocks).rows)
      pc args strategy block sourceEq targetEq views _ _ _ state fresh
    · intro row member
      exact resolvedEntry_typesAgree base blocks pc block sourceEq sourceTypes targetTypes preserved row member
    · exact (resolvedRow_typesAgree base blocks sourceTypes targetTypes preserved
        (block.terminator, block.terminatorResultDests)
        (term_mem_graphNodes blocks pc block sourceEq)).mono
        (fun _ member => trustIrListMemAppendRight _ member)
    · intro result after afterFresh
      exact transfers depth (base.resolveBlock block) strategy result
        (resolvedRow_typesAgree base blocks sourceTypes targetTypes preserved
          (block.terminator, block.terminatorResultDests) (term_mem_graphNodes blocks pc block sourceEq))
        after afterFresh
  | expanded block names recorded suspend =>
    obtain ⟨originalNames, namesEq⟩ := planAllBlocks_traceGraphNames blocks ready pc names recorded
    obtain ⟨indexType, pointerType, stateType⟩ := typed (pc, names) recorded
    rw [← namesEq] at targetEq indexType pointerType stateType
    cases block with
    | mk params body bodyDests term termDests =>
      cases term <;> simp only [isSuspend, Bool.false_eq_true] at suspend
      exact expandedBlock_effect sourceRecurse targetRecurse base source target headers effects
        blocks _ pc originalNames sourceTypes targetTypes params body bodyDests termDests
        _ _ _ _ sourceEq targetEq indexType pointerType stateType preserved depth args strategy state fresh

end TrustIr.GenericCoro.AllBlocksLayer
