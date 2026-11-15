-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixEntryEffect
import TrustIr.Proofs.GenericCoroPrefixEntry
import TrustIr.Proofs.GenericCoroPrefixInduction

namespace TrustIr.GenericCoro.Prefix

/-- The selected entry's complete one-layer effect follows from actual
    graph declarations and predecessor callee effects. No prefix outcome,
    caller frame, argument validity or memory condition is assumed. -/
theorem expandedGraph_prefix_layer_effect (sourceRecurse targetRecurse : Recurse)
    (base : EvalContext) (source target : FuncId → Option EvalFunction)
    (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (header : EvalFunction) (blocks : List (BlockId × BasicBlock)) (names : GraphNames blocks)
    (sourceTypes targetTypes : LocalTypeTable)
    (params : List (ValueId × Ty)) (bodyPrefix : List Inst)
    (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int)
    (found : cfgOf blocks header.entryBlock = some {
      params := params, body := bodyPrefix, bodyResultDests := bodyDests,
      terminator := .CoroSuspend frame slot next value, terminatorResultDests := termDests })
    (indexType : targetTypes (Names.ofTriple names).index = some .I64)
    (pointerType : targetTypes (Names.ofTriple names).pointer = some .Ptr)
    (stateType : targetTypes (Names.ofTriple names).state = some .I64)
    (preserved : ∀ id ∈ graphValueIds blocks, sourceTypes id = targetTypes id) :
    SelectedEffects
      (fun ctx depth cfg pc args strategy => evalLayer sourceRecurse ctx depth cfg pc args strategy)
      (fun ctx depth cfg pc args strategy => evalLayer targetRecurse ctx depth cfg pc args strategy)
      base source target
      {header with cfg := cfgOf blocks, localTypes := some sourceTypes}
      {header with
        cfg := cfgOf (expandedGraph (Names.ofTriple names) blocks header.entryBlock),
        localTypes := some targetTypes} := by
  intro depth args strategy world
  let temps := Names.ofTriple names
  let block : BasicBlock := {
    params := params, body := bodyPrefix, bodyResultDests := bodyDests,
    terminator := .CoroSuspend frame slot next value, terminatorResultDests := termDests }
  have targetFound : cfgOf (expandedGraph temps blocks header.entryBlock) header.entryBlock =
      some (expandedEntry temps block) := by
    change cfgOf (expandFirstEntry temps header.entryBlock blocks) header.entryBlock = _
    rw [cfgOf_expandFirstEntry, found]
    rfl
  change EffectRelation
    (Sem.run (evalLayer sourceRecurse (scopedContext base source (some sourceTypes)) depth
      (cfgOf blocks) header.entryBlock args strategy) (callerWorld world))
    (Sem.run (evalLayer targetRecurse (scopedContext base target (some targetTypes)) depth
      (cfgOf (expandedGraph temps blocks header.entryBlock)) header.entryBlock args strategy)
      (callerWorld world))
  rw [evalLayer_sourceEntry_eq sourceRecurse (scopedContext base source (some sourceTypes)) depth
      (cfgOf blocks) header.entryBlock params args bodyPrefix bodyDests termDests
      frame value slot next strategy found,
    evalLayer_targetEntry_eq targetRecurse (scopedContext base target (some targetTypes)) depth
      (cfgOf (expandedGraph temps blocks header.entryBlock)) header.entryBlock
      temps params args bodyPrefix bodyDests termDests
      frame value slot next strategy targetTypes rfl indexType pointerType stateType targetFound]
  have operands := suspend_prefix_operands blocks header.entryBlock params bodyPrefix bodyDests termDests
    frame value slot next found
  have frameFree := GraphNames.different_original blocks names frame operands.1
  have valueFree := GraphNames.different_original blocks names value operands.2
  have pointerState : temps.pointer ≠ temps.state := by
    intro equality
    exact names.secondThird (congrArg ValueId.index equality)
  apply expandedPrefix_effect sourceRecurse targetRecurse base source target headers effects
    sourceTypes targetTypes _ _ params args depth strategy temps frame value slot next indexType
    pointerState frameFree.1 valueFree.1 valueFree.2.1 valueFree.2.2 world
  intro row member
  exact resolvedEntry_typesAgree base blocks header.entryBlock block found sourceTypes targetTypes
    preserved row member

end TrustIr.GenericCoro.Prefix
