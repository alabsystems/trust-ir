-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixBodyFresh
import TrustIr.Proofs.GenericCoroPrefixLayerEq

namespace TrustIr.GenericCoro.Prefix

/-- A source entry's resolved body only reads declarations belonging to its
    original graph. Resolution does not add operand identifiers. -/
theorem resolvedEntry_typesAgree (base : EvalContext)
    (blocks : List (BlockId × BasicBlock)) (entry : BlockId) (block : BasicBlock)
    (found : cfgOf blocks entry = some block) (source target : LocalTypeTable)
    (same : ∀ id ∈ graphValueIds blocks, source id = target id)
    (row : Inst × List ValueId)
    (member : row ∈ bodyInstsWithResultDests (base.resolveBlock block).body
      (base.resolveBlock block).bodyResultDests) :
    TypesAgreeOn (row.2 ++ operandIds row.1) (some source) (some target) := by
  change row ∈ bodyInstsWithResultDests (block.body.map base.resolveDrop) block.bodyResultDests at member
  rw [bodyInsts_resolve] at member
  obtain ⟨original, originalMember, equality⟩ := List.mem_map.mp member
  subst row
  exact resolvedRow_typesAgree base blocks source target same original
    (entry_body_mem_graphNodes blocks entry block found original originalMember)

/-- Arbitrary prefix errors are retained verbatim. On success, the actual
    prefix freshness theorem supplies the only invariant used by the macro. -/
theorem effect_after_fresh_prefix (first : Sem Unit) (source target : Sem (List Value))
    (firstFresh : SSAFreshStep.KeepsFresh first)
    (tails : ∀ state, SSAFreshFrames.FreshState state →
      EffectRelation (Sem.run source state) (Sem.run target state))
    (state : MachineState) (fresh : SSAFreshFrames.FreshState state) :
    EffectRelation (Sem.run (do first; source) state) (Sem.run (do first; target) state) := by
  simp only [Sem.run_bind]
  cases ran : Sem.run first state with
  | error error => exact .error error
  | ok result =>
    rcases result with ⟨unit, after⟩
    cases unit
    exact tails after (firstFresh state ((), after) fresh ran)

theorem suspend_prefix_operands (blocks : List (BlockId × BasicBlock)) (entry : BlockId)
    (params : List (ValueId × Ty)) (bodyPrefix : List Inst)
    (bodyDests : List (List ValueId)) (termDests : List ValueId)
    (frame value : ValueId) (slot : Nat) (next : Int)
    (found : cfgOf blocks entry = some {
      params := params, body := bodyPrefix, bodyResultDests := bodyDests,
      terminator := .CoroSuspend frame slot next value, terminatorResultDests := termDests }) :
    frame ∈ graphValueIds blocks ∧ value ∈ graphValueIds blocks := by
  obtain ⟨before, selectedId, after, decomposition, selected, noMatch⟩ :=
    cfgOf_decompose blocks entry _ found
  have termMember : (.CoroSuspend frame slot next value, termDests) ∈ graphNodes blocks := by
    rw [decomposition, graphNodes_append, graphNodes_cons]
    exact trustIrListMemAppendRight _
      (trustIrListMemAppendLeft _ (trustIrListMemAppendRight _ ((trustIrListMemConsSelf _ _))))
  constructor
  · exact graphNode_ids blocks _ termMember frame
      (trustIrListMemAppendRight _ ((trustIrListMemConsSelf _ _)))
  · exact graphNode_ids blocks _ termMember value
      (trustIrListMemAppendRight _ (List.mem_cons_of_mem _ ((trustIrListMemConsSelf _ _))))

/-- Complete prefix-plus-macro simulation. The prefix's declaration
    agreement and all generated-id exclusions are supplied from the actual
    source/expanded graph in the entry theorem below. -/
theorem expandedPrefix_effect (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (sourceTypes targetTypes : LocalTypeTable) (rows : List (Inst × List ValueId))
    (rowTypes : ∀ row ∈ rows,
      TypesAgreeOn (row.2 ++ operandIds row.1) (some sourceTypes) (some targetTypes))
    (params : List (ValueId × Ty)) (args : List Value) (depth : Nat) (strategy : PanicStrategy)
    (names : Names) (frame value : ValueId) (slot : Nat) (next : Int)
    (indexType : targetTypes names.index = some .I64)
    (pointerState : names.pointer ≠ names.state) (frameIndex : frame ≠ names.index)
    (valueIndex : value ≠ names.index) (valuePointer : value ≠ names.pointer)
    (valueState : value ≠ names.state) (world : MachineState) :
    EffectRelation
      (Sem.run (do
        let _ ← Sem.fromMemoryExcept (checkFunctionItemValues
          (scopedContext base source (some sourceTypes)) (params.map (·.snd)) args)
        bindBlockParamsChecked params args
        evalBody sourceRecurse (scopedContext base source (some sourceTypes)) depth strategy rows
        let values ← suspendValues base.byteModel frame value slot next
        checkedReturn (scopedContext base source (some sourceTypes)) values) (callerWorld world))
      (Sem.run (do
        let _ ← Sem.fromMemoryExcept (checkFunctionItemValues
          (scopedContext base target (some targetTypes)) (params.map (·.snd)) args)
        bindBlockParamsChecked params args
        evalBody targetRecurse (scopedContext base target (some targetTypes)) depth strategy rows
        let values ← expandedValues (scopedContext base target (some targetTypes)) names frame value slot next
        checkedReturn (scopedContext base target (some targetTypes)) values)
        (callerWorld world)) := by
  rw [evalBody_congrOn sourceRecurse targetRecurse base source target headers effects
    (some sourceTypes) (some targetTypes) depth strategy rows rowTypes]
  have paramsFresh : SSAFreshStep.KeepsFresh (bindBlockParamsChecked params args) := by
    intro state result fresh ran
    rcases result with ⟨unit, after⟩
    cases unit
    exact SSAFreshFrames.bindBlockParamsChecked_preserves_fresh params args state after fresh ran
  have checks := itemValues_constantContext
    (scopedContext base source (some sourceTypes))
    (scopedContext base target (some targetTypes)) rfl (params.map (·.snd)) args
  have returns (values : List Value) := checkedReturn_congr
    (scopedContext base source (some sourceTypes))
    (scopedContext base target (some targetTypes)) rfl rfl values
  simp only [checks, returns]
  apply effect_after_fresh_prefix _ _ _ (SSAFreshMemory.fromMemoryExcept_fresh _)
  · intro afterCheck checkFresh
    apply effect_after_fresh_prefix _ _ _ paramsFresh
    · intro afterParams paramsFresh
      apply effect_after_fresh_prefix _ _ _ (evalBody_fresh _ _ _ _ _)
      · intro afterBody bodyFresh
        apply checkedReturn_effect
        exact expandedValues_effect (scopedContext base target (some targetTypes)) targetTypes
          names frame value slot next rfl indexType pointerState frameIndex valueIndex
          valuePointer valueState afterBody bodyFresh
      · exact paramsFresh
    · exact checkFresh
  · exact SSAFreshFrames.cleared_fresh world

end TrustIr.GenericCoro.Prefix
