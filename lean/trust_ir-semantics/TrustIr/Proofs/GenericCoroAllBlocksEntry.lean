-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixEntryEffect

namespace TrustIr.GenericCoro.AllBlocksEntry
open Prefix

/-- The prefix-plus-macro layer at an arbitrary current block. Its input is
    any fresh SSA state, including nonempty locals carried over from earlier
    blocks. It does not require a freshly cleared function-entry frame. -/
theorem expandedPrefix_effect_fresh (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
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
    (valueState : value ≠ names.state) (state : MachineState)
    (fresh : SSAFreshFrames.FreshState state) :
    EffectRelation
      (Sem.run (do
        let _ ← Sem.fromMemoryExcept (checkFunctionItemValues
          (scopedContext base source (some sourceTypes)) (params.map (·.snd)) args)
        bindBlockParamsChecked params args
        evalBody sourceRecurse (scopedContext base source (some sourceTypes)) depth strategy rows
        let values ← suspendValues base.byteModel frame value slot next
        checkedReturn (scopedContext base source (some sourceTypes)) values) state)
      (Sem.run (do
        let _ ← Sem.fromMemoryExcept (checkFunctionItemValues
          (scopedContext base target (some targetTypes)) (params.map (·.snd)) args)
        bindBlockParamsChecked params args
        evalBody targetRecurse (scopedContext base target (some targetTypes)) depth strategy rows
        let values ← expandedValues (scopedContext base target (some targetTypes)) names frame value slot next
        checkedReturn (scopedContext base target (some targetTypes)) values)
        state) := by
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
  · exact fresh


end TrustIr.GenericCoro.AllBlocksEntry
