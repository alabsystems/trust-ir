-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixCorrect
import TrustIr.Proofs.GenericCoroPrefixControls

namespace TrustIr.GenericCoro.PrefixProofControls

private theorem ready_contracts (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (header : EvalFunction) (blocks : List (BlockId × BasicBlock)) (expected : List Nat)
    (correct : ExpansionCorrect direct indirect header blocks
      (functionsOfExpansion direct indirect header blocks))
    (ready : Controls.preparedNames (functionsOfExpansion direct indirect header blocks) = some expected) :
    ∃ source target names,
      functionsOfExpansion direct indirect header blocks = .ok (.expanded source target names) ∧
      RunCallEquivalent source target ∧ CallEquivalent source target := by
  trustIrCompilerProof {
    cases run : functionsOfExpansion direct indirect header blocks with
    | error error => simp only [run, Controls.preparedNames] at ready
    | ok expansion =>
      cases expansion with
      | capacity source certificate => simp only [run, Controls.preparedNames] at ready
      | expanded source target names =>
        rw [run] at correct
        exact ⟨source, target, names, rfl, correct.2.2⟩
  } {
    cases run : functionsOfExpansion direct indirect header blocks with
    | error error =>
      simp only [run, Controls.preparedNames] at ready
      cases ready
    | ok expansion =>
      cases expansion with
      | capacity source certificate =>
        simp only [run, Controls.preparedNames] at ready
        cases ready
      | expanded source target names =>
        rw [run] at correct
        exact ⟨source, target, names, rfl, correct.2.2⟩
  }

/-- An inhabited application of the new theorem to the actual Copy-prefix
    factory, not just a conditional statement about an unknown ready branch. -/
theorem nonempty_copy_factory_retains_call_contract :
    ∃ source target names,
      Controls.prepared (PrefixControls.graph []) = .ok (.expanded source target names) ∧
      RunCallEquivalent source target ∧ CallEquivalent source target := by
  have correct := functionsOfExpansion_prefix_correct (fun _ => none) (fun _ => none)
    Controls.header (PrefixControls.graph [])
    [(⟨0⟩, .Ptr), (⟨1⟩, .I32), (⟨2⟩, .U64), (⟨7⟩, .U32)]
    [.Copy .I32 ⟨1⟩] [[⟨5⟩]] [] ⟨0⟩ ⟨5⟩ 0 17 rfl
  exact ready_contracts _ _ _ _ [3, 4, 6] correct rfl

def metadataCycleGraph : List (BlockId × BasicBlock) := PrefixControls.graph [] ++ [
  (⟨5⟩, {
    params := []
    body := [.Borrow ⟨90⟩]
    bodyResultDests := [[⟨90⟩]]
    terminator := .Return [⟨90⟩] })]

theorem nonempty_prefix_metadata_cycle_is_refused :
    Controls.prepared metadataCycleGraph =
      .error (.typeError "SSA types: cyclic borrow declarations") := rfl

/-- The total theorem propagates the real source error before choosing fresh
    names, while retaining the selected nonempty entry. -/
theorem nonempty_prefix_metadata_refusal_retains_contract :
    ExpansionCorrect (fun _ => none) (fun _ => none) Controls.header metadataCycleGraph
      (Controls.prepared metadataCycleGraph) :=
  functionsOfExpansion_prefix_correct _ _ _ _
    [(⟨0⟩, .Ptr), (⟨1⟩, .I32), (⟨2⟩, .U64), (⟨7⟩, .U32)]
    [.Copy .I32 ⟨1⟩] [[⟨5⟩]] [] ⟨0⟩ ⟨5⟩ 0 17 rfl

/-- Undefined yield id3 and unused raw destination4 remain reserved. This
    malformed-input control makes no validator-admission or NoUB claim. -/
def undefinedYieldGraph : List (BlockId × BasicBlock) := [
  (⟨900⟩, {
    params := [(⟨0⟩, .Ptr), (⟨1⟩, .I32), (⟨2⟩, .U64), (⟨7⟩, .U32)]
    body := [.Copy .I32 ⟨1⟩]
    bodyResultDests := [[⟨5⟩], [⟨4⟩]]
    terminator := .CoroSuspend ⟨0⟩ 0 17 ⟨3⟩ })]

theorem undefined_yield_and_unused_rows_remain_reserved :
    Controls.preparedNames (Controls.prepared undefinedYieldGraph) = some [6, 8, 9] := rfl

theorem undefined_yield_prefix_retains_complete_call_contract :
    ∃ source target names,
      Controls.prepared undefinedYieldGraph = .ok (.expanded source target names) ∧
      RunCallEquivalent source target ∧ CallEquivalent source target := by
  have correct := functionsOfExpansion_prefix_correct (fun _ => none) (fun _ => none)
    Controls.header undefinedYieldGraph
    [(⟨0⟩, .Ptr), (⟨1⟩, .I32), (⟨2⟩, .U64), (⟨7⟩, .U32)]
    [.Copy .I32 ⟨1⟩] [[⟨5⟩], [⟨4⟩]] [] ⟨0⟩ ⟨3⟩ 0 17 rfl
  exact ready_contracts _ _ _ _ [6, 8, 9] correct undefined_yield_and_unused_rows_remain_reserved

def recursiveSignature : FuncTyDef :=
  { params := [.Ptr, .I32, .U64, .U32], returns := [.I32], isVararg := false }

def recursiveHeaders (id : FuncId) : Option FuncTyDef :=
  if id == ⟨101⟩ then some recursiveSignature else none

def recursiveGraph : List (BlockId × BasicBlock) := [
  (⟨900⟩, {
    params := [(⟨0⟩, .Ptr), (⟨1⟩, .I32), (⟨2⟩, .U64), (⟨7⟩, .U32)]
    body := [.Call ⟨101⟩ [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨7⟩]]
    bodyResultDests := [[⟨5⟩]]
    terminator := .CoroSuspend ⟨0⟩ 0 17 ⟨5⟩ })]

/-- Source inference consumes the explicit original direct-call signature.
    Installing the produced pair at id101 makes this a real recursive prefix;
    the full theorem needs no recursive-callback equivalence premise. -/
theorem recursive_prefix_factory_retains_call_contract :
    ∃ source target names,
      functionsOfExpansion recursiveHeaders (fun _ => none) Controls.header recursiveGraph =
        .ok (.expanded source target names) ∧
      RunCallEquivalent source target ∧ CallEquivalent source target := by
  have correct := functionsOfExpansion_prefix_correct recursiveHeaders (fun _ => none)
    Controls.header recursiveGraph
    [(⟨0⟩, .Ptr), (⟨1⟩, .I32), (⟨2⟩, .U64), (⟨7⟩, .U32)]
    [.Call ⟨101⟩ [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨7⟩]] [[⟨5⟩]] [] ⟨0⟩ ⟨5⟩ 0 17 rfl
  exact ready_contracts _ _ _ _ [3, 4, 6] correct rfl

/-- Instantiate the ready pair's actual shared helper equality at each zero
    budget, for arbitrary caller contexts, values and strategies. -/
theorem actual_copy_pair_preserves_zero_resource_contracts :
    ∃ source target names,
      Controls.prepared (PrefixControls.graph []) = .ok (.expanded source target names) ∧
      (∀ ctx id depth values strategy,
        runCallReq (withFunction ctx id source) 0 depth id values strategy =
          runCallReq (withFunction ctx id target) 0 depth id values strategy) ∧
      (∀ ctx id fuel values strategy,
        runCallReq (withFunction ctx id source) fuel 0 id values strategy =
          runCallReq (withFunction ctx id target) fuel 0 id values strategy) := by
  obtain ⟨source, target, names, ready, calls, _⟩ := nonempty_copy_factory_retains_call_contract
  exact ⟨source, target, names, ready,
    (fun ctx id depth values strategy => calls ctx id 0 depth values strategy),
    (fun ctx id fuel values strategy => calls ctx id fuel 0 values strategy)⟩

end TrustIr.GenericCoro.PrefixProofControls
