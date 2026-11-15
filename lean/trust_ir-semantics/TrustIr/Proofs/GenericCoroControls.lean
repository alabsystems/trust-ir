-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroProps

namespace TrustIr.GenericCoro.Controls

def header : EvalFunction := {
  body := {paramTys := [.Ptr, .I32, .U64, .U32], returnTys := [.I32]}
  cfg := fun _ => none
  entryBlock := ⟨900⟩ }

/-- The four-parameter graph used by the validated cold-codec Rust corpus.
    The unused fourth parameter must still reserve its source id. -/
def graph (frame value extra : Nat) : List (BlockId × BasicBlock) := [
  (⟨900⟩, {
    params := [(⟨frame⟩, .Ptr), (⟨value⟩, .I32), (⟨extra⟩, .U64), (⟨7⟩, .U32)]
    body := []
    terminator := .CoroSuspend ⟨frame⟩ 0 17 ⟨value⟩})]

def prepared (blocks : List (BlockId × BasicBlock)) :=
  functionsOfExpansion (fun _ => none) (fun _ => none) header blocks

def preparedNames {blocks : List (BlockId × BasicBlock)} :
    Except SemError (FunctionExpansion blocks) → Option (List Nat)
  | .ok (.expanded _ _ names) => some [names.first, names.second, names.third]
  | _ => none

theorem dense_graph_uses_actual_gaps :
    preparedNames (prepared (graph 0 1 2)) = some [3, 4, 5] := by rfl

theorem sparse_graph_uses_low_gaps :
    preparedNames (prepared (graph 42 65537 0)) = some [1, 2, 3] := by rfl

theorem maximum_u32_graph_stays_serializable :
    preparedNames (prepared (graph (2 ^ 32 - 1) 0 2)) = some [1, 3, 4] := by rfl

/-- A ground, inhabited application of the complete generic theorem. The
    maximum source id does not turn the result into a capacity/error branch. -/
theorem maximum_u32_actual_call_equivalence :
    ∃ source target names,
      prepared (graph (2 ^ 32 - 1) 0 2) = .ok (.expanded source target names) ∧
      RunCallEquivalent source target ∧ CallEquivalent source target := by
  trustIrCompilerProof {
    have correct := functionsOfExpansion_correct (fun _ => none) (fun _ => none) header
      (graph (2 ^ 32 - 1) 0 2) [(⟨2 ^ 32 - 1⟩, .Ptr), (⟨0⟩, .I32), (⟨2⟩, .U64), (⟨7⟩, .U32)]
        [] [] ⟨2 ^ 32 - 1⟩ ⟨0⟩ 0 17 rfl
    have ready := maximum_u32_graph_stays_serializable
    cases run : prepared (graph (2 ^ 32 - 1) 0 2) with
    | error error => simp only [run, preparedNames] at ready
    | ok expansion =>
      cases expansion with
      | capacity source certificate => simp only [run, preparedNames] at ready
      | expanded source target names =>
        change ExpansionCorrect _ _ _ _ (prepared (graph (2 ^ 32 - 1) 0 2)) at correct
        rw [run] at correct
        exact ⟨source, target, names, rfl, correct.2.2⟩
  } {
    have correct := functionsOfExpansion_correct (fun _ => none) (fun _ => none) header
      (graph (2 ^ 32 - 1) 0 2) [(⟨2 ^ 32 - 1⟩, .Ptr), (⟨0⟩, .I32), (⟨2⟩, .U64), (⟨7⟩, .U32)]
        [] [] ⟨2 ^ 32 - 1⟩ ⟨0⟩ 0 17 rfl
    have ready := maximum_u32_graph_stays_serializable
    cases run : prepared (graph (2 ^ 32 - 1) 0 2) with
    | error error =>
      simp only [run, preparedNames] at ready
      cases ready
    | ok expansion =>
      cases expansion with
      | capacity source certificate =>
        simp only [run, preparedNames] at ready
        cases ready
      | expanded source target names =>
        change ExpansionCorrect _ _ _ _ (prepared (graph (2 ^ 32 - 1) 0 2)) at correct
        rw [run] at correct
        exact ⟨source, target, names, rfl, correct.2.2⟩
  }

/-- The formal graph domain also includes malformed/unvisited source rows.
    This is a reservation control, not a validator-admission claim: Rust
    refuses the unreachable block while the total theorem still accounts for
    its declarations and all original lookup behavior. -/
def unvisitedGraph : List (BlockId × BasicBlock) :=
  (⟨2⟩, {params := [(⟨3⟩, .I32)], body := [], terminator := .Return [⟨3⟩]}) :: graph 0 1 2

theorem unvisited_rows_reserve_identifiers :
    preparedNames (prepared unvisitedGraph) = some [4, 5, 6] := by rfl

/-- Raw destination rows unused by the empty source body still reserve ids.
    In particular the missing yield id zero can never become a new alias. -/
def missingYieldGraph : List (BlockId × BasicBlock) := [
  (⟨900⟩, {
    params := [(⟨42⟩, .Ptr)]
    body := []
    bodyResultDests := [[⟨0⟩], [⟨2⟩], [⟨3⟩]]
    terminator := .CoroSuspend ⟨42⟩ 0 17 ⟨0⟩})]

def missingHeader : EvalFunction :=
  {header with body := {paramTys := [.Ptr], returnTys := [.I32]}}

def missingPrepared := functionsOfExpansion (fun _ => none) (fun _ => none) missingHeader missingYieldGraph

theorem undeclared_yield_and_unused_rows_are_reserved :
    preparedNames missingPrepared = some [1, 4, 5] := by rfl

theorem missing_yield_retains_complete_call_contract :
    ExpansionCorrect (fun _ => none) (fun _ => none) missingHeader missingYieldGraph missingPrepared :=
  functionsOfExpansion_correct _ _ _ _ [(⟨42⟩, .Ptr)] [[⟨0⟩], [⟨2⟩], [⟨3⟩]] [] ⟨42⟩ ⟨0⟩ 0 17 rfl

def cyclicMetadataGraph : List (BlockId × BasicBlock) := [
  (⟨900⟩, {
    params := [(⟨42⟩, .Ptr), (⟨0⟩, .I32)]
    body := []
    terminator := .CoroSuspend ⟨42⟩ 0 17 ⟨0⟩}),
  (⟨5⟩, {
    params := []
    body := [.Borrow ⟨5⟩]
    bodyResultDests := [[⟨5⟩]]
    terminator := .Return [⟨5⟩]})]

theorem source_metadata_cycle_is_propagated :
    ExpansionCorrect (fun _ => none) (fun _ => none) header cyclicMetadataGraph
      (prepared cyclicMetadataGraph) :=
  functionsOfExpansion_correct _ _ _ _ [(⟨42⟩, .Ptr), (⟨0⟩, .I32)] [] [] ⟨42⟩ ⟨0⟩ 0 17 rfl

theorem cyclic_metadata_refuses_before_expansion :
    prepared cyclicMetadataGraph = .error (.typeError "SSA types: cyclic borrow declarations") := by rfl

theorem zero_block_fuel_precedes_missing_cfg (ctx : EvalContext) (state : MachineState) :
    Sem.run (stepNWithContext ctx 0 0 (fun _ => none) ⟨0⟩ [] .unwind) state =
      .error .outOfFuel := by rfl

theorem zero_depth_preserves_parameter_arity_error (ctx : EvalContext) (state : MachineState) :
    Sem.run (stepNWithContext ctx 1 0 (fun _ => some {
      params := [(⟨0⟩, .I32)]
      body := []
      terminator := .Call ⟨0⟩ [⟨0⟩] }) ⟨0⟩ [] .unwind) state =
      .error (.typeError "block parameter count mismatch: expected 1, got 0") := by
  trustIrCompilerProof {
    rfl
  } {
    trustIrReduce
  }

theorem zero_depth_preserves_undefined_argument (ctx : EvalContext) (state : MachineState) :
    Sem.run (stepNWithContext ctx 1 0 (fun _ => some {
      params := []
      body := []
      terminator := .Call ⟨0⟩ [⟨0⟩] }) ⟨0⟩ [] .unwind) (callerWorld state) =
      .error (.typeError s!"undefined SSA value: {repr (ValueId.mk 0)}") := by rfl

theorem zero_depth_precedes_callee_lookup (ctx : EvalContext) (state : MachineState) :
    Sem.run (stepNWithContext ctx 1 0 (fun _ => some {
      params := []
      body := []
      terminator := .Call ⟨0⟩ [] }) ⟨0⟩ [] .unwind) state = .error .outOfFuel := by rfl

end TrustIr.GenericCoro.Controls
