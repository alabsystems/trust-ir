-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceLayoutSession

namespace TrustIr.SourceLayout

/-- Original struct origins survive every actual successful query transition. -/
theorem Session.Reachable.struct_origin_invariant {source : Environment} {session : Session}
    (history : Session.Reachable source session) :
    Graph.StructOriginInvariant (Index.ofEnvironment source) session.graph := by
  induction history with
  | prepared => exact prepare_struct_origin source
  | queried prior run ih =>
    have same := prior.index_eq
    have kept := Session.query_preserves_struct_origin _ _ _ _ _
      prior.invariant (by rw [same]; exact ih) run
    rw [same] at kept
    exact kept

/-- Exact typed struct-root selection is retained by the existing real compiler
    witness, including witnesses carried through cached root histories. -/
theorem Session.CompiledRoot.struct_selected {source : Environment} {mode : Mode} {id : StructId}
    {root : Nat} {graph : Graph} (origin : Session.CompiledRoot source mode (.Struct id) root graph)
    (value : Summary) (derived : NodeDerivation graph root value) :
    ∃ position, (if mode == .shape then (Index.ofEnvironment source).structShapePositions
      else (Index.ofEnvironment source).structPositions).find id.index = some position ∧
      root = (Index.ofEnvironment source).node mode ((Index.ofEnvironment source).structBase + position) := by
  obtain ⟨before, history, compiled, run, extended⟩ := origin
  rw [history.index_eq] at run
  obtain ⟨position, selected, same, _graphSame⟩ := run.struct_selected graph value extended derived
  exact ⟨position, selected, same⟩

/-- Actual struct queries authenticate the exact selected physical source
    row and its complete logical field type sequence. -/
theorem Session.Reachable.struct_value_origin {source : Environment} {session : Session}
    (history : Session.Reachable source session) (mode : Mode) (id : StructId) (root : Nat) (value : Summary)
    (compiled : Session.CompiledRoot source mode (.Struct id) root session.graph)
    (derived : NodeDerivation session.graph root value) :
    ∃ position definition,
      (if mode == .shape then (Index.ofEnvironment source).structShapePositions
        else (Index.ofEnvironment source).structPositions).find id.index = some position ∧
      (trustIrListGet? source.structs position) = some definition ∧ definition.id = id ∧
      value.fields.map (·.ty) = definition.fields.map (·.ty) := by
  obtain ⟨position, selected, same⟩ := compiled.struct_selected value derived
  obtain ⟨definition, row, bound, identity⟩ := Index.struct_selected_source source mode id position selected
  have safe := derived.satisfies_at history.struct_origin_invariant
  refine ⟨position, definition, selected, row, identity, ?_⟩
  exact safe mode position definition (by simpa only [Index.ofEnvironment] using bound) row same

theorem Session.Reachable.query_struct_origin {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (mode : Mode) (id : StructId) (value : Summary)
    (run : session.query mode (.Struct id) = .ok (value, next)) :
    ∃ position definition,
      (if mode == .shape then (Index.ofEnvironment source).structShapePositions
        else (Index.ofEnvironment source).structPositions).find id.index = some position ∧
      (trustIrListGet? source.structs position) = some definition ∧ definition.id = id ∧
      value.fields.map (·.ty) = definition.fields.map (·.ty) := by
  obtain ⟨root, compiled, derived⟩ := history.query_compilation_origin mode (.Struct id) value run
  exact (Session.Reachable.queried history run).struct_value_origin mode id root value compiled derived

end TrustIr.SourceLayout
