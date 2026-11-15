-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceLayoutSession
import TrustIr.Proofs.SourceEnumOmission

namespace TrustIr.SourceLayout

/-- Original enum origins survive every actual successful query transition. -/
theorem Session.Reachable.enum_origin_invariant {source : Environment} {session : Session}
    (history : Session.Reachable source session) :
    Graph.EnumOriginInvariant (Index.ofEnvironment source)
      (uninhabitedFacts (Index.ofEnvironment source)) session.graph := by
  induction history with
  | prepared => exact prepare_enum_origin source
  | queried prior run ih =>
    have same := prior.index_eq
    have kept := Session.query_preserves_enum_origin _ _ _ _ _
      (uninhabitedFacts (Index.ofEnvironment source)) prior.invariant (by rw [same]; exact ih) run
    rw [same] at kept
    exact kept

theorem Index.enum_selected_source (source : Environment) (mode : Mode) (id : EnumId) (position : Nat)
    (selected : (if mode == .shape then (Index.ofEnvironment source).enumShapePositions
      else (Index.ofEnvironment source).enumPositions).find id.index = some position) :
    ∃ definition, (trustIrListGet? source.enums position) = some definition ∧ position < source.enums.length ∧ definition.id = id := by
  cases mode with
  | shape =>
    change (firstPositionIndex source.enums (·.id.index)).find id.index = some position at selected
    obtain ⟨definition, member, identity⟩ := firstPositionIndex_witness source.enums (·.id.index) id.index position selected
    exact ⟨definition, numbered_get _ _ _ member, numbered_position_bound _ _ _ member, congrArg EnumId.mk identity⟩
  | execution =>
    change (positionIndex source.enums (·.id.index)).find id.index = some position at selected
    obtain ⟨definition, member, identity⟩ := positionIndex_witness source.enums (·.id.index) id.index position selected
    exact ⟨definition, numbered_get _ _ _ member, numbered_position_bound _ _ _ member, congrArg EnumId.mk identity⟩

/-- Exact typed enum-root selection is retained by the existing real compiler
    witness, including witnesses carried through cached root histories. -/
theorem Session.CompiledRoot.enum_selected {source : Environment} {mode : Mode} {id : EnumId}
    {root : Nat} {graph : Graph} (origin : Session.CompiledRoot source mode (.Enum id) root graph)
    (value : Summary) (derived : NodeDerivation graph root value) :
    ∃ position, (if mode == .shape then (Index.ofEnvironment source).enumShapePositions
      else (Index.ofEnvironment source).enumPositions).find id.index = some position ∧
      root = (Index.ofEnvironment source).node mode ((Index.ofEnvironment source).enumBase + position) := by
  obtain ⟨before, history, compiled, run, extended⟩ := origin
  rw [history.index_eq] at run
  obtain ⟨position, selected, same, _graphSame⟩ := run.enum_selected graph value extended derived
  exact ⟨position, selected, same⟩

/-- Every real enum value derivation retains the original definition, exact
    mode and actual solver flags; cache provenance and graph provenance are
    both required, rather than trusting an arbitrary memo entry. -/
theorem Session.Reachable.enum_value_origin {source : Environment} {session : Session}
    (history : Session.Reachable source session) (mode : Mode) (id : EnumId) (root : Nat) (value : Summary)
    (compiled : Session.CompiledRoot source mode (.Enum id) root session.graph)
    (derived : NodeDerivation session.graph root value) :
    ∃ position definition, (trustIrListGet? source.enums position) = some definition ∧ definition.id = id ∧
      EnumOrigin (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source)) mode definition value := by
  obtain ⟨position, selected, same⟩ := compiled.enum_selected value derived
  obtain ⟨definition, row, bound, identity⟩ := Index.enum_selected_source source mode id position selected
  have safe := derived.satisfies_at history.enum_origin_invariant
  refine ⟨position, definition, row, identity, ?_⟩
  exact safe mode position definition (by simpa only [Index.ofEnvironment] using bound) row same

theorem Session.Reachable.query_enum_origin {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (mode : Mode) (id : EnumId) (value : Summary)
    (run : session.query mode (.Enum id) = .ok (value, next)) :
    ∃ position definition, (trustIrListGet? source.enums position) = some definition ∧ definition.id = id ∧
      EnumOrigin (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source)) mode definition value := by
  obtain ⟨root, compiled, derived⟩ := history.query_compilation_origin mode (.Enum id) value run
  exact (Session.Reachable.queried history run).enum_value_origin mode id root value compiled derived

theorem Session.Reachable.memo_enum_origin {source : Environment} {session : Session}
    (history : Session.Reachable source session) (bucket : Nat) (mode : Mode) (id : EnumId)
    (root : Nat) (value : Summary) (entry : (.Enum id, mode, root) ∈ (session.roots.find bucket).getD [])
    (cached : session.memo.find root = some value) :
    ∃ position definition, (trustIrListGet? source.enums position) = some definition ∧ definition.id = id ∧
      EnumOrigin (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source)) mode definition value :=
  history.enum_value_origin mode id root value (history.roots_compiled bucket _ mode root entry)
    (history.cached root value cached)

theorem query_enum_origin (source : Environment) (mode : Mode) (id : EnumId) (value : Summary)
    (run : query source mode (.Enum id) = .ok value) :
    ∃ position definition, (trustIrListGet? source.enums position) = some definition ∧ definition.id = id ∧
      EnumOrigin (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source)) mode definition value := by
  obtain ⟨next, event, _rest⟩ := query_session_derivation source mode (.Enum id) value run
  exact (Session.Reachable.prepared (source := source)).query_enum_origin mode id value event

/-- A queried enum summary's flags belong to the evaluator's exact definition
    after source-bound ID admission, not to a same-ID duplicate. -/
theorem Session.Reachable.query_enum_flags {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (ctx : EvalContext) (associated : CaptureSource source ctx)
    (admitted : enumIdsAdmitted source.enums = true) (mode : Mode) (id : EnumId) (definition : EnumDef)
    (resolved : ctx.enums id = some definition) (value : Summary) (enumeration : Enumeration)
    (present : value.enumeration = some enumeration)
    (run : session.query mode (.Enum id) = .ok (value, next)) :
    enumeration.uninhabited = definition.variants.map (fun variant =>
      variantUninhabited (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source)) variant.fields) := by
  obtain ⟨position, actual, row, identity, origin⟩ := history.query_enum_origin mode id value run
  have member := numbered_source_member source.enums actual position ((numbered_member_iff_get _ _ _).2 row)
  have same := enum_lookup_agrees_of_admission source ctx associated admitted id definition resolved actual member identity
  subst actual
  exact origin.flags enumeration present

/-- A real queried flag table cannot mark the initialized, actually accepted
    active capture as impossible. The tag/position witness is retained. -/
theorem Session.Reachable.query_enum_capture_active_flag_false {source : Environment} {session next : Session}
    (history : Session.Reachable source session) (ctx : EvalContext) (associated : CaptureSource source ctx)
    (admitted : enumIdsAdmitted source.enums = true) (mode : Mode) (id : EnumId) (definition : EnumDef)
    (resolved : ctx.enums id = some definition) (value : Summary) (enumeration : Enumeration)
    (present : value.enumeration = some enumeration)
    (run : session.query mode (.Enum id) = .ok (value, next)) (fuel : Nat) (values : List Value)
    (initialized : (Value.aggregate values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ tag payload position variant, values = tag :: payload ∧ EnumTagSelects definition tag position ∧
      (trustIrListGet? definition.variants position) = some variant ∧ (trustIrListGet? enumeration.uninhabited position) = some false := by
  trustIrCompilerProof {
    have flags := history.query_enum_flags ctx associated admitted mode id definition resolved value enumeration present run
    obtain ⟨tag, payload, position, variant, shape, selected, found, live⟩ :=
      enum_capture_active_flag_false source ctx associated id definition resolved fuel values initialized checked
    refine ⟨tag, payload, position, variant, shape, selected, found, ?_⟩
    rw [flags, List.get?_map, found]
    simp only [Option.map, live]
  } {
    have flags := history.query_enum_flags ctx associated admitted mode id definition resolved value enumeration present run
    obtain ⟨tag, payload, position, variant, shape, selected, found, live⟩ :=
      enum_capture_active_flag_false source ctx associated id definition resolved fuel values initialized checked
    refine ⟨tag, payload, position, variant, shape, selected, found, ?_⟩
    rw [flags, CompilerCompat.listGetConstructive_map, found]
    simp only [Option.map, live]
  }

theorem query_enum_capture_active_flag_false (source : Environment) (ctx : EvalContext)
    (associated : CaptureSource source ctx) (admitted : enumIdsAdmitted source.enums = true)
    (mode : Mode) (id : EnumId) (definition : EnumDef) (resolved : ctx.enums id = some definition)
    (value : Summary) (enumeration : Enumeration) (present : value.enumeration = some enumeration)
    (run : query source mode (.Enum id) = .ok value) (fuel : Nat) (values : List Value)
    (initialized : (Value.aggregate values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ tag payload position variant, values = tag :: payload ∧ EnumTagSelects definition tag position ∧
      (trustIrListGet? definition.variants position) = some variant ∧ (trustIrListGet? enumeration.uninhabited position) = some false := by
  obtain ⟨next, event, _rest⟩ := query_session_derivation source mode (.Enum id) value run
  exact (Session.Reachable.prepared (source := source)).query_enum_capture_active_flag_false ctx associated admitted
    mode id definition resolved value enumeration present event fuel values initialized checked


end TrustIr.SourceLayout

namespace TrustIr.SourceLayout.EnumGraphControls

private def definition : EnumDef :=
  { id := ⟨0⟩, name := "TwoLive", variants := [{ name := "A", fields := [] }, { name := "B", fields := [] }] }
private def source : Environment := { enums := [definition] }
private def info : Enumeration :=
  { tag := .u8, discriminants := [0, 1], encoding := .direct 0, variants := [[], []], uninhabited := [true, false] }
private def forged : Summary := { size := 1, align := some 1, enumeration := some info }

theorem forged_flags_pass_metadata : EnumMetadata forged := by
  intro enumeration present
  cases present
  exact ⟨rfl, rfl, .cons (by decide) (.cons (by decide) .nil), rfl⟩

theorem forged_flags_have_no_source_origin (mode : Mode) :
    ¬ EnumOrigin (Index.ofEnvironment source) (uninhabitedFacts (Index.ofEnvironment source)) mode definition forged := by
  intro origin
  have flags := origin.flags info rfl
  change [true, false] = [false, false] at flags
  have impossible := (List.cons.inj flags).1
  cases impossible

private def forgedGraph : Graph :=
  { count := 4, nodes := NatIndexTree.empty.insert 1 (.done (.ok forged)) }

theorem raw_forged_graph_derives : NodeDerivation forgedGraph 1 forged :=
  .equation (equation := Equation.done (.ok forged))
    (by simp [forgedGraph, NatIndexTree.find_insert]) rfl (.nil _) rfl

theorem forged_graph_fails_origin_invariant :
    ¬ Graph.EnumOriginInvariant (Index.ofEnvironment source)
      (uninhabitedFacts (Index.ofEnvironment source)) forgedGraph := by
  intro safe
  have origin := raw_forged_graph_derives.satisfies_at safe
  exact forged_flags_have_no_source_origin .execution (origin .execution 0 definition (by decide) rfl rfl)

private def forgedMemo : Memo := NatIndexTree.empty.insert 1 forged

theorem raw_forged_memo_is_returned :
    solve (prepare source).graph .empty 1 forgedMemo = .ok (forged, forgedMemo) := by
  apply solve_cached
  simp [forgedMemo, NatIndexTree.find_insert]

theorem forged_memo_has_no_derivation : ¬ MemoDerivation (prepare source).graph forgedMemo := by
  intro valid
  have derived := valid 1 forged (by simp [forgedMemo, NatIndexTree.find_insert])
  have origin := derived.satisfies_at (prepare_enum_origin source)
  exact forged_flags_have_no_source_origin .execution (origin .execution 0 definition (by decide) rfl rfl)

private def first : EnumDef := { definition with id := ⟨1⟩, name := "First" }
private def other : EnumDef :=
  { first with name := "Matching", variants := [{ name := "Never", fields := [.Never] }, { name := "Unit", fields := [] }] }
private def duplicates : Environment := { source with enums := [first, other] }

theorem shape_selects_original_first : (Index.ofEnvironment duplicates).enumShapePositions.find 1 = some 0 := rfl

theorem execution_selects_original_matching : (Index.ofEnvironment duplicates).enumPositions.find 1 = some 1 := rfl

theorem duplicate_shape_position_witness :
    ∃ row, (trustIrListGet? duplicates.enums 0) = some row ∧ 0 < duplicates.enums.length ∧ row.id = ⟨1⟩ :=
  Index.enum_selected_source duplicates .shape ⟨1⟩ 0 shape_selects_original_first

theorem duplicate_execution_position_witness :
    ∃ row, (trustIrListGet? duplicates.enums 1) = some row ∧ 1 < duplicates.enums.length ∧ row.id = ⟨1⟩ :=
  Index.enum_selected_source duplicates .execution ⟨1⟩ 1 execution_selects_original_matching

end TrustIr.SourceLayout.EnumGraphControls
