-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Service

run_cmd do
  if Lean.versionString == "4.30.0-rc2" then
    let env ← Lean.getEnv
    let mut registered := 0
    for (n, _) in env.constants.map₁.toList do
      if n.toString.endsWith "TrustIr.SourceLayout.compileTy.eq_def" ||
         n.toString.endsWith "TrustIr.SourceLayout.compileTypes.eq_def" then
        Lean.Elab.Command.elabCommand (← `(command| attribute [local cbv_eval] $(Lean.mkIdent n):ident))
        registered := registered + 1
    unless registered == 2 do
      Lean.throwError "expected the two original layout compiler equations"
  else if Lean.versionString != "4.8.0" then
    Lean.throwError "unsupported compiler for layout equation reduction"

namespace TrustIr.SourceLayoutProps
open SourceLayout

private def view (result : Result Summary) : Option (Nat × Option Nat × List Nat) :=
  match result with
  | .ok value => some (value.size, value.align, value.fields.map (·.offset))
  | .error _ => none

private def source : Environment := { hasTargetInfo := true }

/-- Source-owned physical order is retained rather than recomputed. -/
def reordered : Environment :=
  { source with structs := [{ id := ⟨7⟩, name := "Mixed", fields := [{ name := "a", ty := .U8, offset := some 8 }, { name := "b", ty := .U64, offset := some 0 }, { name := "c", ty := .U8, offset := some 9 }], size := some 16, align := some 8 }] }

theorem pointer32 : view (query { source with model := .le32 } .execution .Ptr) = some (4, some 4, []) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem pointer64 : view (query source .shape .Ptr) = some (8, some 8, []) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem pointer_cuts_nominal_cycle :
    view (query source .shape (.PtrConst (.Struct ⟨999⟩))) = some (8, some 8, []) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem reordered_offsets : view (query reordered .execution (.Struct ⟨7⟩)) =
    some (16, some 8, [8, 0, 9]) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem source_never_has_no_alignment : view (query source .shape .Never) = some (0, none, []) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem execution_never_refuses : view (query source .execution .Never) = none := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

/-- The source service recognizes an actual declared closure frame, while
    direct executable byte-layout admission remains a separate refusal. -/
def closureSource : Environment :=
  { source with closures := [{ func := ⟨0⟩, captures := [.U8, .U64, .U8] }], closureLayouts := [{ closure := ⟨0⟩, size := 16, align := 8, captureOffsets := [8, 0, 9] }] }

theorem closure_source_offsets : view (query closureSource .shape (.Closure ⟨0⟩)) =
    some (16, some 8, [8, 0, 9]) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem closure_execution_refuses : view (query closureSource .execution (.Closure ⟨0⟩)) = none := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private def tuple : Ty := .Tuple [.U8, .U64, .U8]

theorem tuple_without_descriptor_is_not_source_layout : view (query source .shape tuple) = none := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem tuple_without_descriptor_execution_canonical :
    view (query source .execution tuple) = some (24, some 8, [0, 8, 16]) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private def closureTuple : Environment :=
  { closureSource with types := [some (.Tuple [.Closure ⟨0⟩])], tupleLayouts := [{ tupleType := ⟨0⟩, size := 16, align := 8, fieldOffsets := [0] }] }

theorem global_tuple_rows_follow_closure_frames :
    view (query closureTuple .execution (.Tuple [])) = some (0, some 1, []) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem declared_tuple_summary_does_not_admit_a_closure_codec :
    view (query closureTuple .execution (.Tuple [.Closure ⟨0⟩])) = some (16, some 8, [0]) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private def invalidClosureTuple : Environment :=
  { closureTuple with closureLayouts := [{ closure := ⟨0⟩, size := 16, align := 8, captureOffsets := [0] }] }

theorem unused_bad_closure_dependency_refuses_tuple_execution :
    view (query invalidClosureTuple .execution (.Tuple [])) = none := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem unrelated_pointer_ignores_bad_closure_dependency :
    view (query invalidClosureTuple .execution .Ptr) = some (8, some 8, []) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private def canonicalStruct : Environment :=
  { source with structs := [{ id := ⟨0⟩, name := "Legacy", fields := [{ name := "a", ty := .U8, offset := none }, { name := "b", ty := .U64, offset := none }, { name := "c", ty := .U8, offset := none }], size := none, align := none }] }

theorem struct_without_metadata_is_not_source_layout :
    view (query canonicalStruct .shape (.Struct ⟨0⟩)) = none := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem struct_without_metadata_execution_canonical :
    view (query canonicalStruct .execution (.Struct ⟨0⟩)) = some (24, some 8, [0, 8, 16]) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private def partialStruct : Environment :=
  { source with structs := [{ id := ⟨0⟩, name := "Partial", fields := [], size := some 8, align := none }] }

theorem partial_struct_metadata_refuses : view (query partialStruct .execution (.Struct ⟨0⟩)) = none := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private def packed : Environment :=
  { source with structs := [{ id := ⟨0⟩, name := "Packed", fields := [{ name := "a", ty := .U8, offset := some 0 }, { name := "b", ty := .U64, offset := some 1 }], size := some 9, align := some 1, repr := .packed 1 }] }

theorem packed_field_alignment_is_clamped : view (query packed .shape (.Struct ⟨0⟩)) =
    some (9, some 1, [0, 1]) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private def cycle : Environment := { source with types := [some (.Array ⟨0⟩ 0)] }

theorem zero_array_still_resolves_its_cycle : view (query cycle .execution (.Array ⟨0⟩ 0)) = none := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private def uninhabited (source : Environment) (ty : Ty) : Bool :=
  let index := Index.ofEnvironment source
  (inhabitFormula index ty).holds (uninhabitedFacts index)

theorem inhabit_cycle_is_not_a_proof :
    uninhabited { source with types := [some (.Array ⟨0⟩ 1)] } (.Array ⟨0⟩ 1) = false := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem inhabit_cycle_with_never_has_a_finite_witness :
    uninhabited { source with types := [some (.Tuple [.Array ⟨0⟩ 1, .Never])] } (.Array ⟨0⟩ 1) = true := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem empty_array_of_never_is_inhabited :
    uninhabited { source with types := [some .Never] } (.Array ⟨0⟩ 0) = false := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private def duplicateDefinitions : Environment :=
  { source with structs := [{ id := ⟨0⟩, name := "Never", fields := [{ name := "f", ty := .Never, offset := none }], size := none, align := none }, { id := ⟨0⟩, name := "Unit", fields := [], size := none, align := none }] }

theorem inhabit_requires_every_duplicate_definition :
    uninhabited duplicateDefinitions (.Struct ⟨0⟩) = false := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private def collidingTuples : Environment :=
  { source with types := [some (.Tuple [.FatPtr .Str]), some (.Tuple [.FatPtr (.Slice ⟨0⟩)])], tupleLayouts := [{ tupleType := ⟨0⟩, size := 16, align := 8, fieldOffsets := [0] }, { tupleType := ⟨1⟩, size := 24, align := 8, fieldOffsets := [8] }] }

theorem colliding_buckets_still_check_actual_source_identity :
    (TupleIndex.ofRows collidingTuples.types.toArray collidingTuples.tupleLayouts).lookup
      (.Tuple [.FatPtr (.Slice ⟨0⟩)]) =
      .ok (some { tupleType := ⟨1⟩, size := 24, align := 8, fieldOffsets := [8] }) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem noncanonical_execution_refuses_before_layout :
    view (query { source with model := .le32, canonicalScalars := false } .execution .Ptr) = none := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private def repeatedGraphSize : Option Bool := do
  let (_, first) ← ((prepare source).query .execution .Ptr).toOption
  let (_, second) ← (first.query .execution .Ptr).toOption
  pure (first.graph.count == second.graph.count)

theorem repeated_roots_share_the_prepared_graph : repeatedGraphSize = some true := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private def canonicalVariant : Summary :=
  { size := 4, align := some 2, fields := [{ ty := .U8, offset := 0, size := 1, align := 1 }, { ty := .U16, offset := 2, size := 2, align := 2 }] }

/-- Canonical variant fields start at the aligned payload, not at their
    relative per-variant offsets. This exercises the actual assembly rule. -/
theorem canonical_enum_assembly_uses_absolute_offsets :
    (placePayload 2 [{ size := 0, align := some 1 }, canonicalVariant]).map
      (fun fields => fields.map (·.offset)) = [[], [2, 4]] := rfl

/-- An empty nominal declaration is retained as the impossible source child. -/
private def emptyNominal : EnumDef := { id := ⟨1⟩, name := "Empty", variants := [] }
private def singleDefinition : EnumDef :=
  { id := ⟨0⟩, name := "Single", variants := [
      { name := "Impossible", fields := [.Enum ⟨1⟩], fieldNames := ["retained"] },
      { name := "Active", fields := [.U32], fieldNames := ["word"] }],
    discriminants := [some 7, some 23],
    layout := some { encoding := .singleInhabited 1, size := 4, align := 4, variantFieldOffsets := [[], [0]] } }
private def singleSource (definition : EnumDef := singleDefinition) : Environment :=
  { source with enums := [definition, emptyNominal] }
private def enumView (result : Result Summary) :=
  result.toOption.bind (fun value => value.enumeration.map (fun e =>
    (value.size, value.align, e.discriminants, e.variants.map (fun row => row.map (·.offset)), e.uninhabited)))

theorem single_inhabited_skips_only_proven_impossible_physical_children :
    enumView (query (singleSource) .execution (.Enum ⟨0⟩)) =
      some (4, some 4, [7, 23], [[], [0]], [true, false]) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem single_inhabited_keeps_all_logical_source_rows :
    singleDefinition.variants.map (fun row => (row.fields, row.fieldNames)) =
      [([.Enum ⟨1⟩], ["retained"]), ([.U32], ["word"])] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem empty_nominal_has_no_canonical_tag : canonicalTag emptyNominal = none := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem empty_nominal_has_no_shape_or_execution_layout :
    view (query (singleSource) .shape (.Enum ⟨1⟩)) = none ∧
    view (query (singleSource) .execution (.Enum ⟨1⟩)) = none := by
  trustIrCompilerProof {
    exact ⟨rfl, rfl⟩
  } {
    exact ⟨(by trustIrReduce), (by trustIrReduce)⟩
  }

private def withEncoding (encoding : EnumTagEncoding) : EnumDef :=
  { singleDefinition with layout := singleDefinition.layout.map (fun descriptor => { descriptor with encoding }) }

private def untaggedTwoLive : EnumDef :=
  { (withEncoding .untagged) with variants := [{ name := "Unit", fields := [] },
      { name := "Word", fields := [.U32] }] }

/-- Both rows have valid physical layouts: only the v37 declared-count rule
    refuses this descriptor, independently of impossible-child layout refusal. -/
theorem v37_untagged_still_requires_one_declared_variant :
    view (query { source with enums := [untaggedTwoLive] } .execution (.Enum ⟨0⟩)) = none := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem single_inhabited_missing_selected_row_refuses :
    view (query (singleSource (withEncoding (.singleInhabited 2))) .execution (.Enum ⟨0⟩)) = none := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private def bothInhabited : EnumDef :=
  { singleDefinition with variants := [{ name := "AlsoLive", fields := [] },
      { name := "Active", fields := [.U32] }] }
theorem single_inhabited_live_inactive_row_refuses :
    view (query (singleSource bothInhabited) .execution (.Enum ⟨0⟩)) = none := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private def inactiveOffset : EnumDef :=
  { singleDefinition with layout := some { encoding := .singleInhabited 1, size := 4, align := 4, variantFieldOffsets := [[0], [0]] } }
theorem single_inhabited_nonempty_inactive_offsets_refuse :
    view (query (singleSource inactiveOffset) .execution (.Enum ⟨0⟩)) = none := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

/-- This checks the early predicate itself, so a later child-layout error
    cannot accidentally stand in for checking inactive physical rows. -/
theorem single_inhabited_inactive_offsets_fail_before_child_skipping :
    singleInhabitedValid inactiveOffset
      { encoding := .singleInhabited 1, size := 4, align := 4, variantFieldOffsets := [[0], [0]] }
      [true, false] 1 = false := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private def selectedImpossible : EnumDef :=
  { singleDefinition with variants := [{ name := "Dead0", fields := [.Never] },
      { name := "Dead1", fields := [.Never] }] }
/-- The actual field rules prove both Never rows impossible for EVERY source
    index/fact context. The early selector guard therefore always rejects,
    independently of physical-child traversal or graph normalization. -/
theorem single_inhabited_selected_never_has_no_eligibility
    (index : Index) (facts : NatIndexTree Unit) :
    singleInhabitedValid selectedImpossible
      { encoding := .singleInhabited 1, size := 4, align := 4, variantFieldOffsets := [[], [0]] }
      (selectedImpossible.variants.map (fun row => variantUninhabited index facts row.fields))
      1 = false := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

namespace DuplicateSelectionControls

private def neverRow : StructDef :=
  { id := ⟨1⟩, name := "FirstNever", fields := [{ name := "empty", ty := .Never, offset := none }], size := none, align := none }

private def unitRow : StructDef :=
  { id := ⟨1⟩, name := "MatchingUnit", fields := [], size := none, align := none }

private def duplicates : Environment := { source with structs := [neverRow, unitRow] }

theorem shape_uses_first :
    (Index.ofEnvironment duplicates).structShapePositions.find 1 = some 0 := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem execution_uses_matching_position :
    (Index.ofEnvironment duplicates).structPositions.find 1 = some 1 := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem group_retains_both_in_source_order :
    ((Index.ofEnvironment duplicates).structDefinitions.find 1).getD [] =
      [neverRow, unitRow] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem first_rule_alone_is_enabled :
    variantUninhabited (Index.ofEnvironment duplicates) .empty (neverRow.fields.map (·.ty)) = true := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem actual_solver_requires_the_other_definition :
    uninhabited duplicates (.Struct ⟨1⟩) = false := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem absent_id_is_not_selected :
    (Index.ofEnvironment duplicates).structPositions.find 77 = none := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

end DuplicateSelectionControls

end TrustIr.SourceLayoutProps


namespace TrustIr.SingleReferenceQueryControls
open SourceLayout

private def definition (fields : List Ty) : EnumDef :=
  { id := ⟨7⟩, name := "SingleReferences", variants := [
      { name := "Dead", fields }, { name := "Live", fields := [.U32] }],
    discriminants := [some (-5), some 17],
    layout := some { encoding := .singleInhabited 1, size := 4, align := 4, variantFieldOffsets := [[], [0]] } }
private def source (fields : List Ty) : Environment :=
  { hasTargetInfo := true, types := [some .U128], enums := [definition fields] }
private def bad (ty : Ty) : Environment := source [.Never, ty]
private def captureBad : Environment :=
  { (bad (.Closure ⟨0⟩)) with
    funcTypes := [{ params := [], returns := [], isVararg := false }],
    closures := [{ func := ⟨0⟩, captures := [.Sequence ⟨99⟩] }] }
private def cycle (withNever : Bool) : Environment :=
  { (source (if withNever then [.Never, .Enum ⟨8⟩] else [.Enum ⟨8⟩])) with
    enums := [definition (if withNever then [.Never, .Enum ⟨8⟩] else [.Enum ⟨8⟩]),
      { id := ⟨8⟩, name := "Cycle", variants := [{ name := "Again", fields := [.Enum ⟨8⟩] }] }] }
private def one : Environment :=
  { hasTargetInfo := true, enums := [
      { id := ⟨7⟩, name := "SingleReferences", variants := [{ name := "Live", fields := [.U32] }],
        discriminants := [some 17], layout := some { encoding := .singleInhabited 0, size := 4, align := 4, variantFieldOffsets := [[0]] } }] }
private def zero : Environment :=
  { (source [.Never, .Array ⟨0⟩ word64Max]) with enums := [
      { (definition [.Never, .Array ⟨0⟩ word64Max]) with
        variants := [{ name := "Dead", fields := [.Never, .Array ⟨0⟩ word64Max] }, { name := "Live", fields := [] }],
        layout := some { encoding := .singleInhabited 1, size := 0, align := 1, variantFieldOffsets := [[], []] } }] }
private def item (functions : List (FuncId × FuncTyId)) (types : List FuncTyDef) : Environment :=
  { (bad (.FnItem ⟨42⟩)) with functions, funcTypes := types }
private def signature : FuncTyDef := { params := [], returns := [], isVararg := false }
private def view (result : Result Summary) :=
  result.toOption.bind (fun value => value.enumeration.map (fun e =>
    (value.size, value.align, e.discriminants, e.variants.map (fun row => row.map (·.offset)), e.uninhabited)))

private theorem fresh_query_from_compilation
    (index : Index) (before after : Graph) (mode : Mode) (ty : Ty) (root : Nat)
    (compiled : RootCompilation index mode ty before root after) :
    ({ index, graph := before } : Session).query mode ty = (do
      let (value, memo) ← SourceLayout.solve after (Available.domain after.nodes) root .empty
      pure (value, { index, graph := after, memo, roots := (NatIndexTree.empty : NatIndexTree (List (Ty × Mode × Nat))).insert (rootBucket mode ty) [(ty, mode, root)] })) := by
  unfold RootCompilation at compiled
  simp only [Session.query, compiled]
  rfl


private theorem public_query_from_compilation
    (environment : Environment) (mode : Mode) (ty : Ty) (root : Nat)
    (compiled : RootCompilation (Index.ofEnvironment environment) mode ty
      (prepare environment).graph root (prepare environment).graph) :
    query environment mode ty = (do
      pure (← SourceLayout.solve (prepare environment).graph
        (Available.domain (prepare environment).graph.nodes) root .empty).1) := by
  unfold query
  change (do pure (← ({index := Index.ofEnvironment environment, graph := (prepare environment).graph} : Session).query mode ty).1) = _
  rw [fresh_query_from_compilation _ _ _ _ _ _ compiled]
  cases event : SourceLayout.solve (prepare environment).graph
      (Available.domain (prepare environment).graph.nodes) root .empty with
  | error error => rfl
  | ok pair => cases pair; rfl


private theorem query_initial_error
    (environment : Environment) (mode : Mode) (ty : Ty) (root : Nat)
    (equation : Equation) (error : Error)
    (compiled : RootCompilation (Index.ofEnvironment environment) mode ty
      (prepare environment).graph root (prepare environment).graph)
    (found : (prepare environment).graph.nodes.find root = some equation)
    (initial : equation.initial = .error error) :
    query environment mode ty = .error error := by
  rw [public_query_from_compilation _ _ _ _ compiled]
  have present : (Available.domain (prepare environment).graph.nodes).find root = some () := by
    rw [Available.find_domain, found]
    rfl
  rw [solve_initial_error _ _ _ .empty error equation (by rfl) present found initial]
  rfl

namespace OverflowEvidence

private def positive := source [.Never,.Array ⟨0⟩ word64Max]
private abbrev idx := Index.ofEnvironment positive

private theorem nonzero : (word64Max == 0) = false := by decide
private theorem formula_wide (index : Index) : inhabitFormulas index [.Never,.Array ⟨0⟩ word64Max] = [.yes, if !(index.typeRows[0]?).isSome then .no else .ref 0] := by
  simp only [inhabitFormulas, inhabitFormula, nonzero, Bool.false_or]
private theorem formula_live (index : Index) : inhabitFormulas index [.U32] = [.no] := by rfl
private theorem formula_type (index : Index) : inhabitFormula index .U128 = .no := by rfl
private theorem refs_wide (index : Index) : referenceFormulas index [.Never,.Array ⟨0⟩ word64Max] = [.yes, if !(trustIrArrayGet? index.typeRows 0).isSome then .no else .ref 0] := by
  have no : decide False = false := rfl
  simp only [referenceFormulas, referenceFormula, Nat.lt_irrefl, no, Bool.false_or]
private theorem refs_live (index : Index) : referenceFormulas index [.U32] = [.yes] := by rfl
private theorem refs_type (index : Index) : referenceFormula index .U128 = .yes := by rfl

private theorem wide_inhabit : uninhabitedFacts idx = .empty := by
  trustIrCompilerProof {
    unfold uninhabitedFacts
    conv =>
      lhs
      arg 1
      rw [inhabitEquations_eq]
      dsimp only [idx, positive, source, definition, Index.ofEnvironment, numbered, ForIn.forIn, List.forIn, List.forIn.loop, Id.run, Bind.bind, Pure.pure, definitionGroups, List.foldr, List.map, List.zip, List.zipWith, List.length, List.range, List.range.loop, NatIndexTree.find, NatIndexTree.insert]
      simp only [formula_wide, formula_live, formula_type]
    rfl
  } { trustIrReduce }

private theorem wide_references : referenceFacts idx = ((NatIndexTree.empty.insert 0 ()).insert 1 ()) := by
  trustIrCompilerProof {
    unfold referenceFacts
    conv =>
      lhs
      arg 1
      rw [referenceEquations_eq]
      dsimp only [idx, positive, source, definition, Index.ofEnvironment, numbered, ForIn.forIn, List.forIn, List.forIn.loop, Id.run, Bind.bind, Pure.pure, definitionGroups, List.foldr, List.map, List.zip, List.zipWith, List.length, List.range, List.range.loop, NatIndexTree.find, NatIndexTree.insert]
      simp only [refs_wide, refs_live, refs_type]
    rfl
  } { trustIrReduce }

private theorem dead_flag : variantUninhabited idx .empty [.Never,.Array ⟨0⟩ word64Max] = true := by
  unfold variantUninhabited
  rw [formula_wide]
  rfl
private theorem live_flag : variantUninhabited idx .empty [.U32] = false := by rfl
private theorem wide_guard (q : Equation) : directEnumEquation idx (definition [.Never,.Array ⟨0⟩ word64Max]) q = q := by
  unfold directEnumEquation
  change (if (definition [.Never,.Array ⟨0⟩ word64Max]).variants.all (fun variant => fieldsHaveReferences idx (referenceFacts idx) variant.fields) then q else .done (.error (.incoherent "enum" 7))) = q
  rw [wide_references]
  simp only [definition, List.all_cons, List.all_nil, fieldsHaveReferences, refs_wide, refs_live]
  rfl

private theorem wide_types : idx.source.types = [some .U128] := by rfl
private theorem wide_enums : idx.source.enums = [definition [.Never,.Array ⟨0⟩ word64Max]] := by rfl
private theorem wide_structs : idx.source.structs = [] := by rfl
private theorem wide_closures : idx.source.closures = [] := by rfl
private theorem wide_tupleLayouts : idx.source.tupleLayouts = [] := by rfl
private theorem wide_closureLayouts : idx.source.closureLayouts = [] := by rfl
private theorem wide_variants : (definition [.Never,.Array ⟨0⟩ word64Max]).variants = [{name:="Dead",fields:=[.Never,.Array ⟨0⟩ word64Max]},{name:="Live",fields:=[.U32]}] := by rfl

private theorem wide_flags : (definition [.Never,.Array ⟨0⟩ word64Max]).variants.map (fun v => variantUninhabited idx .empty v.fields) = [true,false] := by
  simp only [wide_variants,List.map_cons,List.map_nil,dead_flag,live_flag]
private theorem wide_flags_direct : ([{name:="Dead",fields:=[.Never,.Array ⟨0⟩ word64Max]},{name:="Live",fields:=[.U32]}] : List EnumVariantDef).map (fun v => variantUninhabited idx .empty v.fields) = [true,false] := by
  simp only [List.map_cons,List.map_nil,dead_flag,live_flag]
private theorem wide_selected : enumPhysicalSelection (definition [.Never,.Array ⟨0⟩ word64Max]) [true,false] = some 1 := by rfl

private def deadSource := source [.Never, .Array ⟨0⟩ word64Max]
private def unitEq : Equation := { kind := .unit, initial := .ok (), steps := [], finish := fun _ => .ok { size := 0, align := some 1 } }
private def deadGraph : Graph := {
  count := 12
  leaves := (NatIndexTree.empty.insert 1041 6).insert 261 8
  nodes := ([(0, Equation.done (.ok {size := 16, align := some 16})),
    (1, enumEquation .shape (definition [.Never, .Array ⟨0⟩ word64Max]) [true,false] [7,9]),
    (2, Equation.done (.ok {size := 16, align := some 16})),
    (3, enumEquation .execution (definition [.Never, .Array ⟨0⟩ word64Max]) [true,false] [10,11]),
    (4, unitEq), (5, unitEq),
    (6, Equation.done (.ok {size := 16, align := some 16})),
    (7, declaredFields .shape "enum" 7 4 4 word64Max false []),
    (8, Equation.done (.ok {size := 4, align := some 4})),
    (9, declaredFields .shape "enum" 7 4 4 word64Max false [(.U32, some 0, 8)]),
    (10, declaredFields .execution "enum" 7 4 4 word64Max false []),
    (11, declaredFields .execution "enum" 7 4 4 word64Max false [(.U32, some 0, 8)])] : List (Nat × Equation)).foldl (fun tree (key,eqn) => tree.insert key eqn) .empty }

private theorem wide_graph : (prepare positive).graph = deadGraph := by
  have flags_exact : ∀ d, d ∈ idx.source.enums →
      d.variants.map (fun v => variantUninhabited idx .empty v.fields) = [true,false] := by
    intro d member
    rewrite [wide_enums] at member
    cases member with
    | head => exact wide_flags
    | tail _ impossible => cases impossible
  have roots_exact : ∀ d, d ∈ idx.source.enums → ∀ q, directEnumEquation idx d q = q := by
    intro d member q
    rewrite [wide_enums] at member
    cases member with
    | head => exact wide_guard q
    | tail _ impossible => cases impossible
  have checked := build_eq_original_of_enum_data idx .empty (fun _ => [true,false]) (fun _ q => q) flags_exact roots_exact
  unfold prepare
  dsimp only
  rewrite [wide_inhabit]
  exact checked.trans (by trustIrReduce)
private theorem wide_solve_shape : view (do pure (← SourceLayout.solve deadGraph (Available.domain deadGraph.nodes) 1 .empty).1) = some (4,some 4,[-5,17],[[],[0]],[true,false]) := by trustIrReduce
private theorem wide_solve_execution : view (do pure (← SourceLayout.solve deadGraph (Available.domain deadGraph.nodes) 3 .empty).1) = some (4,some 4,[-5,17],[[],[0]],[true,false]) := by trustIrReduce
private theorem wide_public :
    view (query positive .shape (.Enum ⟨7⟩)) = some (4,some 4,[-5,17],[[],[0]],[true,false]) ∧
    view (query positive .execution (.Enum ⟨7⟩)) = some (4,some 4,[-5,17],[[],[0]],[true,false]) := by
  constructor
  · have compiled : RootCompilation idx .shape (.Enum ⟨7⟩) (prepare positive).graph 1 (prepare positive).graph := by rfl
    rewrite [public_query_from_compilation _ _ _ _ compiled]
    rewrite [wide_graph]
    exact wide_solve_shape
  · have compiled : RootCompilation idx .execution (.Enum ⟨7⟩) (prepare positive).graph 3 (prepare positive).graph := by rfl
    rewrite [public_query_from_compilation _ _ _ _ compiled]
    rewrite [wide_graph]
    exact wide_solve_execution

end OverflowEvidence

namespace CycleEvidence

private def positive := cycle true
private abbrev idx := Index.ofEnvironment positive
private def cycleDef : EnumDef := { id:=⟨8⟩,name:="Cycle",variants:=[{name:="Again",fields:=[.Enum ⟨8⟩]}] }
private theorem wide_inhabit : uninhabitedFacts idx = .empty := by trustIrReduce
private theorem wide_references : referenceFacts idx = ((NatIndexTree.empty.insert 0 ()).insert 1 ()).insert 2 () := by trustIrReduce
private theorem wide_enums : idx.source.enums = [definition [.Never,.Enum ⟨8⟩],cycleDef] := by rfl
private theorem wide_guard (q : Equation) : directEnumEquation idx (definition [.Never,.Enum ⟨8⟩]) q = q := by
  unfold directEnumEquation
  change (if (definition [.Never,.Enum ⟨8⟩]).variants.all (fun v => fieldsHaveReferences idx (referenceFacts idx) v.fields) then q else .done (.error (.incoherent "enum" 7))) = q
  rewrite [wide_references]
  rfl
private theorem flags_exact : ∀ d, d ∈ idx.source.enums → d.variants.map (fun v=>variantUninhabited idx .empty v.fields) = (if d.id.index = 7 then [true,false] else [false]) := by
  intro d member
  rewrite [wide_enums] at member
  cases member with
  | head => rfl
  | tail _ member => cases member with
    | head => rfl
    | tail _ impossible => cases impossible
private theorem roots_exact : ∀ d, d ∈ idx.source.enums → ∀ q, directEnumEquation idx d q = q := by
  intro d member q
  rewrite [wide_enums] at member
  cases member with
  | head => exact wide_guard q
  | tail _ member => cases member with
    | head => rfl
    | tail _ impossible => cases impossible
private def flags (d : EnumDef) : List Bool := if d.id.index = 7 then [true,false] else [false]
private def roots (_ : EnumDef) (q : Equation) := q
private theorem checkedFlags : ∀ d, d ∈ idx.source.enums → d.variants.map (fun v=>variantUninhabited idx .empty v.fields) = flags d := flags_exact
private theorem checkedRoots : ∀ d, d ∈ idx.source.enums → ∀ q, directEnumEquation idx d q = roots d q := roots_exact
private def unitEq : Equation := {kind:=.unit,initial:=.ok (),steps:=[],finish:=fun _ =>.ok {size:=0,align:=some 1}}
private def deadGraph : Graph := {count:=16,leaves:=(NatIndexTree.empty.insert 1041 8).insert 261 10, nodes:= ([(0,Equation.done (.ok {size:=16,align:=some 16})),
 (1,enumEquation .shape (definition [.Never,.Enum ⟨8⟩]) [true,false] [9,11]),
 (2,enumEquation .shape cycleDef [false] [12]),
 (3,Equation.done (.ok {size:=16,align:=some 16})),
 (4,enumEquation .execution (definition [.Never,.Enum ⟨8⟩]) [true,false] [13,14]),
 (5,enumEquation .execution cycleDef [false] [15]),(6,unitEq),(7,unitEq),
 (8,Equation.done (.ok {size:=16,align:=some 16})),
 (9,declaredFields .shape "enum" 7 4 4 word64Max false []),
 (10,Equation.done (.ok {size:=4,align:=some 4})),
 (11,declaredFields .shape "enum" 7 4 4 word64Max false [(.U32,some 0,10)]),
 (12,canonicalFields .shape "enum" 8 [(.Enum ⟨8⟩,2)]),
 (13,declaredFields .execution "enum" 7 4 4 word64Max false []),
 (14,declaredFields .execution "enum" 7 4 4 word64Max false [(.U32,some 0,10)]),
 (15,canonicalFields .execution "enum" 8 [(.Enum ⟨8⟩,5)])] : List (Nat × Equation)).foldl (fun t (k,e)=>t.insert k e) .empty}
private theorem wide_graph : (prepare positive).graph = deadGraph := by
  have checked := build_eq_original_of_enum_data idx .empty flags roots checkedFlags checkedRoots
  unfold prepare
  dsimp only
  rewrite [wide_inhabit]
  exact checked.trans (by trustIrReduce)
private theorem wide_solve_shape : view (do pure (← SourceLayout.solve deadGraph (Available.domain deadGraph.nodes) 1 .empty).1) = some (4,some 4,[-5,17],[[],[0]],[true,false]) := by trustIrReduce
private theorem wide_solve_execution : view (do pure (← SourceLayout.solve deadGraph (Available.domain deadGraph.nodes) 4 .empty).1) = some (4,some 4,[-5,17],[[],[0]],[true,false]) := by trustIrReduce
private theorem wide_public :
    view (query positive .shape (.Enum ⟨7⟩)) = some (4,some 4,[-5,17],[[],[0]],[true,false]) ∧
    view (query positive .execution (.Enum ⟨7⟩)) = some (4,some 4,[-5,17],[[],[0]],[true,false]) := by
  constructor
  · have compiled : RootCompilation idx .shape (.Enum ⟨7⟩) (prepare positive).graph 1 (prepare positive).graph := by rfl
    rewrite [public_query_from_compilation _ _ _ _ compiled]
    rewrite [wide_graph]
    exact wide_solve_shape
  · have compiled : RootCompilation idx .execution (.Enum ⟨7⟩) (prepare positive).graph 4 (prepare positive).graph := by rfl
    rewrite [public_query_from_compilation _ _ _ _ compiled]
    rewrite [wide_graph]
    exact wide_solve_execution

end CycleEvidence

namespace ItemEvidence

private def positive := item [(⟨42⟩,⟨0⟩)] [signature]
private abbrev idx := Index.ofEnvironment positive
private theorem wide_inhabit : uninhabitedFacts idx = .empty := by trustIrReduce
private theorem wide_references : referenceFacts idx = (NatIndexTree.empty.insert 0 ()).insert 1 () := by trustIrReduce
private theorem wide_enums : idx.source.enums = [definition [.Never,.FnItem ⟨42⟩]] := by rfl
private theorem wide_flags : (definition [.Never,.FnItem ⟨42⟩]).variants.map (fun v => variantUninhabited idx .empty v.fields) = [true,false] := by rfl
private theorem wide_guard (q : Equation) : directEnumEquation idx (definition [.Never,.FnItem ⟨42⟩]) q = q := by
  unfold directEnumEquation
  change (if (definition [.Never,.FnItem ⟨42⟩]).variants.all (fun v => fieldsHaveReferences idx (referenceFacts idx) v.fields) then q else .done (.error (.incoherent "enum" 7))) = q
  rewrite [wide_references]
  rfl

private def deadSource := source [.Never, .FnItem ⟨42⟩]
private def unitEq : Equation := { kind := .unit, initial := .ok (), steps := [], finish := fun _ => .ok { size := 0, align := some 1 } }
private def deadGraph : Graph := {
  count := 12
  leaves := (NatIndexTree.empty.insert 1041 6).insert 261 8
  nodes := ([(0, Equation.done (.ok {size := 16, align := some 16})),
    (1, enumEquation .shape (definition [.Never, .FnItem ⟨42⟩]) [true,false] [7,9]),
    (2, Equation.done (.ok {size := 16, align := some 16})),
    (3, enumEquation .execution (definition [.Never, .FnItem ⟨42⟩]) [true,false] [10,11]),
    (4, unitEq), (5, unitEq),
    (6, Equation.done (.ok {size := 16, align := some 16})),
    (7, declaredFields .shape "enum" 7 4 4 word64Max false []),
    (8, Equation.done (.ok {size := 4, align := some 4})),
    (9, declaredFields .shape "enum" 7 4 4 word64Max false [(.U32, some 0, 8)]),
    (10, declaredFields .execution "enum" 7 4 4 word64Max false []),
    (11, declaredFields .execution "enum" 7 4 4 word64Max false [(.U32, some 0, 8)])] : List (Nat × Equation)).foldl (fun tree (key,eqn) => tree.insert key eqn) .empty }
private theorem wide_graph : (prepare positive).graph = deadGraph := by
  have flags_exact : ∀ d, d ∈ idx.source.enums →
      d.variants.map (fun v => variantUninhabited idx .empty v.fields) = [true,false] := by
    intro d member
    rewrite [wide_enums] at member
    cases member with
    | head => exact wide_flags
    | tail _ impossible => cases impossible
  have roots_exact : ∀ d, d ∈ idx.source.enums → ∀ q, directEnumEquation idx d q = q := by
    intro d member q
    rewrite [wide_enums] at member
    cases member with
    | head => exact wide_guard q
    | tail _ impossible => cases impossible
  have checked := build_eq_original_of_enum_data idx .empty (fun _ => [true,false]) (fun _ q => q) flags_exact roots_exact
  unfold prepare
  dsimp only
  rewrite [wide_inhabit]
  exact checked.trans (by trustIrReduce)
private theorem wide_solve_shape : view (do pure (← SourceLayout.solve deadGraph (Available.domain deadGraph.nodes) 1 .empty).1) = some (4,some 4,[-5,17],[[],[0]],[true,false]) := by trustIrReduce
private theorem wide_solve_execution : view (do pure (← SourceLayout.solve deadGraph (Available.domain deadGraph.nodes) 3 .empty).1) = some (4,some 4,[-5,17],[[],[0]],[true,false]) := by trustIrReduce
private theorem wide_public :
    view (query positive .shape (.Enum ⟨7⟩)) = some (4,some 4,[-5,17],[[],[0]],[true,false]) ∧
    view (query positive .execution (.Enum ⟨7⟩)) = some (4,some 4,[-5,17],[[],[0]],[true,false]) := by
  constructor
  · have compiled : RootCompilation idx .shape (.Enum ⟨7⟩) (prepare positive).graph 1 (prepare positive).graph := by rfl
    rewrite [public_query_from_compilation _ _ _ _ compiled]
    rewrite [wide_graph]
    exact wide_solve_shape
  · have compiled : RootCompilation idx .execution (.Enum ⟨7⟩) (prepare positive).graph 3 (prepare positive).graph := by rfl
    rewrite [public_query_from_compilation _ _ _ _ compiled]
    rewrite [wide_graph]
    exact wide_solve_execution


end ItemEvidence

namespace ZeroEvidence

private def positive := zero
private abbrev idx := Index.ofEnvironment positive

private theorem nonzero : (word64Max == 0) = false := by decide
private theorem formula_wide (index : Index) : inhabitFormulas index [.Never,.Array ⟨0⟩ word64Max] = [.yes, if !(index.typeRows[0]?).isSome then .no else .ref 0] := by
  simp only [inhabitFormulas, inhabitFormula, nonzero, Bool.false_or]
private theorem formula_live (index : Index) : inhabitFormulas index [.U32] = [.no] := by rfl
private theorem formula_type (index : Index) : inhabitFormula index .U128 = .no := by rfl
private theorem refs_wide (index : Index) : referenceFormulas index [.Never,.Array ⟨0⟩ word64Max] = [.yes, if !(trustIrArrayGet? index.typeRows 0).isSome then .no else .ref 0] := by
  have no : decide False = false := rfl
  simp only [referenceFormulas, referenceFormula, Nat.lt_irrefl, no, Bool.false_or]
private theorem refs_live (index : Index) : referenceFormulas index [.U32] = [.yes] := by rfl
private theorem refs_type (index : Index) : referenceFormula index .U128 = .yes := by rfl

private theorem wide_inhabit : uninhabitedFacts idx = .empty := by
  trustIrCompilerProof {
    unfold uninhabitedFacts
    conv =>
      lhs
      arg 1
      rw [inhabitEquations_eq]
      dsimp only [idx, positive, zero, source, definition, Index.ofEnvironment, numbered, ForIn.forIn, List.forIn, List.forIn.loop, Id.run, Bind.bind, Pure.pure, definitionGroups, List.foldr, List.map, List.zip, List.zipWith, List.length, List.range, List.range.loop, NatIndexTree.find, NatIndexTree.insert]
      simp only [formula_wide, formula_live, formula_type]
    rfl
  } { trustIrReduce }

private theorem wide_references : referenceFacts idx = ((NatIndexTree.empty.insert 0 ()).insert 1 ()) := by
  trustIrCompilerProof {
    unfold referenceFacts
    conv =>
      lhs
      arg 1
      rw [referenceEquations_eq]
      dsimp only [idx, positive, zero, source, definition, Index.ofEnvironment, numbered, ForIn.forIn, List.forIn, List.forIn.loop, Id.run, Bind.bind, Pure.pure, definitionGroups, List.foldr, List.map, List.zip, List.zipWith, List.length, List.range, List.range.loop, NatIndexTree.find, NatIndexTree.insert]
      simp only [refs_wide, refs_live, refs_type]
    rfl
  } { trustIrReduce }

private def zeroDef : EnumDef := { (definition [.Never,.Array ⟨0⟩ word64Max]) with variants := [{name:="Dead",fields:=[.Never,.Array ⟨0⟩ word64Max]},{name:="Live",fields:=[]}], layout:=some {encoding:=.singleInhabited 1,size:=0,align:=1,variantFieldOffsets:=[[],[]]} }

private theorem wide_enums : idx.source.enums = [zeroDef] := by rfl
private theorem zero_variants : zeroDef.variants = [{name:="Dead",fields:=[.Never,.Array ⟨0⟩ word64Max]},{name:="Live",fields:=[]}] := by rfl
private theorem dead_flag : variantUninhabited idx .empty [.Never,.Array ⟨0⟩ word64Max] = true := by
  unfold variantUninhabited
  rewrite [formula_wide]
  rfl
private theorem empty_flag : variantUninhabited idx .empty [] = false := by rfl
private theorem empty_refs (index : Index) : referenceFormulas index [] = [] := by rfl
private theorem wide_flags : zeroDef.variants.map (fun v=>variantUninhabited idx .empty v.fields) = [true,false] := by
  simp only [zero_variants,List.map_cons,List.map_nil,dead_flag,empty_flag]
private theorem wide_guard (q : Equation) : directEnumEquation idx zeroDef q = q := by
  unfold directEnumEquation
  change (if zeroDef.variants.all (fun v=>fieldsHaveReferences idx (referenceFacts idx) v.fields) then q else .done (.error (.incoherent "enum" 7))) = q
  rewrite [wide_references]
  simp only [zero_variants,List.all_cons,List.all_nil,fieldsHaveReferences,refs_wide,empty_refs]
  rfl
private def unitEq : Equation := {kind:=.unit,initial:=.ok (),steps:=[],finish:=fun _=>.ok {size:=0,align:=some 1}}
private def deadGraph : Graph := {count:=11,leaves:=NatIndexTree.empty.insert 1041 6,nodes:= ([(0,Equation.done (.ok {size:=16,align:=some 16})),(1,enumEquation .shape zeroDef [true,false] [7,8]),(2,Equation.done (.ok {size:=16,align:=some 16})),(3,enumEquation .execution zeroDef [true,false] [9,10]),(4,unitEq),(5,unitEq),(6,Equation.done (.ok {size:=16,align:=some 16})),(7,declaredFields .shape "enum" 7 0 1 word64Max false []),(8,declaredFields .shape "enum" 7 0 1 word64Max false []),(9,declaredFields .execution "enum" 7 0 1 word64Max false []),(10,declaredFields .execution "enum" 7 0 1 word64Max false [])] : List (Nat × Equation)).foldl (fun t (k,e)=>t.insert k e) .empty}
private theorem wide_graph : (prepare positive).graph = deadGraph := by
  have flags_exact : ∀ d, d ∈ idx.source.enums →
      d.variants.map (fun v => variantUninhabited idx .empty v.fields) = [true,false] := by
    intro d member
    rewrite [wide_enums] at member
    cases member with
    | head => exact wide_flags
    | tail _ impossible => cases impossible
  have roots_exact : ∀ d, d ∈ idx.source.enums → ∀ q, directEnumEquation idx d q = q := by
    intro d member q
    rewrite [wide_enums] at member
    cases member with
    | head => exact wide_guard q
    | tail _ impossible => cases impossible
  have checked := build_eq_original_of_enum_data idx .empty (fun _ => [true,false]) (fun _ q => q) flags_exact roots_exact
  unfold prepare
  dsimp only
  rewrite [wide_inhabit]
  exact checked.trans (by trustIrReduce)
private theorem wide_solve_shape : view (do pure (← SourceLayout.solve deadGraph (Available.domain deadGraph.nodes) 1 .empty).1) = some (0,some 1,[-5,17],[[],[]],[true,false]) := by trustIrReduce
private theorem wide_solve_execution : view (do pure (← SourceLayout.solve deadGraph (Available.domain deadGraph.nodes) 3 .empty).1) = some (0,some 1,[-5,17],[[],[]],[true,false]) := by trustIrReduce
private theorem wide_public :
    view (query positive .shape (.Enum ⟨7⟩)) = some (0,some 1,[-5,17],[[],[]],[true,false]) ∧
    view (query positive .execution (.Enum ⟨7⟩)) = some (0,some 1,[-5,17],[[],[]],[true,false]) := by
  constructor
  · have compiled : RootCompilation idx .shape (.Enum ⟨7⟩) (prepare positive).graph 1 (prepare positive).graph := by rfl
    rewrite [public_query_from_compilation _ _ _ _ compiled]
    rewrite [wide_graph]
    exact wide_solve_shape
  · have compiled : RootCompilation idx .execution (.Enum ⟨7⟩) (prepare positive).graph 3 (prepare positive).graph := by rfl
    rewrite [public_query_from_compilation _ _ _ _ compiled]
    rewrite [wide_graph]
    exact wide_solve_execution


end ZeroEvidence

theorem missing_struct :
    query (bad (.Struct ⟨99⟩)) .shape (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) ∧
    query (bad (.Struct ⟨99⟩)) .execution (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) := by
  trustIrCompilerProof {
    constructor
    · apply query_initial_error (root := ((Index.ofEnvironment (bad (.Struct ⟨99⟩))).node .shape (Index.ofEnvironment (bad (.Struct ⟨99⟩))).enumBase)) (equation := (.done (.error (.incoherent "enum" 7))))
      all_goals rfl
    · apply query_initial_error (root := ((Index.ofEnvironment (bad (.Struct ⟨99⟩))).node .execution (Index.ofEnvironment (bad (.Struct ⟨99⟩))).enumBase)) (equation := (.done (.error (.incoherent "enum" 7))))
      all_goals rfl
  } { exact ⟨(by trustIrReduce), (by trustIrReduce)⟩ }

theorem missing_enum :
    query (bad (.Enum ⟨99⟩)) .shape (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) ∧
    query (bad (.Enum ⟨99⟩)) .execution (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) := by
  trustIrCompilerProof {
    constructor
    · apply query_initial_error (root := ((Index.ofEnvironment (bad (.Enum ⟨99⟩))).node .shape (Index.ofEnvironment (bad (.Enum ⟨99⟩))).enumBase)) (equation := (.done (.error (.incoherent "enum" 7))))
      all_goals rfl
    · apply query_initial_error (root := ((Index.ofEnvironment (bad (.Enum ⟨99⟩))).node .execution (Index.ofEnvironment (bad (.Enum ⟨99⟩))).enumBase)) (equation := (.done (.error (.incoherent "enum" 7))))
      all_goals rfl
  } { exact ⟨(by trustIrReduce), (by trustIrReduce)⟩ }

theorem missing_record :
    query (bad (.Record ⟨99⟩)) .shape (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) ∧
    query (bad (.Record ⟨99⟩)) .execution (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) := by
  trustIrCompilerProof {
    constructor
    · apply query_initial_error (root := ((Index.ofEnvironment (bad (.Record ⟨99⟩))).node .shape (Index.ofEnvironment (bad (.Record ⟨99⟩))).enumBase)) (equation := (.done (.error (.incoherent "enum" 7))))
      all_goals rfl
    · apply query_initial_error (root := ((Index.ofEnvironment (bad (.Record ⟨99⟩))).node .execution (Index.ofEnvironment (bad (.Record ⟨99⟩))).enumBase)) (equation := (.done (.error (.incoherent "enum" 7))))
      all_goals rfl
  } { exact ⟨(by trustIrReduce), (by trustIrReduce)⟩ }

theorem missing_zero_array_element :
    query (bad (.Array ⟨99⟩ 0)) .shape (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) ∧
    query (bad (.Array ⟨99⟩ 0)) .execution (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) := by
  trustIrCompilerProof {
    constructor
    · apply query_initial_error (root := ((Index.ofEnvironment (bad (.Array ⟨99⟩ 0))).node .shape (Index.ofEnvironment (bad (.Array ⟨99⟩ 0))).enumBase)) (equation := (.done (.error (.incoherent "enum" 7))))
      all_goals rfl
    · apply query_initial_error (root := ((Index.ofEnvironment (bad (.Array ⟨99⟩ 0))).node .execution (Index.ofEnvironment (bad (.Array ⟨99⟩ 0))).enumBase)) (equation := (.done (.error (.incoherent "enum" 7))))
      all_goals rfl
  } { exact ⟨(by trustIrReduce), (by trustIrReduce)⟩ }

theorem missing_ref_referent :
    query (bad (.Ref (.Struct ⟨99⟩))) .shape (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) ∧
    query (bad (.Ref (.Struct ⟨99⟩))) .execution (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) := by
  trustIrCompilerProof {
    constructor
    · apply query_initial_error (root := ((Index.ofEnvironment (bad (.Ref (.Struct ⟨99⟩)))).node .shape (Index.ofEnvironment (bad (.Ref (.Struct ⟨99⟩)))).enumBase)) (equation := (.done (.error (.incoherent "enum" 7))))
      all_goals rfl
    · apply query_initial_error (root := ((Index.ofEnvironment (bad (.Ref (.Struct ⟨99⟩)))).node .execution (Index.ofEnvironment (bad (.Ref (.Struct ⟨99⟩)))).enumBase)) (equation := (.done (.error (.incoherent "enum" 7))))
      all_goals rfl
  } { exact ⟨(by trustIrReduce), (by trustIrReduce)⟩ }

theorem missing_closure_capture_sequence :
    query (captureBad) .shape (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) ∧
    query (captureBad) .execution (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) := by
  trustIrCompilerProof {
    constructor
    · apply query_initial_error (root := ((Index.ofEnvironment (captureBad)).node .shape (Index.ofEnvironment (captureBad)).enumBase)) (equation := (.done (.error (.incoherent "enum" 7))))
      all_goals rfl
    · apply query_initial_error (root := ((Index.ofEnvironment (captureBad)).node .execution (Index.ofEnvironment (captureBad)).enumBase)) (equation := (.done (.error (.incoherent "enum" 7))))
      all_goals rfl
  } { exact ⟨(by trustIrReduce), (by trustIrReduce)⟩ }

theorem missing_function_item :
    query (bad (.FnItem ⟨99⟩)) .shape (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) ∧
    query (bad (.FnItem ⟨99⟩)) .execution (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) := by
  trustIrCompilerProof {
    constructor
    · apply query_initial_error (root := ((Index.ofEnvironment (bad (.FnItem ⟨99⟩))).node .shape (Index.ofEnvironment (bad (.FnItem ⟨99⟩))).enumBase)) (equation := (.done (.error (.incoherent "enum" 7))))
      all_goals rfl
    · apply query_initial_error (root := ((Index.ofEnvironment (bad (.FnItem ⟨99⟩))).node .execution (Index.ofEnvironment (bad (.FnItem ⟨99⟩))).enumBase)) (equation := (.done (.error (.incoherent "enum" 7))))
      all_goals rfl
  } { exact ⟨(by trustIrReduce), (by trustIrReduce)⟩ }

theorem bare_cycle_no_deadness :
    query (cycle false) .shape (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) ∧
    query (cycle false) .execution (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) := by
  trustIrCompilerProof {
    constructor
    · apply query_initial_error (root := ((Index.ofEnvironment (cycle false)).node .shape (Index.ofEnvironment (cycle false)).enumBase)) (equation := (enumEquation .shape (definition [.Enum ⟨8⟩]) [false,false] [9,11]))
      all_goals rfl
    · apply query_initial_error (root := ((Index.ofEnvironment (cycle false)).node .execution (Index.ofEnvironment (cycle false)).enumBase)) (equation := (enumEquation .execution (definition [.Enum ⟨8⟩]) [false,false] [13,14]))
      all_goals rfl
  } { exact ⟨(by trustIrReduce), (by trustIrReduce)⟩ }

theorem ambiguous_function_item_header :
    query (item [(⟨42⟩, ⟨0⟩), (⟨42⟩, ⟨0⟩)] [signature]) .shape (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) ∧
    query (item [(⟨42⟩, ⟨0⟩), (⟨42⟩, ⟨0⟩)] [signature]) .execution (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) := by
  trustIrCompilerProof {
    constructor
    · apply query_initial_error (root := ((Index.ofEnvironment (item [(⟨42⟩, ⟨0⟩), (⟨42⟩, ⟨0⟩)] [signature])).node .shape (Index.ofEnvironment (item [(⟨42⟩, ⟨0⟩), (⟨42⟩, ⟨0⟩)] [signature])).enumBase)) (equation := (.done (.error (.incoherent "enum" 7))))
      all_goals rfl
    · apply query_initial_error (root := ((Index.ofEnvironment (item [(⟨42⟩, ⟨0⟩), (⟨42⟩, ⟨0⟩)] [signature])).node .execution (Index.ofEnvironment (item [(⟨42⟩, ⟨0⟩), (⟨42⟩, ⟨0⟩)] [signature])).enumBase)) (equation := (.done (.error (.incoherent "enum" 7))))
      all_goals rfl
  } { exact ⟨(by trustIrReduce), (by trustIrReduce)⟩ }

theorem missing_function_item_signature :
    query (item [(⟨42⟩, ⟨99⟩)] []) .shape (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) ∧
    query (item [(⟨42⟩, ⟨99⟩)] []) .execution (.Enum ⟨7⟩) = .error (.incoherent "enum" 7) := by
  trustIrCompilerProof {
    constructor
    · apply query_initial_error (root := ((Index.ofEnvironment (item [(⟨42⟩, ⟨99⟩)] [])).node .shape (Index.ofEnvironment (item [(⟨42⟩, ⟨99⟩)] [])).enumBase)) (equation := (.done (.error (.incoherent "enum" 7))))
      all_goals rfl
    · apply query_initial_error (root := ((Index.ofEnvironment (item [(⟨42⟩, ⟨99⟩)] [])).node .execution (Index.ofEnvironment (item [(⟨42⟩, ⟨99⟩)] [])).enumBase)) (equation := (.done (.error (.incoherent "enum" 7))))
      all_goals rfl
  } { exact ⟨(by trustIrReduce), (by trustIrReduce)⟩ }

theorem valid_dead_overflow :
    view (query (source [.Never, .Array ⟨0⟩ word64Max]) .shape (.Enum ⟨7⟩)) = some (4, some 4, [-5, 17], [[], [0]], [true, false]) ∧
    view (query (source [.Never, .Array ⟨0⟩ word64Max]) .execution (.Enum ⟨7⟩)) = some (4, some 4, [-5, 17], [[], [0]], [true, false]) := by
  trustIrCompilerProof { exact OverflowEvidence.wide_public } { exact ⟨(by trustIrReduce), (by trustIrReduce)⟩ }

theorem valid_never_cycle :
    view (query (cycle true) .shape (.Enum ⟨7⟩)) = some (4, some 4, [-5, 17], [[], [0]], [true, false]) ∧
    view (query (cycle true) .execution (.Enum ⟨7⟩)) = some (4, some 4, [-5, 17], [[], [0]], [true, false]) := by
  trustIrCompilerProof { exact CycleEvidence.wide_public } { exact ⟨(by trustIrReduce), (by trustIrReduce)⟩ }

theorem current_one_declaration :
    view (query (one) .shape (.Enum ⟨7⟩)) = some (4, some 4, [17], [[0]], [false]) ∧
    view (query (one) .execution (.Enum ⟨7⟩)) = some (4, some 4, [17], [[0]], [false]) := by
  trustIrCompilerProof { exact ⟨rfl, rfl⟩ } { exact ⟨(by trustIrReduce), (by trustIrReduce)⟩ }

theorem valid_live_zero_size :
    view (query (zero) .shape (.Enum ⟨7⟩)) = some (0, some 1, [-5, 17], [[], []], [true, false]) ∧
    view (query (zero) .execution (.Enum ⟨7⟩)) = some (0, some 1, [-5, 17], [[], []], [true, false]) := by
  trustIrCompilerProof { exact ZeroEvidence.wide_public } { exact ⟨(by trustIrReduce), (by trustIrReduce)⟩ }

theorem valid_function_item_header :
    view (query (item [(⟨42⟩, ⟨0⟩)] [signature]) .shape (.Enum ⟨7⟩)) = some (4, some 4, [-5, 17], [[], [0]], [true, false]) ∧
    view (query (item [(⟨42⟩, ⟨0⟩)] [signature]) .execution (.Enum ⟨7⟩)) = some (4, some 4, [-5, 17], [[], [0]], [true, false]) := by
  trustIrCompilerProof { exact ItemEvidence.wide_public } { exact ⟨(by trustIrReduce), (by trustIrReduce)⟩ }

end TrustIr.SingleReferenceQueryControls

/- Original row401 finite deadness controls. The two declared source rows and
   all their references are retained; zero bytes never certify impossibility.
   These are public-query refusals, not source-to-plan or codec bridge proofs. -/
namespace TrustIr.SingleInhabitedProps
open SourceLayout

/-- Original selected payload and signed discriminants, before either mutation. -/
def definition : EnumDef :=
  { id := ⟨0⟩, name := "Selected"
    variants := [{ name := "Dead", fields := [.Never, .Array ⟨0⟩ 4096] },
      { name := "Live", fields := [.U32] }]
    discriminants := [some (-7), some 42], tagRepr := some .i8
    layout := some { encoding := .singleInhabited 1, size := 4, align := 4, variantFieldOffsets := [[], [0]] } }

def source : Environment :=
  { hasTargetInfo := true, types := [some .U8], enums := [definition] }

private def view (result : SourceLayout.Result Summary) : Option (Nat × Option Nat) :=
  match result with | .ok summary => some (summary.size, summary.align) | .error _ => none

private def changeDead (fields : List Ty) : Environment :=
  { source with enums := [{ definition with variants :=
      [{ name := "Dead", fields }, { name := "Live", fields := [.U32] }] }] }

private def unitSource : Environment := changeDead [.Unit]

private def zeroArraySource : Environment :=
  { (changeDead [.Array ⟨0⟩ 0]) with types := [some .Never] }

private def declaration (fields : List Ty) : EnumDef :=
  { definition with variants :=
    [{ name := "Dead", fields }, { name := "Live", fields := [.U32] }] }

private def descriptor : EnumLayoutDescriptor :=
  { encoding := .singleInhabited 1, size := 4, align := 4,
    variantFieldOffsets := [[], [0]] }

-- These separate checked facts exclude the missing-reference shortcut and
-- identify the precise failed inactive flag. They assume no query success.
private theorem unit_references_resolve :
    unitSource.enums.all (fun d => d.variants.all (fun v =>
      fieldsHaveReferences (Index.ofEnvironment unitSource)
        (referenceFacts (Index.ofEnvironment unitSource)) v.fields)) = true := by
  trustIrCompilerProof { exact rfl } { exact (by trustIrReduce) }

private theorem unit_flags_are_live :
    (declaration [.Unit]).variants.map (fun v =>
      variantUninhabited (Index.ofEnvironment unitSource)
        (uninhabitedFacts (Index.ofEnvironment unitSource)) v.fields) = [false, false] := by
  trustIrCompilerProof { exact rfl } { exact (by trustIrReduce) }

private theorem unit_inactive_flag_refuses :
    singleInhabitedValid (declaration [.Unit]) descriptor [false, false] 1 = false := rfl

private theorem zero_array_references_resolve :
    zeroArraySource.enums.all (fun d => d.variants.all (fun v =>
      fieldsHaveReferences (Index.ofEnvironment zeroArraySource)
        (referenceFacts (Index.ofEnvironment zeroArraySource)) v.fields)) = true := by
  trustIrCompilerProof { exact rfl } { exact (by trustIrReduce) }

private theorem zero_array_flags_are_live :
    (declaration [.Array ⟨0⟩ 0]).variants.map (fun v =>
      variantUninhabited (Index.ofEnvironment zeroArraySource)
        (uninhabitedFacts (Index.ofEnvironment zeroArraySource)) v.fields) = [false, false] := by
  trustIrCompilerProof { exact rfl } { exact (by trustIrReduce) }

private theorem zero_array_inactive_flag_refuses :
    singleInhabitedValid (declaration [.Array ⟨0⟩ 0]) descriptor [false, false] 1 = false := rfl

-- Exact named indices/facts of the two original inputs. These are checked
-- compiler data, not assumed query outcomes or fabricated replacement graphs.
private def unitIndex : Index := Index.ofEnvironment unitSource
private def zeroArrayIndex : Index := Index.ofEnvironment zeroArraySource
private def unitRoot : Nat := unitIndex.node .execution unitIndex.enumBase
private def zeroArrayRoot : Nat := zeroArrayIndex.node .execution zeroArrayIndex.enumBase
private def unitFacts : NatIndexTree Unit := .empty
private def zeroArrayFacts : NatIndexTree Unit := NatIndexTree.empty.insert 0 ()

private theorem unit_inhabitance : uninhabitedFacts unitIndex = unitFacts := by
  trustIrCompilerProof { exact rfl } { exact (by trustIrReduce) }

private theorem zero_array_inhabitance : uninhabitedFacts zeroArrayIndex = zeroArrayFacts := by
  trustIrCompilerProof { exact rfl } { exact (by trustIrReduce) }

private theorem unit_enums : unitIndex.source.enums = [declaration [.Unit]] := rfl
private theorem zero_array_enums : zeroArrayIndex.source.enums = [declaration [.Array ⟨0⟩ 0]] := rfl

private theorem unit_data_flags :
    (declaration [.Unit]).variants.map (fun v =>
      variantUninhabited unitIndex unitFacts v.fields) = [false, false] := by
  trustIrCompilerProof { exact rfl } { exact (by trustIrReduce) }

private theorem zero_array_data_flags :
    (declaration [.Array ⟨0⟩ 0]).variants.map (fun v =>
      variantUninhabited zeroArrayIndex zeroArrayFacts v.fields) = [false, false] := by
  trustIrCompilerProof { exact rfl } { exact (by trustIrReduce) }

private theorem unit_root_guard (equation : Equation) :
    directEnumEquation unitIndex (declaration [.Unit]) equation = equation := by
  trustIrCompilerProof {
    change (if (declaration [.Unit]).variants.all (fun v =>
      fieldsHaveReferences unitIndex (referenceFacts unitIndex) v.fields) then equation
      else .done (.error (.incoherent "enum" 0))) = equation
    have references : (declaration [.Unit]).variants.all (fun v =>
        fieldsHaveReferences unitIndex (referenceFacts unitIndex) v.fields) = true := by rfl
    rw [references]
    rfl
  } { exact (by trustIrReduce) }

private theorem zero_array_root_guard (equation : Equation) :
    directEnumEquation zeroArrayIndex (declaration [.Array ⟨0⟩ 0]) equation = equation := by
  trustIrCompilerProof {
    change (if (declaration [.Array ⟨0⟩ 0]).variants.all (fun v =>
      fieldsHaveReferences zeroArrayIndex (referenceFacts zeroArrayIndex) v.fields) then equation
      else .done (.error (.incoherent "enum" 0))) = equation
    have references : (declaration [.Array ⟨0⟩ 0]).variants.all (fun v =>
        fieldsHaveReferences zeroArrayIndex (referenceFacts zeroArrayIndex) v.fields) = true := by rfl
    rw [references]
    rfl
  } { exact (by trustIrReduce) }

-- Form the compiler observation while its index is still symbolic. The
-- concrete fixtures instantiate only the resulting Option Error equality;
-- no concrete dependent Graph equality is introduced in either proof.
private def enum_data_initial_projection
    (index : Index) (facts : NatIndexTree Unit)
    (flags : EnumDef → List Bool) (rootEquation : EnumDef → Equation → Equation)
    (flags_exact : ∀ d, d ∈ index.source.enums →
      d.variants.map (fun v => variantUninhabited index facts v.fields) = flags d)
    (roots_exact : ∀ d, d ∈ index.source.enums → ∀ equation,
      directEnumEquation index d equation = rootEquation d equation)
    (root : Nat) :=
  congrArg (fun actual : Graph => (actual.nodes.find root).bind (fun equation =>
    match equation.initial with
    | .error failure => some failure
    | .ok _ => none))
    (build_eq_original_of_enum_data index facts flags rootEquation flags_exact roots_exact)

private theorem unit_initial_observation :
    ((prepare unitSource).graph.nodes.find unitRoot).bind (fun equation =>
      match equation.initial with
      | .error failure => some failure
      | .ok _ => none) = some (.incoherent "enum" 0) := by
  trustIrCompilerProof {
    have flags_exact : ∀ d, d ∈ unitIndex.source.enums →
        d.variants.map (fun v => variantUninhabited unitIndex unitFacts v.fields) = [false, false] := by
      intro d member
      rewrite [unit_enums] at member
      cases member with
      | head => exact unit_data_flags
      | tail _ impossible => cases impossible
    have roots_exact : ∀ d, d ∈ unitIndex.source.enums → ∀ equation,
        directEnumEquation unitIndex d equation = equation := by
      intro d member equation
      rewrite [unit_enums] at member
      cases member with
      | head => exact unit_root_guard equation
      | tail _ impossible => cases impossible
    have checked := enum_data_initial_projection unitIndex unitFacts
      (fun _ => [false, false]) (fun _ equation => equation) flags_exact roots_exact unitRoot
    unfold prepare
    dsimp only
    rewrite [show uninhabitedFacts (Index.ofEnvironment unitSource) = unitFacts
      from unit_inhabitance]
    exact checked.trans (by rfl)
  } { exact (by trustIrReduce) }

private theorem zero_array_initial_observation :
    ((prepare zeroArraySource).graph.nodes.find zeroArrayRoot).bind (fun equation =>
      match equation.initial with
      | .error failure => some failure
      | .ok _ => none) = some (.incoherent "enum" 0) := by
  trustIrCompilerProof {
    have flags_exact : ∀ d, d ∈ zeroArrayIndex.source.enums →
        d.variants.map (fun v => variantUninhabited zeroArrayIndex zeroArrayFacts v.fields) = [false, false] := by
      intro d member
      rewrite [zero_array_enums] at member
      cases member with
      | head => exact zero_array_data_flags
      | tail _ impossible => cases impossible
    have roots_exact : ∀ d, d ∈ zeroArrayIndex.source.enums → ∀ equation,
        directEnumEquation zeroArrayIndex d equation = equation := by
      intro d member equation
      rewrite [zero_array_enums] at member
      cases member with
      | head => exact zero_array_root_guard equation
      | tail _ impossible => cases impossible
    have checked := enum_data_initial_projection zeroArrayIndex zeroArrayFacts
      (fun _ => [false, false]) (fun _ equation => equation) flags_exact roots_exact zeroArrayRoot
    unfold prepare
    dsimp only
    rewrite [show uninhabitedFacts (Index.ofEnvironment zeroArraySource) = zeroArrayFacts
      from zero_array_inhabitance]
    exact checked.trans (by rfl)
  } { exact (by trustIrReduce) }

/-- The actual stored initial-error projection is enough; the caller never
    reifies a dependent Equation or assumes a successful prepared query. -/
private theorem public_query_initial_refusal
    (environment : Environment) (mode : Mode) (ty : Ty) (root : Nat) (error : Error)
    (compiled : RootCompilation (Index.ofEnvironment environment) mode ty
      (prepare environment).graph root (prepare environment).graph)
    (observed : ((prepare environment).graph.nodes.find root).bind (fun equation =>
      match equation.initial with
      | .error failure => some failure
      | .ok _ => none) = some error) :
    query environment mode ty = .error error := by
  have fresh :
      ({ index := Index.ofEnvironment environment, graph := (prepare environment).graph } : Session).query mode ty = (do
        let (value, memo) ← SourceLayout.solve (prepare environment).graph
          (Available.domain (prepare environment).graph.nodes) root .empty
        pure (value, { index := Index.ofEnvironment environment, graph := (prepare environment).graph, memo, roots := (NatIndexTree.empty : NatIndexTree (List (Ty × Mode × Nat))).insert (rootBucket mode ty) [(ty, mode, root)] })) := by
    unfold RootCompilation at compiled
    simp only [Session.query, compiled]
    rfl
  unfold query
  change (do pure (← ({ index := Index.ofEnvironment environment, graph := (prepare environment).graph } : Session).query mode ty).1) = _
  rw [fresh]
  rw [solve_initial_error_observed _ _ .empty error (by rfl) observed]
  rfl

private theorem unit_query_error :
    query unitSource .execution (.Enum ⟨0⟩) = .error (.incoherent "enum" 0) := by
  trustIrCompilerProof {
    have compiled : RootCompilation unitIndex .execution (.Enum ⟨0⟩)
        (prepare unitSource).graph unitRoot (prepare unitSource).graph := by rfl
    exact public_query_initial_refusal unitSource .execution (.Enum ⟨0⟩) unitRoot
      (.incoherent "enum" 0) compiled unit_initial_observation
  } { exact (by trustIrReduce) }

private theorem zero_array_query_error :
    query zeroArraySource .execution (.Enum ⟨0⟩) = .error (.incoherent "enum" 0) := by
  trustIrCompilerProof {
    have compiled : RootCompilation zeroArrayIndex .execution (.Enum ⟨0⟩)
        (prepare zeroArraySource).graph zeroArrayRoot (prepare zeroArraySource).graph := by rfl
    exact public_query_initial_refusal zeroArraySource .execution (.Enum ⟨0⟩) zeroArrayRoot
      (.incoherent "enum" 0) compiled zero_array_initial_observation
  } { exact (by trustIrReduce) }

theorem zero_size_is_not_a_deadness_proof :
    view (SourceLayout.query (changeDead [.Unit]) .execution (.Enum ⟨0⟩)) = none := by
  change view (query unitSource .execution (.Enum ⟨0⟩)) = none
  rw [unit_query_error]
  rfl

theorem zero_array_of_never_is_not_a_deadness_proof :
    view (SourceLayout.query { (changeDead [.Array ⟨0⟩ 0]) with types := [some .Never] }
      .execution (.Enum ⟨0⟩)) = none := by
  change view (query zeroArraySource .execution (.Enum ⟨0⟩)) = none
  rw [zero_array_query_error]
  rfl

end TrustIr.SingleInhabitedProps
