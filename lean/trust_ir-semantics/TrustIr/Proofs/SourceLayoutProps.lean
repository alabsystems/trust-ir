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
