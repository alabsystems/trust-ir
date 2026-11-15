-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Inhabit

namespace TrustIr.SourceLayout

/-- Proof view of the source type attached to an uninhabitedness node.
    The four disjoint regions follow actual preparation. Missing type slots
    and positions outside those source tables have no attached type. This
    view does not replace the solver or grant an executable type operation. -/
def sourceNodeType (source : Environment) (node : Nat) : Option Ty :=
  if node < source.types.length then (trustIrListGet? source.types node).join
  else if node < source.types.length + source.structs.length then
    (trustIrListGet? source.structs (node - source.types.length)).map (fun row => .Struct row.id)
  else if node < source.types.length + source.structs.length + source.enums.length then
    (trustIrListGet? source.enums (node - (source.types.length + source.structs.length))).map (fun row => .Enum row.id)
  else if node < source.types.length + source.structs.length + source.enums.length + source.records.length then
    (trustIrListGet? source.records (node - (source.types.length + source.structs.length + source.enums.length))).map
      (fun row => .Record row.id)
  else none

inductive SourceNodeDenotes (source : Environment) : Nat → Ty → Prop where
  | typeRow (ty : Ty) (position : Nat) (member : (some ty, position) ∈ numbered source.types) :
      SourceNodeDenotes source position ty
  | structureRow (definition : StructDef) (position : Nat)
      (member : (definition, position) ∈ numbered source.structs) :
      SourceNodeDenotes source (source.types.length + position) (.Struct definition.id)
  | enumerationRow (definition : EnumDef) (position : Nat)
      (member : (definition, position) ∈ numbered source.enums) :
      SourceNodeDenotes source (source.types.length + source.structs.length + position) (.Enum definition.id)
  | recordRow (definition : RecordDef) (position : Nat)
      (member : (definition, position) ∈ numbered source.records) :
      SourceNodeDenotes source
        (source.types.length + source.structs.length + source.enums.length + position) (.Record definition.id)

theorem SourceNodeDenotes.lookup {source : Environment} {node : Nat} {ty : Ty}
    (denotes : SourceNodeDenotes source node ty) : sourceNodeType source node = some ty := by
  cases denotes with
  | typeRow ty position member =>
      have bound := numbered_position_bound source.types (some ty) node member
      simp only [sourceNodeType, if_pos bound, numbered_get source.types (some ty) node member]
      rfl
  | structureRow definition position member =>
      have bound := numbered_position_bound source.structs definition position member
      unfold sourceNodeType
      rw [if_neg (by omega), if_pos (by omega)]
      have offset : source.types.length + position - source.types.length = position := by omega
      rw [offset, numbered_get source.structs definition position member]
      rfl
  | enumerationRow definition position member =>
      have bound := numbered_position_bound source.enums definition position member
      unfold sourceNodeType
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      have offset : source.types.length + source.structs.length + position -
          (source.types.length + source.structs.length) = position := by omega
      rw [offset, numbered_get source.enums definition position member]
      rfl
  | recordRow definition position member =>
      have bound := numbered_position_bound source.records definition position member
      unfold sourceNodeType
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      have offset : source.types.length + source.structs.length + source.enums.length + position -
          (source.types.length + source.structs.length + source.enums.length) = position := by omega
      rw [offset, numbered_get source.records definition position member]
      rfl

/-- A node cannot acquire a second source type through overlapping regions or
    duplicate nominal IDs; each node is attached to its actual source position. -/
theorem SourceNodeDenotes.functional {source : Environment} {node : Nat} {first second : Ty}
    (left : SourceNodeDenotes source node first) (right : SourceNodeDenotes source node second) :
    first = second :=
  Option.some.inj (left.lookup.symm.trans right.lookup)

theorem SourceNodeDenotes.of_lookup {source : Environment} {node : Nat} {ty : Ty}
    (found : sourceNodeType source node = some ty) : SourceNodeDenotes source node ty := by
  unfold sourceNodeType at found
  split at found
  · cases row : trustIrListGet? source.types node with
    | none => simp [row] at found
    | some slot =>
        cases slot with
        | none => simp [row] at found
        | some actual =>
            have same : actual = ty := by simpa [row] using found
            subst ty
            exact .typeRow actual node ((numbered_member_iff_get _ _ _).2 row)
  · split at found
    · cases row : trustIrListGet? source.structs (node - source.types.length) with
      | none => simp [row] at found
      | some definition =>
          have same : Ty.Struct definition.id = ty := by simpa [row] using found
          subst ty
          have offset : source.types.length + (node - source.types.length) = node := by omega
          simpa only [offset] using (SourceNodeDenotes.structureRow definition _
            ((numbered_member_iff_get _ _ _).2 row))
    · split at found
      · cases row : trustIrListGet? source.enums (node - (source.types.length + source.structs.length)) with
        | none => simp [row] at found
        | some definition =>
            have same : Ty.Enum definition.id = ty := by simpa [row] using found
            subst ty
            have offset : source.types.length + source.structs.length +
                (node - (source.types.length + source.structs.length)) = node := by omega
            simpa only [offset] using (SourceNodeDenotes.enumerationRow definition _
              ((numbered_member_iff_get _ _ _).2 row))
      · split at found
        · cases row : trustIrListGet? source.records
            (node - (source.types.length + source.structs.length + source.enums.length)) with
          | none => simp [row] at found
          | some definition =>
              have same : Ty.Record definition.id = ty := by simpa [row] using found
              subst ty
              have offset : source.types.length + source.structs.length + source.enums.length +
                  (node - (source.types.length + source.structs.length + source.enums.length)) = node := by omega
              simpa only [offset] using (SourceNodeDenotes.recordRow definition _
                ((numbered_member_iff_get _ _ _).2 row))
        · cases found

theorem sourceNodeType_iff (source : Environment) (node : Nat) (ty : Ty) :
    sourceNodeType source node = some ty ↔ SourceNodeDenotes source node ty :=
  ⟨SourceNodeDenotes.of_lookup, SourceNodeDenotes.lookup⟩

theorem SourceNodeDenotes.bound {source : Environment} {node : Nat} {ty : Ty}
    (denotes : SourceNodeDenotes source node ty) :
    node < source.types.length + source.structs.length + source.enums.length + source.records.length := by
  cases denotes with
  | typeRow ty position member => have := numbered_position_bound _ _ _ member; omega
  | structureRow definition position member => have := numbered_position_bound _ _ _ member; omega
  | enumerationRow definition position member => have := numbered_position_bound _ _ _ member; omega
  | recordRow definition position member => have := numbered_position_bound _ _ _ member; omega

theorem Index.structBase_ofEnvironment (source : Environment) :
    (Index.ofEnvironment source).structBase = source.types.length := by
  first
  | simp [Index.structBase, Index.ofEnvironment, Array.size_toArray]
  | simp [Index.structBase, Index.ofEnvironment, List.size_toArray]

theorem Index.enumBase_ofEnvironment (source : Environment) :
    (Index.ofEnvironment source).enumBase = source.types.length + source.structs.length := by
  rw [Index.enumBase, Index.structBase_ofEnvironment]
  rfl

theorem Index.closureBase_ofEnvironment (source : Environment) :
    (Index.ofEnvironment source).closureBase =
      source.types.length + source.structs.length + source.enums.length := by
  rw [Index.closureBase, Index.enumBase_ofEnvironment]
  rfl

/-- Canonical execution selection names a source node of the requested
    nominal type, even when a different duplicate is selected by shape lookup. -/
theorem SourceNodeDenotes.struct_alias (source : Environment) (id : StructId) (position : Nat)
    (selected : (Index.ofEnvironment source).structPositions.find id.index = some position) :
    SourceNodeDenotes source ((Index.ofEnvironment source).structBase + position) (.Struct id) := by
  obtain ⟨definition, member, identity⟩ := positionIndex_witness source.structs (·.id.index) id.index position selected
  have same : definition.id = id := congrArg StructId.mk identity
  simpa only [Index.structBase_ofEnvironment, same] using
    (SourceNodeDenotes.structureRow definition position member)

theorem SourceNodeDenotes.enum_alias (source : Environment) (id : EnumId) (position : Nat)
    (selected : (Index.ofEnvironment source).enumPositions.find id.index = some position) :
    SourceNodeDenotes source ((Index.ofEnvironment source).enumBase + position) (.Enum id) := by
  obtain ⟨definition, member, identity⟩ := positionIndex_witness source.enums (·.id.index) id.index position selected
  have same : definition.id = id := congrArg EnumId.mk identity
  simpa only [Index.enumBase_ofEnvironment, same] using
    (SourceNodeDenotes.enumerationRow definition position member)

theorem SourceNodeDenotes.record_alias (source : Environment) (id : RecordId) (position : Nat)
    (selected : (Index.ofEnvironment source).recordPositions.find id.index = some position) :
    SourceNodeDenotes source ((Index.ofEnvironment source).closureBase + position) (.Record id) := by
  obtain ⟨definition, member, identity⟩ := positionIndex_witness source.records (·.id.index) id.index position selected
  have same : definition.id = id := congrArg RecordId.mk identity
  simpa only [Index.closureBase_ofEnvironment, same] using
    (SourceNodeDenotes.recordRow definition position member)

/-- Each actual source equation either refuses uninhabitedness outright or
    belongs to a node with its precise source type. -/
theorem SourceEquation.has_source_type (source : Environment) (node : Nat) (formula : Formula)
    (equation : SourceEquation (Index.ofEnvironment source) node formula) :
    formula = .no ∨ ∃ ty, SourceNodeDenotes source node ty := by
  cases equation with
  | typeRow row position member =>
      cases row with
      | none => exact Or.inl rfl
      | some ty => exact Or.inr ⟨ty, .typeRow ty node member⟩
  | structureRow definition position member =>
      exact Or.inr ⟨.Struct definition.id, by
        simpa only [Index.structBase_ofEnvironment] using
          (SourceNodeDenotes.structureRow definition position member)⟩
  | enumerationRow definition position member =>
      exact Or.inr ⟨.Enum definition.id, by
        simpa only [Index.enumBase_ofEnvironment] using
          (SourceNodeDenotes.enumerationRow definition position member)⟩
  | recordRow definition position member =>
      exact Or.inr ⟨.Record definition.id, by
        simpa only [Index.closureBase_ofEnvironment] using
          (SourceNodeDenotes.recordRow definition position member)⟩

theorem uninhabitedFacts_denotes (source : Environment) (node : Nat)
    (found : (uninhabitedFacts (Index.ofEnvironment source)).find node = some ()) :
    ∃ ty, SourceNodeDenotes source node ty := by
  obtain ⟨facts, formula, provenance, enabled, _premises⟩ :=
    uninhabitedFacts_source_witness (Index.ofEnvironment source) node found
  rcases SourceEquation.has_source_type source node formula provenance with refuses | typed
  · rw [refuses] at enabled
    cases enabled
  · exact typed

theorem uninhabitedFacts_source_type (source : Environment) (node : Nat)
    (found : (uninhabitedFacts (Index.ofEnvironment source)).find node = some ()) :
    ∃ ty, sourceNodeType source node = some ty := by
  obtain ⟨ty, denotes⟩ := uninhabitedFacts_denotes source node found
  exact ⟨ty, denotes.lookup⟩

theorem uninhabitedFacts_source_bound (source : Environment) (node : Nat)
    (found : (uninhabitedFacts (Index.ofEnvironment source)).find node = some ()) :
    node < source.types.length + source.structs.length + source.enums.length + source.records.length := by
  obtain ⟨ty, denotes⟩ := uninhabitedFacts_denotes source node found
  exact denotes.bound

/-- Missing source types cannot acquire a flag, including holes inside the
    type table and positions beyond all four source regions. -/
theorem uninhabitedFacts_no_source_type (source : Environment) (node : Nat)
    (absent : sourceNodeType source node = none) :
    (uninhabitedFacts (Index.ofEnvironment source)).find node = none := by
  cases found : (uninhabitedFacts (Index.ofEnvironment source)).find node with
  | none => rfl
  | some unit =>
      cases unit
      obtain ⟨ty, present⟩ := uninhabitedFacts_source_type source node found
      rw [absent] at present
      cases present

namespace SourceNodeControls

private def emptyField : FieldDef := { name := "empty", ty := .Never, offset := none }

private def source : Environment :=
  { types := [none, some .Never]
    structs := [
      { id := ⟨1⟩, name := "First", fields := [emptyField], size := none, align := none },
      { id := ⟨1⟩, name := "Canonical", fields := [emptyField], size := none, align := none }]
    enums := [{ id := ⟨99⟩, name := "Empty", variants := [] }]
    records := [{ id := ⟨88⟩, name := "EmptyRecord", fields := [emptyField] }] }

theorem sparse_kinds_remain_distinct :
    sourceNodeType source 3 = some (.Struct ⟨1⟩) ∧
    sourceNodeType source 4 = some (.Enum ⟨99⟩) ∧
    sourceNodeType source 5 = some (.Record ⟨88⟩) := ⟨by trustIrReduce, by trustIrReduce, by trustIrReduce⟩

theorem canonical_alias_keeps_type :
    SourceNodeDenotes source 3 (.Struct ⟨1⟩) :=
  SourceNodeDenotes.struct_alias source ⟨1⟩ 1 (by trustIrReduce)

theorem actual_alias_derives_flag :
    (uninhabitedFacts (Index.ofEnvironment source)).find 2 = some () := by trustIrReduce

theorem actual_never_seed_derives_flag :
    (uninhabitedFacts (Index.ofEnvironment source)).find 1 = some () := by trustIrReduce

theorem actual_type_hole_has_no_flag :
    (uninhabitedFacts (Index.ofEnvironment source)).find 0 = none :=
  uninhabitedFacts_no_source_type source 0 (by trustIrReduce)

theorem outside_all_regions_has_no_flag :
    (uninhabitedFacts (Index.ofEnvironment source)).find 6 = none :=
  uninhabitedFacts_no_source_type source 6 (by trustIrReduce)

end SourceNodeControls

end TrustIr.SourceLayout
