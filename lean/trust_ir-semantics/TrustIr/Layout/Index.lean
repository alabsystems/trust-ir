-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Graph
import TrustIr.Layout.Declarations

namespace TrustIr.SourceLayout

/-- Source positions index equations. Sparse nominal identifiers are resolved
    separately. Shape validation uses first definitions; executable layout uses
    the matching-position-then-first-definition rule. These differ on duplicate
    unvalidated tables, which the service must not silently conflate. -/
structure Index where
  source : Environment
  typeRows : Array (Option Ty)
  closureRows : Array ClosureTy
  structCount : Nat
  enumCount : Nat
  tupleDeclarations : TupleIndex
  closureDeclarations : ClosureIndex
  structDefinitions : NatIndexTree (List StructDef)
  enumDefinitions : NatIndexTree (List EnumDef)
  recordDefinitions : NatIndexTree (List RecordDef)
  structShapePositions : NatIndexTree Nat
  enumShapePositions : NatIndexTree Nat
  structPositions : NatIndexTree Nat
  enumPositions : NatIndexTree Nat
  recordPositions : NatIndexTree Nat

def numbered {α : Type} (rows : List α) : List (α × Nat) := rows.zip (List.range rows.length)

def firstPositionIndex {α : Type} (rows : List α) (id : α → Nat) : NatIndexTree Nat :=
  (numbered rows).foldr (fun (row, position) index => index.insert (id row) position) .empty

def positionIndex {α : Type} (rows : List α) (id : α → Nat) : NatIndexTree Nat :=
  let numbered := numbered rows
  let first := firstPositionIndex rows id
  numbered.foldl (fun index (row, position) =>
    if id row == position then index.insert position position else index) first

def definitionGroups {α : Type} (rows : List α) (id : α → Nat) : NatIndexTree (List α) :=
  rows.foldr (fun row groups => groups.insert (id row) (row :: (groups.find (id row)).getD [])) .empty

def Index.ofEnvironment (source : Environment) : Index :=
  let typeRows := source.types.toArray
  let closureRows := source.closures.toArray
  { source
    tupleDeclarations := TupleIndex.ofRows typeRows source.tupleLayouts
    closureDeclarations := ClosureIndex.ofRows closureRows source.closureLayouts
    typeRows := typeRows
    closureRows := closureRows
    structCount := source.structs.length
    enumCount := source.enums.length
    structDefinitions := definitionGroups source.structs (·.id.index)
    enumDefinitions := definitionGroups source.enums (·.id.index)
    recordDefinitions := definitionGroups source.records (·.id.index)
    structShapePositions := firstPositionIndex source.structs (·.id.index)
    enumShapePositions := firstPositionIndex source.enums (·.id.index)
    structPositions := positionIndex source.structs (·.id.index)
    enumPositions := positionIndex source.enums (·.id.index)
    recordPositions := positionIndex source.records (·.id.index) }

def Index.structBase (index : Index) : Nat := index.typeRows.size
def Index.enumBase (index : Index) : Nat := index.structBase + index.structCount
def Index.closureBase (index : Index) : Nat := index.enumBase + index.enumCount
def Index.count (index : Index) : Nat := index.closureBase + index.closureRows.size

def Index.node (index : Index) (mode : Mode) (position : Nat) : Nat :=
  (if mode == .shape then 0 else index.count) + position

/-- Reserved shape rows form the first block. Execution rows, validators
and dynamically allocated equations use execution as their indexed obligation.
Shape queries at dynamic roots additionally require their local mode guard. -/
def Index.nodeMode (index : Index) (node : Nat) : Mode :=
  if node < index.count then .shape else .execution

theorem Index.nodeMode_node (index : Index) (mode : Mode) (position : Nat)
    (inside : position < index.count) : index.nodeMode (index.node mode position) = mode := by
  cases mode with
  | shape =>
    change (if 0 + position < index.count then Mode.shape else .execution) = .shape
    rw [if_pos (by omega)]
  | execution =>
    change (if index.count + position < index.count then Mode.shape else .execution) = .execution
    rw [if_neg (by omega)]

theorem Index.nodeMode_dynamic (index : Index) (node : Nat) (outside : index.count ≤ node) :
    index.nodeMode node = .execution := by
  unfold Index.nodeMode
  exact if_neg (by omega)

/-- Nominal groups retain exactly the matching source rows, in source order.
    In particular, duplicate definitions are neither lost nor invented. -/
theorem definitionGroups_exact {α : Type} (rows : List α) (id : α → Nat) (key : Nat) :
    ((definitionGroups rows id).find key).getD [] =
      rows.filter (fun row => id row == key) := by
  induction rows with
  | nil => rfl
  | cons first rest ih =>
      simp only [definitionGroups, List.foldr_cons, NatIndexTree.find_insert]
      by_cases same : key = id first
      · subst key
        simp only [if_pos rfl, Option.getD_some]
        rw [show ((rest.foldr (fun row groups =>
          groups.insert (id row) (row :: (groups.find (id row)).getD []))
          NatIndexTree.empty).find (id first)).getD [] =
          rest.filter (fun row => id row == id first) from ih]
        simp
      · rw [if_neg same]
        change ((definitionGroups rest id).find key).getD [] = _
        rw [ih]
        simp [List.filter_cons, Nat.beq_eq, Ne.symm same]

/-- Exact membership in the source group used by uninhabitedness equations. -/
theorem definitionGroups_member {α : Type} (rows : List α) (id : α → Nat)
    (key : Nat) (row : α) :
    row ∈ ((definitionGroups rows id).find key).getD [] ↔ row ∈ rows ∧ id row = key := by
  rw [definitionGroups_exact, List.mem_filter]
  simp only [Nat.beq_eq_true_eq]

private theorem positionFold_lookup {α : Type} (entries : List (α × Nat))
    (id : α → Nat) (key : Nat) :
    (entries.foldr (fun (row, position) tree => tree.insert (id row) position)
      NatIndexTree.empty).find key =
      (entries.find? (fun entry => id entry.1 == key)).map Prod.snd := by
  induction entries with
  | nil => rfl
  | cons first rest ih =>
      rcases first with ⟨row, position⟩
      rw [List.foldr_cons, NatIndexTree.find_insert]
      by_cases same : key = id row
      · subst key
        simp [List.find?]
      · rw [if_neg same, ih]
        have no : (id row == key) = false := by
          cases yes : id row == key
          · rfl
          · exact False.elim (same ((by simpa using yes : id row = key)).symm)
        simp [List.find?, no]

/-- Shape lookup is exactly the first matching source occurrence, including
    malformed tables containing duplicate nominal identifiers. -/
theorem firstPositionIndex_exact {α : Type} (rows : List α) (id : α → Nat) (key : Nat) :
    (firstPositionIndex rows id).find key =
      ((numbered rows).find? (fun entry => id entry.1 == key)).map Prod.snd :=
  positionFold_lookup (numbered rows) id key

private theorem positionFold_witness {α : Type} (entries : List (α × Nat))
    (id : α → Nat) (key position : Nat)
    (found : (entries.foldr (fun (row, pos) tree => tree.insert (id row) pos)
      NatIndexTree.empty).find key = some position) :
    ∃ row, (row, position) ∈ entries ∧ id row = key := by
  induction entries with
  | nil => cases found
  | cons first rest ih =>
      rcases first with ⟨row, pos⟩
      rw [List.foldr_cons, NatIndexTree.find_insert] at found
      split at found
      · rename_i same
        cases found
        exact ⟨row, (trustIrListMemConsSelf _ _), same.symm⟩
      · obtain ⟨row, member, same⟩ := ih found
        exact ⟨row, List.mem_cons_of_mem _ member, same⟩

/-- Every shape position really names a source row with the requested id. -/
theorem firstPositionIndex_witness {α : Type} (rows : List α) (id : α → Nat)
    (key position : Nat) (found : (firstPositionIndex rows id).find key = some position) :
    ∃ row, (row, position) ∈ numbered rows ∧ id row = key :=
  positionFold_witness (numbered rows) id key position found

private theorem positionOverride_preserves {α : Type} (entries : List (α × Nat))
    (id : α → Nat) (property : Nat → Nat → Prop)
    (valid : ∀ row position, (row, position) ∈ entries → property (id row) position)
    (tree : NatIndexTree Nat)
    (initial : ∀ key position, tree.find key = some position → property key position) :
    ∀ key position,
      (entries.foldl (fun index (row, pos) =>
        if id row == pos then index.insert pos pos else index) tree).find key = some position →
      property key position := by
  induction entries generalizing tree with
  | nil => exact initial
  | cons first rest ih =>
      rcases first with ⟨row, pos⟩
      rw [List.foldl_cons]
      apply ih (fun row position member => valid row position (List.mem_cons_of_mem _ member))
      intro key position found
      by_cases matching : id row == pos
      · simp only [matching, ite_true, NatIndexTree.find_insert] at found
        split at found
        · rename_i same
          cases found
          have admitted := valid row pos ((trustIrListMemConsSelf _ _))
          have equal : id row = pos := (by simpa using matching)
          simpa only [same, equal] using admitted
        · exact initial key position found
      · simp only [matching, Bool.false_eq_true, ite_false] at found
        exact initial key position found

/-- Matching-position overrides retain source identity. They can change which
    duplicate is selected, but cannot install a row of another nominal type. -/
theorem positionIndex_witness {α : Type} (rows : List α) (id : α → Nat)
    (key position : Nat) (found : (positionIndex rows id).find key = some position) :
    ∃ row, (row, position) ∈ numbered rows ∧ id row = key := by
  apply positionOverride_preserves (numbered rows) id
    (fun key position => ∃ row, (row, position) ∈ numbered rows ∧ id row = key)
    (fun row position member => ⟨row, member, rfl⟩)
    (firstPositionIndex rows id) (firstPositionIndex_witness rows id) key position found

private theorem zip_source_member {α β : Type} (rows : List α) (other : List β)
    (row : α) (value : β) (member : (row, value) ∈ rows.zip other) : row ∈ rows := by
  induction rows generalizing other with
  | nil => cases member
  | cons first rest ih =>
      cases other with
      | nil => cases member
      | cons second tail =>
          cases member with
          | head => exact .head _
          | tail _ member => exact .tail _ (ih tail member)

/-- A numbered source occurrence is still a member of the original table. -/
theorem numbered_source_member {α : Type} (rows : List α) (row : α) (position : Nat)
    (member : (row, position) ∈ numbered rows) : row ∈ rows :=
  zip_source_member rows (List.range rows.length) row position member

/-- A selected execution row is covered by the exact duplicate-definition
    group used to derive conservative uninhabitedness facts. -/
theorem positionIndex_group {α : Type} (rows : List α) (id : α → Nat)
    (key position : Nat) (found : (positionIndex rows id).find key = some position) :
    ∃ row, (row, position) ∈ numbered rows ∧
      row ∈ ((definitionGroups rows id).find key).getD [] := by
  obtain ⟨row, member, same⟩ := positionIndex_witness rows id key position found
  exact ⟨row, member, (definitionGroups_member rows id key row).2
    ⟨numbered_source_member rows row position member, same⟩⟩

/-- The corresponding coverage theorem for first-occurrence shape lookup. -/
theorem firstPositionIndex_group {α : Type} (rows : List α) (id : α → Nat)
    (key position : Nat) (found : (firstPositionIndex rows id).find key = some position) :
    ∃ row, (row, position) ∈ numbered rows ∧
      row ∈ ((definitionGroups rows id).find key).getD [] := by
  obtain ⟨row, member, same⟩ := firstPositionIndex_witness rows id key position found
  exact ⟨row, member, (definitionGroups_member rows id key row).2
    ⟨numbered_source_member rows row position member, same⟩⟩

theorem Index.structPosition_group (source : Environment) (key position : Nat)
    (found : (Index.ofEnvironment source).structPositions.find key = some position) :
    ∃ row, (row, position) ∈ numbered source.structs ∧
      row ∈ (((Index.ofEnvironment source).structDefinitions).find key).getD [] :=
  positionIndex_group source.structs (·.id.index) key position found

theorem Index.enumPosition_group (source : Environment) (key position : Nat)
    (found : (Index.ofEnvironment source).enumPositions.find key = some position) :
    ∃ row, (row, position) ∈ numbered source.enums ∧
      row ∈ (((Index.ofEnvironment source).enumDefinitions).find key).getD [] :=
  positionIndex_group source.enums (·.id.index) key position found

theorem Index.recordPosition_group (source : Environment) (key position : Nat)
    (found : (Index.ofEnvironment source).recordPositions.find key = some position) :
    ∃ row, (row, position) ∈ numbered source.records ∧
      row ∈ (((Index.ofEnvironment source).recordDefinitions).find key).getD [] :=
  positionIndex_group source.records (·.id.index) key position found

theorem Index.structShapePosition_group (source : Environment) (key position : Nat)
    (found : (Index.ofEnvironment source).structShapePositions.find key = some position) :
    ∃ row, (row, position) ∈ numbered source.structs ∧
      row ∈ (((Index.ofEnvironment source).structDefinitions).find key).getD [] :=
  firstPositionIndex_group source.structs (·.id.index) key position found

theorem Index.enumShapePosition_group (source : Environment) (key position : Nat)
    (found : (Index.ofEnvironment source).enumShapePositions.find key = some position) :
    ∃ row, (row, position) ∈ numbered source.enums ∧
      row ∈ (((Index.ofEnvironment source).enumDefinitions).find key).getD [] :=
  firstPositionIndex_group source.enums (·.id.index) key position found

private theorem range_loop_lookup (count : Nat) (tail : List Nat) (position : Nat) :
    trustIrListGet? (List.range.loop count tail) position =
      if position < count then some position else trustIrListGet? tail (position - count) := by
  induction count generalizing tail with
  | zero =>
      change trustIrListGet? tail position = if position < 0 then some position else trustIrListGet? tail (position - 0)
      rw [if_neg (by omega)]
      rfl
  | succ count ih =>
      rw [List.range.loop, ih]
      by_cases before : position < count
      · rw [if_pos before, if_pos (by omega)]
      · rw [if_neg before]
        by_cases boundary : position = count
        · subst position
          rw [if_pos (by omega), Nat.sub_self]
          rfl
        · rw [if_neg (by omega)]
          have offset : position - count = (position - (count + 1)) + 1 := by omega
          rw [offset]
          rfl

/-- Exact lookup in the ascending range used by `numbered`, including the
    out-of-range case. No source-row identity is inferred from membership alone. -/
theorem numbered_range_lookup (count position : Nat) :
    trustIrListGet? (List.range count) position = if position < count then some position else none := by
  rw [List.range, range_loop_lookup]
  split <;> rfl

/-- The nth numbered occurrence carries exactly n, not just an in-range key. -/
theorem numbered_lookup {α : Type} (rows : List α) (position : Nat) :
    trustIrListGet? (numbered rows) position = (trustIrListGet? rows position).map (fun row => (row, position)) := by
  first
  | rw [numbered, List.zip, List.zipWith_get?, numbered_range_lookup]
  | rw [numbered, List.zip, CompilerCompat.listGetConstructive_zipWith, numbered_range_lookup]
  by_cases inside : position < rows.length
  · rw [if_pos inside]
    cases trustIrListGet? rows position <;> rfl
  · rw [if_neg inside, TrustIr.CompilerCompat.listGet?_outside rows position (Nat.le_of_not_lt inside)]
    rfl

/-- A numbered source witness identifies the exact list lookup. -/
theorem numbered_get {α : Type} (rows : List α) (row : α) (position : Nat)
    (member : (row, position) ∈ numbered rows) : trustIrListGet? rows position = some row := by
  obtain ⟨index, atIndex⟩ := List.get_of_mem member
  have indexed : trustIrListGet? (numbered rows) index.val = some (row, position) :=
    TrustIr.CompilerCompat.listGet?_eq_some.mpr ⟨index.isLt, atIndex⟩
  rw [numbered_lookup] at indexed
  cases found : trustIrListGet? rows index.val with
  | none => simp [found] at indexed
  | some actual =>
      simp only [found, Option.map, Option.some.injEq] at indexed
      cases indexed
      exact found

theorem numbered_member_iff_get {α : Type} (rows : List α) (row : α) (position : Nat) :
    (row, position) ∈ numbered rows ↔ trustIrListGet? rows position = some row := by
  constructor
  · exact numbered_get rows row position
  · intro found
    have indexed : trustIrListGet? (numbered rows) position = some (row, position) := by
      rw [numbered_lookup, found]
      rfl
    obtain ⟨inside, same⟩ := TrustIr.CompilerCompat.listGet?_eq_some.mp indexed
    exact List.mem_iff_get.mpr ⟨⟨position, inside⟩, same⟩

theorem numbered_position_unique {α : Type} (rows : List α) (first second : α) (position : Nat)
    (left : (first, position) ∈ numbered rows) (right : (second, position) ∈ numbered rows) :
    first = second := by
  have same := (numbered_get rows first position left).symm.trans (numbered_get rows second position right)
  exact Option.some.inj same

theorem numbered_position_bound {α : Type} (rows : List α) (row : α) (position : Nat)
    (member : (row, position) ∈ numbered rows) : position < rows.length :=
  (TrustIr.CompilerCompat.listGet?_eq_some.mp (numbered_get rows row position member)).1

end TrustIr.SourceLayout
