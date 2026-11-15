-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import SemRBoolAccess
import Init.Data.List.Nat.Range

/-! A whole private-Bool-heap representation, using the actual canonical
allocator, stores and SemR cell updates. The arbitrary-length heap starts at
Memory.empty and contains only one-byte private Bool allocations: no foreign
allocations, deallocation or address arithmetic is admitted by this relation.

Its structural ID/frontier/allocation-table/image facts are established from
empty and preserved below. Address injection, bounds and disjointness are
derived, not extra premises of stores. This is not an evaluator or a theorem
about whole execution, permissions, lifetime, source quotation or finite u64.
-/

namespace SemR.BoolMemory

open TrustIr

/-- The placement of the id-th one-byte allocation from canonical empty memory.
    Allocation preservation below derives this placement from Memory.alloc. -/
def heapBase (id : Nat) : Addr := Memory.empty.nextAddr + id

/-- Complete structural representation of the private-Bool-only heap. -/
structure HeapAt (memory : Memory) (cells : List Cell) (nextCell : Nat) : Prop where
  ids : cells.map Cell.id = (List.range nextCell).reverse
  allocations : memory.allocations = cells.map (fun cell => allocation cell.id (heapBase cell.id))
  nextIdentity : memory.nextAllocId = nextCell
  nextAddress : memory.nextAddr = heapBase nextCell
  typed : ∀ cell ∈ cells, cell.ty = .bool
  images : ∀ cell ∈ cells, image cell.value = some (memory.bytes (heapBase cell.id))
  fresh : Fresh memory

theorem heapBase_injective {first second : Nat} (equal : heapBase first = heapBase second) :
    first = second := Nat.add_left_cancel equal

theorem heapBase_disjoint {first second : Nat} (different : first ≠ second) :
    heapBase first + 1 ≤ heapBase second ∨ heapBase second + 1 ≤ heapBase first := by
  rcases Nat.lt_or_gt_of_ne different with before | after
  · left
    simpa [heapBase, Nat.add_assoc] using
      Nat.add_le_add_left (Nat.succ_le_of_lt before) Memory.empty.nextAddr
  · right
    simpa [heapBase, Nat.add_assoc] using
      Nat.add_le_add_left (Nat.succ_le_of_lt after) Memory.empty.nextAddr

theorem empty_heap : HeapAt Memory.empty [] 0 := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, fresh_empty⟩ <;> simp

theorem HeapAt.cell_identity_below {memory : Memory} {cells : List Cell} {nextCell : Nat}
    (heap : HeapAt memory cells nextCell) (cell : Cell) (member : cell ∈ cells) :
    cell.id < nextCell := by
  have present : cell.id ∈ cells.map Cell.id := List.mem_map_of_mem member
  rw [heap.ids] at present
  simpa only [List.mem_reverse, List.mem_range] using present

theorem HeapAt.cell_exists {memory : Memory} {cells : List Cell} {nextCell : Nat}
    (heap : HeapAt memory cells nextCell) (id : Nat) (below : id < nextCell) :
    ∃ cell ∈ cells, cell.id = id := by
  have present : id ∈ cells.map Cell.id := by
    rw [heap.ids]
    simpa only [List.mem_reverse, List.mem_range] using below
  exact List.mem_map.mp present

theorem HeapAt.ids_nodup {memory : Memory} {cells : List Cell} {nextCell : Nat}
    (heap : HeapAt memory cells nextCell) : (cells.map Cell.id).Nodup := by
  rw [heap.ids]
  apply List.pairwise_reverse.mpr
  exact (List.nodup_range (n := nextCell)).imp (fun different => Ne.symm different)

private theorem cell_eq_of_id (cells : List Cell) :
    (cells.map Cell.id).Nodup → ∀ {first second : Cell}, first ∈ cells → second ∈ cells →
      first.id = second.id → first = second := by
  induction cells with
  | nil => simp
  | cons head tail induction =>
    intro unique first second firstMember secondMember equal
    have uniqueParts := List.nodup_cons.mp unique
    rcases List.mem_cons.mp firstMember with rfl | firstMember
    · rcases List.mem_cons.mp secondMember with rfl | secondMember
      · rfl
      · exact False.elim (uniqueParts.1 (List.mem_map.mpr ⟨second, secondMember, equal.symm⟩))
    · rcases List.mem_cons.mp secondMember with same | secondMember
      · subst second
        exact False.elim (uniqueParts.1 (List.mem_map.mpr ⟨first, firstMember, equal⟩))
      · exact induction uniqueParts.2 firstMember secondMember equal

theorem HeapAt.cell_identity_injective {memory : Memory} {cells : List Cell} {nextCell : Nat}
    (heap : HeapAt memory cells nextCell) (first second : Cell)
    (firstMember : first ∈ cells) (secondMember : second ∈ cells)
    (equal : first.id = second.id) : first = second :=
  cell_eq_of_id cells heap.ids_nodup firstMember secondMember equal

theorem HeapAt.cell_bounds {memory : Memory} {cells : List Cell} {nextCell : Nat}
    (heap : HeapAt memory cells nextCell) (cell : Cell) (member : cell ∈ cells) :
    heapBase cell.id + 1 ≤ memory.nextAddr ∧ heapBase cell.id < memory.nextAddr := by
  have below := heap.cell_identity_below cell member
  rw [heap.nextAddress]
  constructor
  · simpa [heapBase, Nat.add_assoc] using
      Nat.add_le_add_left (Nat.succ_le_of_lt below) Memory.empty.nextAddr
  · exact Nat.add_lt_add_left below Memory.empty.nextAddr

theorem HeapAt.cells_disjoint {memory : Memory} {cells : List Cell} {nextCell : Nat}
    (heap : HeapAt memory cells nextCell) (first second : Cell)
    (firstMember : first ∈ cells) (secondMember : second ∈ cells) (different : first ≠ second) :
    heapBase first.id + 1 ≤ heapBase second.id ∨
      heapBase second.id + 1 ≤ heapBase first.id := by
  apply heapBase_disjoint
  intro equal
  exact different (heap.cell_identity_injective first second firstMember secondMember equal)

private theorem mapped_lookup (cells : List Cell) (id : Nat) (member : id ∈ cells.map Cell.id) :
    (cells.map (fun cell => allocation cell.id (heapBase cell.id))).find?
      (fun record => record.id == AllocId.mk id) = some (allocation id (heapBase id)) := by
  induction cells with
  | nil => simp at member
  | cons head tail induction =>
    by_cases equal : head.id = id
    · simp [allocation, equal]
    · have tailMember : id ∈ tail.map Cell.id := by
        rcases List.mem_cons.mp member with same | member
        · exact False.elim (equal same.symm)
        · exact member
      simpa [allocation, equal] using induction tailMember

theorem HeapAt.cell_at {memory : Memory} {cells : List Cell} {nextCell : Nat}
    (heap : HeapAt memory cells nextCell) (cell : Cell) (member : cell ∈ cells) :
    CellAt memory (heapBase cell.id) cell := by
  refine ⟨heap.typed cell member, ?_, heap.images cell member⟩
  unfold Memory.lookup
  rw [heap.allocations]
  exact mapped_lookup cells cell.id (List.mem_map_of_mem member)

theorem HeapAt.allocation_ids_nodup {memory : Memory} {cells : List Cell} {nextCell : Nat}
    (heap : HeapAt memory cells nextCell) :
    (memory.allocations.map (fun record => record.id.id)).Nodup := by
  rw [heap.allocations]
  simpa [List.map_map, allocation] using heap.ids_nodup

theorem HeapAt.allocation_identity_below {memory : Memory} {cells : List Cell} {nextCell : Nat}
    (heap : HeapAt memory cells nextCell) (record : Allocation)
    (member : record ∈ memory.allocations) : record.id.id < memory.nextAllocId := by
  rw [heap.allocations] at member
  rcases List.mem_map.mp member with ⟨cell, cellMember, rfl⟩
  simpa [allocation, heap.nextIdentity] using heap.cell_identity_below cell cellMember

theorem HeapAt.allocation_identity_injective {memory : Memory} {cells : List Cell} {nextCell : Nat}
    (heap : HeapAt memory cells nextCell) (first second : Allocation)
    (firstMember : first ∈ memory.allocations) (secondMember : second ∈ memory.allocations)
    (equal : first.id = second.id) : first = second := by
  rw [heap.allocations] at firstMember secondMember
  rcases List.mem_map.mp firstMember with ⟨firstCell, _, rfl⟩
  rcases List.mem_map.mp secondMember with ⟨secondCell, _, rfl⟩
  have ids : firstCell.id = secondCell.id := congrArg AllocId.id equal
  simp [ids]

theorem HeapAt.allocation_bounds {memory : Memory} {cells : List Cell} {nextCell : Nat}
    (heap : HeapAt memory cells nextCell) (record : Allocation)
    (member : record ∈ memory.allocations) :
    record.base + record.size ≤ memory.nextAddr ∧ record.base < memory.nextAddr := by
  rw [heap.allocations] at member
  rcases List.mem_map.mp member with ⟨cell, cellMember, rfl⟩
  exact heap.cell_bounds cell cellMember

theorem HeapAt.allocations_disjoint {memory : Memory} {cells : List Cell} {nextCell : Nat}
    (heap : HeapAt memory cells nextCell) (first second : Allocation)
    (firstMember : first ∈ memory.allocations) (secondMember : second ∈ memory.allocations)
    (different : first ≠ second) :
    first.base + first.size ≤ second.base ∨ second.base + second.size ≤ first.base := by
  rw [heap.allocations] at firstMember secondMember
  rcases List.mem_map.mp firstMember with ⟨firstCell, _, rfl⟩
  rcases List.mem_map.mp secondMember with ⟨secondCell, _, rfl⟩
  apply heapBase_disjoint
  intro equal
  apply different
  simp [equal]

private theorem findCell_eq_of_mem (cells : List Cell) :
    (cells.map Cell.id).Nodup → ∀ cell ∈ cells, findCell cells cell.id = some cell := by
  induction cells with
  | nil => simp
  | cons head tail induction =>
    intro unique cell member
    by_cases equal : head.id = cell.id
    · have same : head = cell :=
        cell_eq_of_id (head :: tail) unique (by simp) member equal
      simp [findCell, same]
    · have tailMember : cell ∈ tail := by
        rcases List.mem_cons.mp member with rfl | member
        · exact False.elim (equal rfl)
        · exact member
      simpa [findCell, equal] using induction (List.nodup_cons.mp unique).2 cell tailMember

theorem HeapAt.findCell_at {memory : Memory} {cells : List Cell} {nextCell : Nat}
    (heap : HeapAt memory cells nextCell) (cell : Cell) (member : cell ∈ cells) :
    findCell cells cell.id = some cell := findCell_eq_of_mem cells heap.ids_nodup cell member

private theorem findCell_none_above (cells : List Cell) (nextCell : Nat)
    (below : ∀ cell ∈ cells, cell.id < nextCell) : findCell cells nextCell = none := by
  induction cells with
  | nil => rfl
  | cons head tail induction =>
    have different : head.id ≠ nextCell := Nat.ne_of_lt (below head (by simp))
    simp [findCell, different]
    exact induction (fun cell member => below cell (List.mem_cons_of_mem head member))

theorem HeapAt.allocation_guard {memory : Memory} {cells : List Cell} {nextCell : Nat}
    (heap : HeapAt memory cells nextCell) : findCell cells nextCell = none :=
  findCell_none_above cells nextCell (fun cell member => heap.cell_identity_below cell member)

theorem HeapAt.allocate {memory : Memory} {cells : List Cell} {nextCell : Nat}
    (heap : HeapAt memory cells nextCell) :
    HeapAt (memory.alloc 1 1 0 .rustStack).snd
      ({ id := nextCell, ty := .bool, value := .poison .bool } :: cells) (nextCell + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, alloca_bool_fresh memory heap.fresh⟩
  · simp [List.range_succ, List.reverse_append, heap.ids]
  · simp [Memory.alloc, TrustIr.alignUp, heap.nextIdentity, heap.nextAddress,
      heap.allocations, heapBase, allocation]
  · simpa [heap.nextIdentity] using alloca_bool_identity memory
  · rw [alloca_bool_next, heap.nextAddress]
    simp [heapBase, Nat.add_assoc]
  · intro cell member
    rcases List.mem_cons.mp member with rfl | member
    · rfl
    · exact heap.typed cell member
  · intro cell member
    rw [alloca_bool_bytes]
    rcases List.mem_cons.mp member with rfl | member
    · have unwritten := heap.fresh memory.nextAddr (Nat.le_refl _)
      simpa [image, heap.nextAddress] using congrArg some unwritten.symm
    · exact heap.images cell member

private theorem putCell_ids (cells : List Cell) (updated : Cell) :
    (putCell cells updated).map Cell.id = cells.map Cell.id := by
  induction cells with
  | nil => rfl
  | cons head tail induction =>
    by_cases equal : head.id = updated.id
    · simp [putCell, equal]
    · simp [putCell, equal, induction]

private theorem putCell_allocations (cells : List Cell) (updated : Cell) :
    (putCell cells updated).map (fun cell => allocation cell.id (heapBase cell.id)) =
      cells.map (fun cell => allocation cell.id (heapBase cell.id)) := by
  induction cells with
  | nil => rfl
  | cons head tail induction =>
    by_cases equal : head.id = updated.id
    · simp [putCell, equal]
    · simp [putCell, equal, induction]

private theorem putCell_members (cells : List Cell) (updated : Cell)
    (unique : (cells.map Cell.id).Nodup) : ∀ cell ∈ putCell cells updated,
      cell = updated ∨ (cell ∈ cells ∧ cell.id ≠ updated.id) := by
  induction cells with
  | nil => simp [putCell]
  | cons head tail induction =>
    have uniqueParts := List.nodup_cons.mp unique
    intro cell member
    by_cases equal : head.id = updated.id
    · simp only [putCell, equal, beq_self_eq_true, ite_true] at member
      rcases List.mem_cons.mp member with rfl | member
      · exact Or.inl rfl
      · refine Or.inr ⟨List.mem_cons_of_mem head member, ?_⟩
        intro same
        exact uniqueParts.1 (List.mem_map.mpr ⟨cell, member, same.trans equal.symm⟩)
    · simp [putCell, equal] at member
      rcases member with rfl | member
      · exact Or.inr ⟨by simp, equal⟩
      · rcases induction uniqueParts.2 cell member with same | ⟨old, different⟩
        · exact Or.inl same
        · exact Or.inr ⟨List.mem_cons_of_mem head old, different⟩

theorem HeapAt.store_bool {memory : Memory} {cells : List Cell} {nextCell : Nat}
    (heap : HeapAt memory cells nextCell) (cell : Cell) (member : cell ∈ cells) (value : Bool) :
    HeapAt (memory.writeBytes (heapBase cell.id) [if value then 1 else 0])
      (putCell cells { cell with value := .bool value }) nextCell := by
  refine ⟨?_, ?_, heap.nextIdentity, heap.nextAddress, ?_, ?_, ?_⟩
  · rw [putCell_ids, heap.ids]
  · change memory.allocations = _
    rw [putCell_allocations, heap.allocations]
  · intro current present
    rcases putCell_members cells _ heap.ids_nodup current present with rfl | ⟨old, _⟩
    · exact heap.typed cell member
    · exact heap.typed current old
  · intro current present
    rcases putCell_members cells _ heap.ids_nodup current present with rfl | ⟨old, different⟩
    · have written := Memory.bytes_writeBytes_inside memory (heapBase cell.id) 0
        [if value then 1 else 0] (by simp)
      simpa [image] using (congrArg some written).symm
    · have addresses : heapBase current.id ≠ heapBase cell.id := by
        intro equal
        exact different (heapBase_injective equal)
      rw [store_bool_other_byte memory (heapBase cell.id) (heapBase current.id) value addresses]
      exact heap.images current old
  · exact store_bool_preserves_fresh memory (heapBase cell.id) value heap.fresh
      (heap.cell_bounds cell member).2

theorem HeapAt.store_poison {memory : Memory} {cells : List Cell} {nextCell : Nat}
    (heap : HeapAt memory cells nextCell) (cell : Cell) (member : cell ∈ cells) :
    HeapAt (memory.writeBytesMaybeUninit (heapBase cell.id) [none])
      (putCell cells { cell with value := .poison .bool }) nextCell := by
  refine ⟨?_, ?_, heap.nextIdentity, heap.nextAddress, ?_, ?_, ?_⟩
  · rw [putCell_ids, heap.ids]
  · change memory.allocations = _
    rw [putCell_allocations, heap.allocations]
  · intro current present
    rcases putCell_members cells _ heap.ids_nodup current present with rfl | ⟨old, _⟩
    · exact heap.typed cell member
    · exact heap.typed current old
  · intro current present
    rcases putCell_members cells _ heap.ids_nodup current present with rfl | ⟨old, different⟩
    · simpa [image] using
        (congrArg some (store_poison_byte memory (heapBase cell.id))).symm
    · have addresses : heapBase current.id ≠ heapBase cell.id := by
        intro equal
        exact different (heapBase_injective equal)
      rw [store_poison_other_byte memory (heapBase cell.id) (heapBase current.id) addresses]
      exact heap.images current old
  · exact store_poison_preserves_fresh memory (heapBase cell.id) heap.fresh
      (heap.cell_bounds cell member).2

theorem HeapAt.semStore_bool {state : MachineState} {cells : List Cell} {nextCell : Nat}
    (heap : HeapAt state.memory cells nextCell) (cell : Cell) (member : cell ∈ cells)
    (ptr source : ValueId) (value : Bool) (operand : PointerAt state ptr (heapBase cell.id) cell)
    (stored : state.lookupValue source = some (.bool value)) :
    ∃ result, Sem.run (TrustIr.semStore .Bool ptr source) state = .ok ((), result) ∧
      HeapAt result.memory (putCell cells { cell with value := .bool value }) nextCell := by
  exact ⟨_, semStore_bool_cell state ptr source (heapBase cell.id) cell value false
    (heap.cell_at cell member) operand stored, heap.store_bool cell member value⟩

theorem HeapAt.semStore_poison {state : MachineState} {cells : List Cell} {nextCell : Nat}
    (heap : HeapAt state.memory cells nextCell) (cell : Cell) (member : cell ∈ cells)
    (ptr source : ValueId) (operand : PointerAt state ptr (heapBase cell.id) cell)
    (stored : state.lookupValue source = some (.partial [none])) :
    ∃ result, Sem.run (TrustIr.semStore .Bool ptr source) state = .ok ((), result) ∧
      HeapAt result.memory (putCell cells { cell with value := .poison .bool }) nextCell := by
  exact ⟨_, semStore_poison_cell state ptr source (heapBase cell.id) cell
    (heap.cell_at cell member) operand stored, heap.store_poison cell member⟩

theorem duplicate_cell_ids_refuse (memory : Memory) (first second : Cell)
    (sameFirst : first.id = 0) (sameSecond : second.id = 0) :
    ¬ HeapAt memory [first, second] 2 := by
  intro heap
  have ids := heap.ids
  simp [sameFirst, sameSecond, List.range_succ] at ids

private def firstAllocation : Addr × Memory := Memory.empty.alloc 1 1 0 .rustStack

private def secondAllocation : Addr × Memory := firstAllocation.snd.alloc 1 1 0 .rustStack

private def writtenTwoAllocations : Memory :=
  secondAllocation.snd.writeBytes firstAllocation.fst [1]

theorem two_allocations_have_distinct_bases :
    firstAllocation.fst ≠ secondAllocation.fst := by decide

theorem second_allocation_placement :
    secondAllocation.fst = heapBase 1 := rfl

theorem store_first_preserves_second_poison :
    writtenTwoAllocations.readBytes firstAllocation.fst 1 = some [1] ∧
    writtenTwoAllocations.readBytes secondAllocation.fst 1 = none := ⟨rfl, rfl⟩

theorem store_first_other_cell_readback :
    writtenTwoAllocations.readBytes secondAllocation.fst 1 = none :=
  store_first_preserves_second_poison.2

def WrongOtherCellContents : Prop :=
  writtenTwoAllocations.readBytes secondAllocation.fst 1 = some [1]

def WrongReusedAllocationBase : Prop :=
  secondAllocation.fst = firstAllocation.fst

end SemR.BoolMemory
