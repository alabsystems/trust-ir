-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import SemR
import TrustIr.Proofs.ByteMemory

/-! Bool-cell representation in the existing canonical allocation/byte memory.

These lemmas use TrustIr.Memory's actual functions, not another operational
interpreter. Unwritten Bool cells correspond to a one-byte poison image;
defined cells have the 0/1 image produced by typed Bool stores. Freshness is
an explicit invariant, not a consequence of allocation-layout well-formedness.

This is a dependency of an execution refinement, not that refinement. It does
not establish frame lifetime/provenance, finite-u64 exhaustion, source/body
quotation, whole-program nonescape or any original obligation's certificate.
-/

namespace SemR.BoolMemory

open TrustIr (Memory Addr)

/-- The allocation bump must not expose preexisting defined bytes. -/
def Fresh (memory : Memory) : Prop :=
  ∀ address, memory.nextAddr ≤ address → memory.bytes address = none

/-- Poison is the absence of a byte, never a default false or arbitrary Bool. -/
def image : Val → Option (Option UInt8)
  | .bool value => some (some (if value then 1 else 0))
  | .poison .bool => some none
  | _ => none

def allocation (id base : Nat) : TrustIr.Allocation :=
  { id := ⟨id⟩, base := base, size := 1, alive := true,
    origin := .rustStack, requested := 1 }

/-- A live one-byte allocation and its exact typed cell image. No address hash,
    public receipt or unrelated allocation can supply this relation. -/
def CellAt (memory : Memory) (base : Addr) (cell : Cell) : Prop :=
  cell.ty = .bool ∧
  memory.lookup ⟨cell.id⟩ = some (allocation cell.id base) ∧
  image cell.value = some (memory.bytes base)

theorem fresh_empty : Fresh Memory.empty := by
  intro address _
  rfl

theorem alloca_bool_base (memory : Memory) :
    (memory.alloc 1 1 0 .rustStack).fst = memory.nextAddr := by
  simp [Memory.alloc, TrustIr.alignUp]

theorem alloca_bool_next (memory : Memory) :
    (memory.alloc 1 1 0 .rustStack).snd.nextAddr = memory.nextAddr + 1 := by
  simp [Memory.alloc, TrustIr.alignUp]

theorem alloca_bool_bytes (memory : Memory) :
    (memory.alloc 1 1 0 .rustStack).snd.bytes = memory.bytes := by
  rfl

theorem alloca_bool_fresh (memory : Memory) (fresh : Fresh memory) :
    Fresh (memory.alloc 1 1 0 .rustStack).snd := by
  intro address later
  rw [alloca_bool_bytes]
  apply fresh
  rw [alloca_bool_next] at later
  exact Nat.le_trans (Nat.le_succ _) later

theorem alloca_bool_unwritten (memory : Memory) (fresh : Fresh memory) :
    (memory.alloc 1 1 0 .rustStack).snd.readBytes memory.nextAddr 1 = none ∧
    (memory.alloc 1 1 0 .rustStack).snd.readBytesMaybeUninit memory.nextAddr 1 = [none] := by
  have unread := fresh memory.nextAddr (Nat.le_refl _)
  simp [Memory.readBytes, Memory.readBytes.go, Memory.readBytesMaybeUninit,
    Memory.readBytesMaybeUninit.go, alloca_bool_bytes, unread]

theorem alloca_bool_cell (memory : Memory) (fresh : Fresh memory) :
    CellAt (memory.alloc 1 1 0 .rustStack).snd memory.nextAddr
      { id := memory.nextAllocId, ty := .bool, value := .poison .bool } := by
  have unread := fresh memory.nextAddr (Nat.le_refl _)
  simp [CellAt, allocation, image, Memory.lookup, Memory.alloc, TrustIr.alignUp, Memory.bytes]
  simpa [Memory.bytes] using congrArg some unread.symm

theorem alloca_bool_identity (memory : Memory) :
    (memory.alloc 1 1 0 .rustStack).snd.nextAllocId = memory.nextAllocId + 1 := by
  simp [Memory.alloc]

theorem alloca_bool_other_lookup (memory : Memory) (id : Nat)
    (different : memory.nextAllocId ≠ id) :
    (memory.alloc 1 1 0 .rustStack).snd.lookup ⟨id⟩ = memory.lookup ⟨id⟩ := by
  simp [Memory.alloc, Memory.lookup, different]

theorem alloca_bool_preserves_cell (memory : Memory) (base : Addr) (cell : Cell)
    (different : memory.nextAllocId ≠ cell.id) (related : CellAt memory base cell) :
    CellAt (memory.alloc 1 1 0 .rustStack).snd base cell := by
  rcases related with ⟨typed, found, contents⟩
  refine ⟨typed, ?_, ?_⟩
  · rw [alloca_bool_other_lookup memory cell.id different]
    exact found
  · rw [alloca_bool_bytes]
    exact contents

theorem bool_encoding (value : Bool) :
    TrustIr.encodeValue (.bool value) = some [if value then 1 else 0] := by
  cases value <;> rfl

theorem bool_decoding (value : Bool) :
    TrustIr.decodeValue .Bool [if value then 1 else 0] = some (.bool value) := by
  cases value <;> rfl

theorem store_bool_readback (memory : Memory) (address : Addr) (value : Bool) :
    (memory.writeBytes address [if value then 1 else 0]).readBytes address 1 =
      some [if value then 1 else 0] := by
  exact TrustIr.writeBytes_readBytes_single memory address _

theorem store_poison_byte (memory : Memory) (address : Addr) :
    (memory.writeBytesMaybeUninit address [none]).bytes address = none := by
  change (memory.writeImage address (TrustIr.ByteImage.ofList [none])).bytes (address + 0) = none
  rw [Memory.bytes_writeImage_inside memory address 0 _ (by decide)]
  rfl

theorem store_poison_readback (memory : Memory) (address : Addr) :
    (memory.writeBytesMaybeUninit address [none]).readBytes address 1 = none ∧
    (memory.writeBytesMaybeUninit address [none]).readBytesMaybeUninit address 1 = [none] := by
  simp [Memory.readBytes, Memory.readBytes.go, Memory.readBytesMaybeUninit,
    Memory.readBytesMaybeUninit.go, store_poison_byte]

theorem store_bool_other_byte (memory : Memory) (address other : Addr) (value : Bool)
    (different : other ≠ address) :
    (memory.writeBytes address [if value then 1 else 0]).bytes other = memory.bytes other := by
  have outside : other < address ∨ address + 1 ≤ other := by
    by_cases before : other < address
    · exact Or.inl before
    · exact Or.inr (Nat.succ_le_of_lt
        (Nat.lt_of_le_of_ne (Nat.le_of_not_lt before) (Ne.symm different)))
  exact Memory.bytes_writeBytes_outside memory address other _ (by simpa using outside)

theorem store_poison_other_byte (memory : Memory) (address other : Addr)
    (different : other ≠ address) :
    (memory.writeBytesMaybeUninit address [none]).bytes other = memory.bytes other := by
  have outside : other < address ∨ address + 1 ≤ other := by
    by_cases before : other < address
    · exact Or.inl before
    · exact Or.inr (Nat.succ_le_of_lt
        (Nat.lt_of_le_of_ne (Nat.le_of_not_lt before) (Ne.symm different)))
  exact Memory.bytes_writeImage_outside memory address other _ (by simpa using outside)

theorem store_bool_cell (memory : Memory) (address : Addr) (cell : Cell) (value : Bool)
    (related : CellAt memory address cell) :
    CellAt (memory.writeBytes address [if value then 1 else 0]) address
      { cell with value := .bool value } := by
  rcases related with ⟨typed, found, _⟩
  refine ⟨typed, found, ?_⟩
  have written := Memory.bytes_writeBytes_inside memory address 0 [if value then 1 else 0] (by simp)
  simpa [image] using (congrArg some written).symm

theorem store_poison_cell (memory : Memory) (address : Addr) (cell : Cell)
    (related : CellAt memory address cell) :
    CellAt (memory.writeBytesMaybeUninit address [none]) address
      { cell with value := .poison .bool } := by
  rcases related with ⟨typed, found, _⟩
  refine ⟨typed, found, ?_⟩
  simpa [image] using (congrArg some (store_poison_byte memory address)).symm

theorem store_bool_other_cell (memory : Memory) (address other : Addr) (cell : Cell)
    (value : Bool) (different : other ≠ address) (related : CellAt memory other cell) :
    CellAt (memory.writeBytes address [if value then 1 else 0]) other cell := by
  rcases related with ⟨typed, found, contents⟩
  refine ⟨typed, found, ?_⟩
  rw [store_bool_other_byte memory address other value different]
  exact contents

theorem store_poison_other_cell (memory : Memory) (address other : Addr) (cell : Cell)
    (different : other ≠ address) (related : CellAt memory other cell) :
    CellAt (memory.writeBytesMaybeUninit address [none]) other cell := by
  rcases related with ⟨typed, found, contents⟩
  refine ⟨typed, found, ?_⟩
  rw [store_poison_other_byte memory address other different]
  exact contents

/-- The exact update used by SemR's Store changes every subsequent lookup
    through that logical pointer, rather than storing a pointer snapshot. -/
theorem findCell_after_store (cells : List Cell) (cell old : Cell)
    (found : findCell cells cell.id = some old) :
    findCell (putCell cells cell) cell.id = some cell := by
  induction cells with
  | nil => simp [findCell] at found
  | cons head tail induction =>
    by_cases same : head.id = cell.id
    · simp [findCell, putCell, same]
    · simp [findCell, putCell, same] at found ⊢
      exact induction found

theorem store_bool_preserves_fresh (memory : Memory) (address : Addr) (value : Bool)
    (fresh : Fresh memory) (inside : address < memory.nextAddr) :
    Fresh (memory.writeBytes address [if value then 1 else 0]) := by
  intro other later
  have different : other ≠ address := by
    show other ≠ address
    have ordered : address < other := Nat.lt_of_lt_of_le inside later
    exact Ne.symm (Nat.ne_of_lt ordered)
  rw [store_bool_other_byte memory address other value different]
  exact fresh other later

theorem store_poison_preserves_fresh (memory : Memory) (address : Addr)
    (fresh : Fresh memory) (inside : address < memory.nextAddr) :
    Fresh (memory.writeBytesMaybeUninit address [none]) := by
  intro other later
  have different : other ≠ address := by
    have ordered : address < other := Nat.lt_of_lt_of_le inside later
    exact Ne.symm (Nat.ne_of_lt ordered)
  rw [store_poison_other_byte memory address other different]
  exact fresh other later

/- Allocation-layout facts alone cannot prove poison. This actual canonical
   allocation retains a preexisting byte; Fresh is therefore indispensable. -/
private def stale : Memory :=
  Memory.empty.writeBytes 1024 [7]

theorem stale_allocation_retains_byte :
    (stale.alloc 1 1 0 .rustStack).snd.readBytes 1024 1 = some [7] := rfl

def WrongFreshAllocation : Prop :=
  (stale.alloc 1 1 0 .rustStack).snd.readBytes 1024 1 = none

def WrongStoredBool : Prop :=
  (Memory.empty.writeBytes 1024 [1]).readBytes 1024 1 = some [0]

/- The existing decoder accepts any nonzero Bool byte. The typed 0/1 image
   invariant above is deliberately stronger than decoder acceptance. -/
theorem noncanonical_bool_byte_decodes_true :
    TrustIr.decodeValue .Bool [7] = some (.bool true) := rfl

end SemR.BoolMemory
