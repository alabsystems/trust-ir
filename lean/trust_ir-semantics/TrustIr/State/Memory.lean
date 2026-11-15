-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Byte-addressable memory model.
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 4

import TrustIr.State.ByteImage

namespace TrustIr

/-!
# Memory Model

Byte-addressable, allocation-aware memory model for TrustIr.
This is the unified memory model that supports all three language
paradigms (Rust borrows, Swift ARC, C raw pointers).

## Key types

- `AllocId`: unique identifier for each allocation
- `Allocation`: metadata for one allocation (base, size, alive)
- `AllocationOrigin`: which language paradigm created this allocation
- `Memory`: the complete memory state
-/

/-- Unique identifier for a memory allocation. -/
structure AllocId where
  id : Nat
  deriving DecidableEq, Hashable, Repr

/-- Address type (byte-level). -/
abbrev Addr := Nat

/-- Origin of an allocation — which language paradigm created it.
    This determines the applicable permission discipline. -/
inductive AllocationOrigin where
  | rustStack  : AllocationOrigin
  | rustHeap   : AllocationOrigin
  | swiftHeap  : AllocationOrigin   -- ARC-managed
  | cleanHeap  : AllocationOrigin   -- Perceus RC-managed (Clean); refcount
                                    -- discipline identical to swiftHeap —
                                    -- the tag is runtime provenance
  | cMalloc    : AllocationOrigin
  | cStack     : AllocationOrigin
  deriving DecidableEq, Repr

/-- Metadata for one memory allocation. -/
structure Allocation where
  id     : AllocId
  base   : Addr
  /-- The allocation's FOOTPRINT: the requested bytes plus any heap slack
      tail (`Memory.alloc`). Bounds of every access. -/
  size   : Nat
  alive  : Bool
  origin : AllocationOrigin
  /-- The bytes the program REQUESTED (`size` without the slack tail). Only
      the borrow operand rule reads it (`borrowTarget`). -/
  requested : Nat
  deriving Repr

/-- Bytes explicitly left unwritten by a typed aggregate lane. The allocation
    identity is retained separately from the byte image and its padding. -/
structure UnwrittenRange where
  allocation : AllocId
  start : Addr
  stop : Addr
  deriving Repr

/-- The memory state: allocation metadata + byte-level storage. -/
structure Memory where
  allocations : List Allocation
  storage     : ByteStore
  nextAddr    : Addr
  nextAllocId : Nat
  unwritten : List UnwrittenRange := []

/-- Point lookup is derived from the authoritative retained images. -/
def Memory.bytes (mem : Memory) (address : Addr) : Option UInt8 := mem.storage.get address

/-- A structural, immutable snapshot of the actual byte store. -/
def Memory.readImage (mem : Memory) (address count : Nat) : ByteImage :=
  mem.storage.snapshot address count

instance : Repr Memory where
  reprPrec m _ :=
    "{ allocations := " ++ repr m.allocations
      ++ ", storage := <compact images>, nextAddr := " ++ repr m.nextAddr
      ++ ", nextAllocId := " ++ repr m.nextAllocId ++ " }"

/-- Empty memory state. -/
def Memory.empty : Memory :=
  { allocations := []
  , storage := .empty
  , nextAddr := 1024  -- reserve low addresses (null page)
  , nextAllocId := 0 }

/-- The allocation with this id, live or dead (ids are never reused). -/
def Memory.lookup (mem : Memory) (id : AllocId) : Option Allocation :=
  mem.allocations.find? fun a => a.id == id

trustIrDenseMatch
/-- Every actual byte write clips the old lane record. A byte copy carries
    no such record. Zero-length operations leave it unchanged. -/
def Memory.forgetUnwritten (mem : Memory) (addr length : Nat) : Memory :=
  { mem with unwritten :=
    match mem.unwritten with
    | [] => []
    | lanes =>
      if length == 0 then lanes
      else
        let stop := addr + length
        trustIrListBind lanes fun lane =>
          if lane.stop ≤ addr || stop ≤ lane.start then [lane]
          else
            (if lane.start < addr then [{ lane with stop := addr }] else []) ++
            (if stop < lane.stop then [{ lane with start := stop }] else []) }

trustIrDenseMatch
def Memory.recordUnwritten (mem : Memory) (allocation : AllocId) (addr : Addr)
    (lanes : List (Nat × Nat)) : Memory :=
  match lanes with
  | [] => mem
  | lanes =>
    { mem with unwritten := mem.unwritten ++ lanes.filterMap (fun (offset, length) =>
      if length == 0 then none
      else some { allocation, start := addr + offset, stop := addr + offset + length }) }

def Memory.isUnwritten (mem : Memory) (allocation : AllocId) (addr : Addr) : Bool :=
  mem.unwritten.any fun lane => lane.allocation == allocation && lane.start ≤ addr && addr < lane.stop

/-- The provenance an ADDRESS recovers (an integer cast to a pointer, pointer
    bytes loaded from memory): the allocation, live or dead, whose footprint
    contains it, else one it is one past the end of, the OLDEST first (the
    allocation list is newest-first). Mirrors the reference interpreter's
    `MemoryState::try_pointer_from_address` exactly. -/
def Memory.provenanceAt (mem : Memory) (addr : Addr) : Option AllocId :=
  let oldestFirst := mem.allocations.reverse
  match oldestFirst.find? (fun a => a.base ≤ addr && addr < a.base + a.size) with
  | some a => some a.id
  | none => (oldestFirst.find? (fun a => addr == a.base + a.size)).map (·.id)

/-- Check if an address is within some live allocation. An ADDRESS-level
    predicate: since 2026-09-30 no semantics reads it — an access is checked
    against the allocation its pointer was derived from (`Sem.checkedAccess`).
    Kept for the origin-irrelevance lemmas over `Memory.alloc`. -/
def Memory.isAllocated (mem : Memory) (addr : Addr) : Bool :=
  mem.allocations.any fun alloc =>
    alloc.alive && addr >= alloc.base && addr < alloc.base + alloc.size

/-- Check if an address range is within bounds of some live allocation (an
    address-level predicate no semantics reads; see `Memory.isAllocated`). -/
def Memory.isInBounds (mem : Memory) (addr : Addr) (size : Nat) : Bool :=
  mem.allocations.any fun alloc =>
    alloc.alive && addr >= alloc.base && addr + size <= alloc.base + alloc.size

end TrustIr

#trustIrAxiomsExact TrustIr.Memory.forgetUnwritten == []
#trustIrAxiomsExact TrustIr.Memory.recordUnwritten == []
