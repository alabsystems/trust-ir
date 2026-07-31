-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Byte-addressable memory model.
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 4

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
  size   : Nat
  alive  : Bool
  origin : AllocationOrigin
  deriving Repr

/-- The memory state: allocation metadata + byte-level storage. -/
structure Memory where
  allocations : List Allocation
  bytes       : Addr → Option UInt8
  nextAddr    : Addr
  nextAllocId : Nat

instance : Repr Memory where
  reprPrec m _ :=
    "{ allocations := " ++ repr m.allocations
      ++ ", bytes := <fn>, nextAddr := " ++ repr m.nextAddr
      ++ ", nextAllocId := " ++ repr m.nextAllocId ++ " }"

/-- Empty memory state. -/
def Memory.empty : Memory :=
  { allocations := []
  , bytes := fun _ => none
  , nextAddr := 1024  -- reserve low addresses (null page)
  , nextAllocId := 0 }

/-- Check if an address is within a live allocation. -/
def Memory.isAllocated (mem : Memory) (addr : Addr) : Bool :=
  mem.allocations.any fun alloc =>
    alloc.alive && addr >= alloc.base && addr < alloc.base + alloc.size

/-- Check if an address range is within bounds of a live allocation. -/
def Memory.isInBounds (mem : Memory) (addr : Addr) (size : Nat) : Bool :=
  mem.allocations.any fun alloc =>
    alloc.alive && addr >= alloc.base && addr + size <= alloc.base + alloc.size

end TrustIr
