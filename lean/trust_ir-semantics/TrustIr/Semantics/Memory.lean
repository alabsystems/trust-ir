-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Memory semantics: Load, Store, Alloca, GEP.
-- Phase 2 of the formalization roadmap.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 6 Phase 2
--
-- These operations implement byte-addressable memory with type-aware
-- encoding/decoding. The memory model is allocation-aware: every access
-- must target a live allocation that is in-bounds.

import TrustIr.Inst
import TrustIr.Semantics.Monad

namespace TrustIr

/-!
# Memory Semantics

## Overview

Memory instructions operate on the byte-addressable Memory in the
MachineState. Each memory access is checked against live allocations
for bounds safety.

## Instructions

- Alloca: Allocate size bytes on the stack. Returns a pointer to the
  fresh allocation. The count field optionally specifies an array count.
- Load: Read Ty.byteSize bytes from memory at the pointer address
  and decode them into a typed Value.
- Store: Encode a typed Value into bytes and write them to memory
  at the pointer address.
- GEP (GetElementPtr): Compute a new pointer by adding type-aware
  offsets to a base pointer. Mirrors LLVM GEP instruction.

## Byte encoding

Values are encoded in little-endian byte order, matching the most common
target architectures (x86, ARM in LE mode). The encoding is invertible:
decodeValue (encodeValue v) = some v for well-typed values.

## Safety model

All memory accesses check:
1. The pointer is not null (address 0 is in the reserved null page)
2. The access is within a live allocation bounds
3. The type matches what was stored (for Load)

Violations produce SemError.ub (undefined behavior).
-/

-- =================================================================
-- Byte size computation
-- =================================================================

/-- Declared metadata type of each fat-pointer kind at the model's fixed
    64-bit pointer width (`Ty.byteSize .Ptr = some 8`). Mirrors Rust
    `FatPtrKind::metadata_ty` (crates/trust-ir/src/shape.rs) at
    `pointer_bits = 64`: slice/str metadata is the element/byte count
    (`U64`); trait-object metadata is the vtable pointer (`Ptr`). -/
def FatPtrKind.metadataTy : FatPtrKind → Ty
  | .Slice _       => .U64
  | .Str           => .U64
  | .TraitObject _ => .Ptr

/-- Shallow structural check that a runtime value inhabits a fat-pointer
    metadata type: a 64-bit int for `U64`, or a (possibly null) thin pointer
    for `Ptr`. Used both when constructing and when storing a fat pointer so
    malformed externally-supplied values fail closed at the memory boundary. -/
def metadataInhabits : Ty → Value → Bool
  | .U64, .int 64 _ => true
  | .Ptr, .ptr _    => true
  | .Ptr, .nullPtr  => true
  | _,    _         => false

/-- Dynamic well-formedness guard needed specifically at the typed Store
    boundary. Non-fat values retain the existing encoder contract; a fat type
    requires a fat value whose metadata inhabits that kind's canonical lane. -/
def fatPtrStoreValueValid : Ty → Value → Bool
  | .FatPtr kind, .fatPtr _ metadata => metadataInhabits kind.metadataTy metadata
  | .FatPtr _,    _                  => false
  | _,            _                  => true

/-- Compute the byte size of a type.
    Returns none for types with no fixed byte size (aggregates, etc.). -/
def Ty.byteSize : Ty -> Option Nat
  | .Bool  => some 1
  | .I8    => some 1
  | .I16   => some 2
  | .I32   => some 4
  | .I64   => some 8
  | .I128  => some 16
  -- Issue #53: unsigned integer byte sizes match their signed counterparts.
  | .U8    => some 1
  | .U16   => some 2
  | .U32   => some 4
  | .U64   => some 8
  | .U128  => some 16
  | .F32   => some 4
  | .F64   => some 8
  | .Ptr   => some 8   -- 64-bit pointers
  -- Pointer-like reference types are 64-bit (8 bytes)
  | .Ref _    => some 8
  | .RefMut _ => some 8
  | .PtrConst _ => some 8
  | .PtrMut _ => some 8
  | .Rc _     => some 8
  -- A wide pointer is two 64-bit lanes: data address then metadata.
  | .FatPtr _ => some 16
  -- Unit is zero-sized
  | .Unit     => some 0
  -- Never, Tuple, Enum, Struct, Array, Func and ty aggregates: context-dependent
  | _         => none

-- =================================================================
-- Value encoding/decoding (little-endian byte layout)
-- =================================================================

/-- Encode an unsigned integer value as little-endian bytes. -/
def encodeIntBytes (val : Int) (numBytes : Nat) : List UInt8 :=
  let rec go (remaining : Nat) (v : Nat) : List UInt8 :=
    match remaining with
    | 0 => []
    | n + 1 =>
      let byte := UInt8.ofNat (v % 256)
      byte :: go n (v / 256)
  go numBytes val.toNat

/-- Decode a list of little-endian bytes into an unsigned integer value. -/
def decodeIntBytes (bytes : List UInt8) : Nat :=
  let rec go (bs : List UInt8) (shift : Nat) : Nat :=
    match bs with
    | [] => 0
    | b :: rest => b.toNat * (256 ^ shift) + go rest (shift + 1)
  go bytes 0

/-- Encode a Value into a list of bytes for storage in memory.
    Returns none for values that cannot be encoded (aggregates, undef). -/
def encodeValue : Value -> Option (List UInt8)
  | .int width val =>
    let numBytes := width / 8
    -- Ensure unsigned representation for encoding
    let modulus := (2 : Int) ^ width
    let uval := ((val % modulus) + modulus) % modulus
    some (encodeIntBytes uval numBytes)
  | .bool b =>
    some [if b then 1 else 0]
  | .ptr addr =>
    -- 64-bit pointer encoded as 8 bytes LE
    some (encodeIntBytes (Int.ofNat addr) 8)
  | .float _ =>
    -- Float encoding: axiomatized. Store as 8 bytes (f64 representation).
    -- Full IEEE 754 byte-level encoding is future work.
    some (List.replicate 8 0)  -- placeholder: proper float encoding in Phase 5
  | .nullPtr =>
    -- Null pointer = address 0 encoded as 8 bytes
    some (List.replicate 8 0)
  | .aggregate _ => none   -- Aggregates: element-by-element in Phase 4
  | .vector _ => none      -- Vectors stay in SSA for this first executable path
  | .frame _ => none       -- Binding frames cannot be stored to memory (Rust-side validation)
  -- ty supremacy aggregate values live in SSA registers, not memory.
  -- No byte encoding is defined for them; frontends must lower these
  -- through explicit aggregate/scalar stores before hitting memory.
  | .set _ => none
  | .sequence _ => none
  | .record _ => none
  | .closure _ _ => none
  -- A fat pointer's byte image is its two 64-bit lanes back-to-back:
  -- data address followed by canonical metadata. The static Ty determines
  -- whether the second lane is a length or a vtable pointer when decoding;
  -- encoding therefore accepts exactly one 8-byte metadata image and fails
  -- closed on malformed Value.fatPtr payloads.
  | .fatPtr data metadata =>
    match metadata with
    | .int 64 value =>
      let modulus := (2 : Int) ^ 64
      let unsigned := ((value % modulus) + modulus) % modulus
      some (encodeIntBytes (Int.ofNat data) 8 ++ encodeIntBytes unsigned 8)
    | .ptr metadataAddr =>
      some (encodeIntBytes (Int.ofNat data) 8 ++
        encodeIntBytes (Int.ofNat metadataAddr) 8)
    | .nullPtr =>
      some (encodeIntBytes (Int.ofNat data) 8 ++ List.replicate 8 0)
    | _ => none
  -- A partial (poison) image has no fixed-width encoding: it is written back
  -- verbatim by `semStore` via `writeBytesMaybeUninit`, never through the
  -- typed encoder. Returning none here keeps the STRICT store/atomic paths
  -- (which route through `encodeValue`) from silently accepting poison.
  | .partial _ => none
  | .undef _ => none       -- Undef: no defined encoding

/-- Decode a list of bytes into a Value given a type.
    Returns none if the byte count does not match the type byte size. -/
def decodeValue (ty : Ty) (bytes : List UInt8) : Option Value :=
  match ty with
  | .Bool =>
    match bytes with
    | [b] => some (.bool (b.toNat != 0))
    | _   => none
  | .I8 | .U8 =>
    if bytes.length == 1 then some (.int 8 (Int.ofNat (decodeIntBytes bytes)))
    else none
  | .I16 | .U16 =>
    if bytes.length == 2 then some (.int 16 (Int.ofNat (decodeIntBytes bytes)))
    else none
  | .I32 | .U32 =>
    if bytes.length == 4 then some (.int 32 (Int.ofNat (decodeIntBytes bytes)))
    else none
  | .I64 | .U64 =>
    if bytes.length == 8 then some (.int 64 (Int.ofNat (decodeIntBytes bytes)))
    else none
  | .I128 | .U128 =>
    if bytes.length == 16 then some (.int 128 (Int.ofNat (decodeIntBytes bytes)))
    else none
  | .F32 =>
    if bytes.length == 4 then some (.float 0.0)  -- axiomatized: proper decode in Phase 5
    else none
  | .F64 =>
    if bytes.length == 8 then some (.float 0.0)  -- axiomatized: proper decode in Phase 5
    else none
  | .Ptr | .Ref _ | .RefMut _ | .PtrConst _ | .PtrMut _ | .Rc _ =>
    if bytes.length == 8 then
      let addr := decodeIntBytes bytes
      if addr == 0 then some .nullPtr
      else some (.ptr addr)
    else none
  | .FatPtr kind =>
    if bytes.length == 16 then
      let data := decodeIntBytes (bytes.take 8)
      let metadataBytes := bytes.drop 8
      match kind with
      | .Slice _ | .Str =>
        some (.fatPtr data (.int 64 (Int.ofNat (decodeIntBytes metadataBytes))))
      | .TraitObject _ =>
        let metadataAddr := decodeIntBytes metadataBytes
        let metadata := if metadataAddr == 0 then .nullPtr else .ptr metadataAddr
        some (.fatPtr data metadata)
    else none
  | .Unit =>
    -- Unit is zero-sized; decode from empty byte list
    if bytes.length == 0 then some (.aggregate [])
    else none
  | _ => none  -- Struct, Array, Func, Never, Tuple, Enum, Set, Sequence, Record, Closure: not directly decodable

-- =================================================================
-- Memory read/write helpers
-- =================================================================

/-- Read n bytes starting at addr from memory.
    Returns none if any byte is uninitialized. -/
def Memory.readBytes (mem : Memory) (addr : Addr) (n : Nat) : Option (List UInt8) :=
  let rec go (remaining : Nat) (currentAddr : Addr) : Option (List UInt8) :=
    match remaining with
    | 0 => some []
    | k + 1 =>
      match mem.bytes currentAddr with
      | none => none  -- uninitialized byte
      | some b =>
        match go k (currentAddr + 1) with
        | none => none
        | some rest => some (b :: rest)
  go n addr

/-- Read n bytes starting at addr as their raw PER-BYTE init image, WITHOUT
    collapsing to none on an uninitialized byte: `some b` for an initialized
    byte, `none` for a never-written one. The copy-propagates-poison `Load`
    path (`semLoad`, non-strict) uses this to materialize a `.partial` transport
    value once the bounds/permission checks have already passed and `readBytes`
    reported that some byte is uninitialized. Mirrors the Rust reference
    interpreter's `Memory::read_maybe_uninit` (crates/trust-ir/src/interpret.rs,
    commit 530fdd5). -/
def Memory.readBytesMaybeUninit (mem : Memory) (addr : Addr) (n : Nat)
    : List (Option UInt8) :=
  let rec go (remaining : Nat) (currentAddr : Addr) : List (Option UInt8) :=
    match remaining with
    | 0 => []
    | k + 1 => mem.bytes currentAddr :: go k (currentAddr + 1)
  go n addr

/-- Write a partially-initialized byte IMAGE verbatim: `some b` sets the byte,
    `none` RESTORES (leaves) the destination byte uninitialized. This is the
    store half of copy-propagates-poison — the uninitialized-ness of the source
    lane is preserved at the destination, so a padding/niche lane round-trip
    never fabricates a defined value. Mirrors the Rust reference interpreter's
    `Memory::write_maybe_uninit`. -/
def Memory.writeBytesMaybeUninit (mem : Memory) (addr : Addr)
    (image : List (Option UInt8)) : Memory :=
  let rec updateBytes (bytes : Addr -> Option UInt8) (currentAddr : Addr)
      (remaining : List (Option UInt8)) : Addr -> Option UInt8 :=
    match remaining with
    | [] => bytes
    | b :: rest =>
      let bytes' := fun a => if a == currentAddr then b else bytes a
      updateBytes bytes' (currentAddr + 1) rest
  { mem with bytes := updateBytes mem.bytes addr image }

/-- Write a list of bytes starting at addr into memory.
    Returns the updated memory. -/
def Memory.writeBytes (mem : Memory) (addr : Addr) (data : List UInt8) : Memory :=
  let rec updateBytes (bytes : Addr -> Option UInt8) (currentAddr : Addr) (remaining : List UInt8)
      : Addr -> Option UInt8 :=
    match remaining with
    | [] => bytes
    | b :: rest =>
      let bytes' := fun a => if a == currentAddr then some b else bytes a
      updateBytes bytes' (currentAddr + 1) rest
  { mem with bytes := updateBytes mem.bytes addr data }

/-- Find the allocation that contains the given address. -/
def Memory.findAllocation (mem : Memory) (addr : Addr) : Option Allocation :=
  mem.allocations.find? fun alloc =>
    alloc.alive && addr >= alloc.base && addr < alloc.base + alloc.size

/-- Find the allocation that contains the given address range. -/
def Memory.findAllocationRange (mem : Memory) (addr : Addr) (size : Nat) : Option Allocation :=
  mem.allocations.find? fun alloc =>
    alloc.alive && addr >= alloc.base && addr + size <= alloc.base + alloc.size

/-- Create a new allocation in memory.
    Returns the allocation base address and the updated memory. -/
def Memory.alloc (mem : Memory) (size : Nat) (origin : AllocationOrigin) : Addr × Memory :=
  let allocId := AllocId.mk mem.nextAllocId
  let baseAddr := mem.nextAddr
  let allocation : Allocation :=
    { id     := allocId
    , base   := baseAddr
    , size   := size
    , alive  := true
    , origin := origin }
  let mem' : Memory :=
    { mem with
      allocations := allocation :: mem.allocations
      nextAddr    := baseAddr + size
      nextAllocId := mem.nextAllocId + 1 }
  (baseAddr, mem')

-- =================================================================
-- Alloca semantics
-- =================================================================

/-- Evaluate an Alloca instruction.
    Allocates stack space for count elements of type ty.
    Returns a pointer to the allocated memory.

    Alloca always succeeds (no OOM in semantics model -- memory is
    unbounded). The allocation is marked with AllocationOrigin.rustStack.

    Mirrors Rust Inst::Alloca -/
def semAlloca (ty : Ty) (countId : Option ValueId) : Sem ValueId := do
  let byteSize ← match ty.byteSize with
    | some s => pure s
    | none   => Sem.throwTypeError "Alloca: type has no byte size"
  -- Determine count (default 1 if not specified)
  let count ← match countId with
    | none => pure 1
    | some cid => do
      let countVal ← Sem.lookupValue cid
      match countVal with
      | .int _ n =>
        if n <= 0 then Sem.throwUB "Alloca: count must be positive"
        else pure n.toNat
      | _ => Sem.throwTypeError "Alloca: count must be an integer"
  let totalSize := byteSize * count
  -- Allocate memory
  let s ← Sem.getState
  let (baseAddr, mem') := s.memory.alloc totalSize .rustStack
  -- Set permission to Owned for the new allocation
  let allocId := AllocId.mk (s.memory.nextAllocId)
  let perms' := s.permissions.set allocId .owned
  Sem.setState { s with memory := mem', permissions := perms' }
  -- Return pointer to allocated memory
  Sem.bindFresh (.ptr baseAddr)

/-- Map the IR-level `AllocOrigin` to the memory model's `AllocationOrigin`.
    `CleanHeap` (Clean's Perceus RC cells) maps to `cleanHeap`, whose refcount
    discipline is identical to `swiftHeap` — no origin-sensitive rule
    distinguishes them; the tag records which runtime owns the cell. -/
def AllocOrigin.toAllocationOrigin : AllocOrigin → AllocationOrigin
  | .RustHeap  => .rustHeap
  | .SwiftHeap => .swiftHeap
  | .CMalloc   => .cMalloc
  | .CleanHeap => .cleanHeap

/-- Evaluate a HeapAlloc instruction. Like `semAlloca`, but the allocation is
    tagged with the heap `origin` (so `AllocationOrigin.rustHeap`/`.swiftHeap`/
    `.cleanHeap`/`.cMalloc` finally become reachable in the dynamic semantics)
    and owned. -/
def semHeapAlloc (ty : Ty) (countId : Option ValueId) (origin : AllocOrigin) : Sem ValueId := do
  let byteSize ← match ty.byteSize with
    | some s => pure s
    | none   => Sem.throwTypeError "HeapAlloc: type has no byte size"
  let count ← match countId with
    | none => pure 1
    | some cid => do
      let countVal ← Sem.lookupValue cid
      match countVal with
      | .int _ n =>
        if n <= 0 then Sem.throwUB "HeapAlloc: count must be positive"
        else pure n.toNat
      | _ => Sem.throwTypeError "HeapAlloc: count must be an integer"
  let totalSize := byteSize * count
  let s ← Sem.getState
  let (baseAddr, mem') := s.memory.alloc totalSize origin.toAllocationOrigin
  let allocId := AllocId.mk (s.memory.nextAllocId)
  let perms' := s.permissions.set allocId .owned
  Sem.setState { s with memory := mem', permissions := perms' }
  Sem.bindFresh (.ptr baseAddr)

/-- Evaluate a `GlobalAddr` instruction: materialize a pointer to a module-level
    global. Faithful to the Rust reference interpreter's `global_pointer`
    (interpret.rs) in the observable the Lean model can express — POINTER IDENTITY
    / ALIASING: the first `GlobalAddr` of a `GlobalId` reserves a fresh address
    from the shared allocator and caches `GlobalId -> addr` in
    `MachineState.globals`; every later `GlobalAddr` of the same global returns the
    cached address, so they alias and compare equal. Routing through the allocator
    makes the reserved address collision-free with stack/heap allocations by
    construction.

    PARTIAL (documented, NOT faked): the global's true storage SIZE and
    INITIALIZER contents are not modeled — `semGlobalAddr` has no module context
    (the global's type/initializer live in the `Module`, not threaded into `Sem`).
    It reserves ONE byte (size 1, not 0: a 0-size allocation would not advance the
    allocator's `nextAddr`, so DISTINCT globals would collide at the same address —
    the size-1 reservation gives each fresh global a distinct address while keeping
    the cache aliasing repeats of the SAME global). The reserved byte is
    uninitialized, so a `Load` through a global pointer fails to decode and ERRORS
    rather than fabricating bytes. Content-faithful global storage is a follow-up
    that threads the module into the evaluator. -/
def semGlobalAddr (global : GlobalId) : Sem ValueId := do
  let s ← Sem.getState
  match s.lookupGlobal global with
  | some addr => Sem.bindFresh (.ptr addr)
  | none =>
    let (baseAddr, mem') := s.memory.alloc 1 .rustHeap
    let allocId := AllocId.mk s.memory.nextAllocId
    let perms' := s.permissions.set allocId .owned
    Sem.setState { s with
      memory := mem'
      permissions := perms'
      globals := (global, baseAddr) :: s.globals }
    Sem.bindFresh (.ptr baseAddr)

-- =================================================================
-- Load semantics
-- =================================================================

/-- Is the access at byte address `addr` UNDER-ALIGNED for its declared
    alignment? A `some a` (with `a > 0`) alignment demands `addr % a == 0`;
    `some 0` and `none` (no explicit alignment constraint carried on this
    access) never fault. Mirrors the Rust reference interpreter's
    `checked_access` alignment gate (crates/trust-ir/src/interpret.rs:
    `address % align != 0` is UB, with `align` the access's declared alignment;
    the frontend emits the correct power-of-two `align`, e.g. `align 1` on the
    `[u8; 8]` → `u64` transmute load, commit dd27b78). Only NON-atomic Load /
    Store carry and check this; the atomic path keeps its own discipline. -/
def isMisaligned : Option Nat → Nat → Bool
  | some a, addr => a != 0 && addr % a != 0
  | none,   _    => false

/-- The SCALAR decode types that participate in copy-propagates-poison: a
    plain (non-strict) load of one of these whose byte range has an
    uninitialized byte transports a `.partial` poison image instead of
    faulting. Aggregate / fat-pointer / unit loads keep the strict all-or-UB
    decode. Mirrors the Rust reference interpreter's `partial_load_ty`
    (crates/trust-ir/src/interpret.rs, commit 530fdd5). -/
def isPartialLoadTy : Ty → Bool
  | .I8 | .I16 | .I32 | .I64 | .I128
  | .U8 | .U16 | .U32 | .U64 | .U128
  | .Isize | .Usize | .Char
  | .F16 | .F32 | .F64
  | .Bool | .Ptr
  | .PtrConst _ | .PtrMut _ | .Ref _ | .RefMut _ | .Rc _ => true
  | _ => false

/-- Evaluate a Load instruction.
    Reads ty.byteSize bytes from memory at the pointer address and
    decodes them into a typed value.

    Safety checks:
    - Pointer is not null
    - Access is within a live allocation

    Initialization discipline (`strict` selects it): a STRICT load (`strict =
    true`, used for VOLATILE plain loads; the atomic loads keep their own
    all-or-UB read in `Atomic.lean`) requires every byte of the access to be
    initialized — an uninitialized byte is UB. A NON-strict (plain) SCALAR load
    implements copy-propagates-poison: if the byte range has any uninitialized
    byte it yields an inert `.partial` transport value instead of faulting, so a
    whole-lane aggregate copy that reads padding or an inactive niche payload
    can move those bytes verbatim to their destination. A fully-initialized
    load decodes exactly as before. The `.partial` value only faults if it is
    later INSPECTED (see `Sem.rejectPartial`).

    Alignment (`align`): a non-atomic access whose address is under-aligned for
    the declared alignment is UB (`isMisaligned`, mirroring interpret.rs
    `checked_access`). `align = none` (or `some 0`) imposes no constraint. The
    atomic path (`Atomic.lean`) keeps its own discipline.

    Mirrors Rust Inst::Load (`eval_load`'s `strict` flag, commit 530fdd5;
    `align` gate, commit dd27b78). -/
def semLoad (ty : Ty) (ptrId : ValueId) (strict : Bool := false)
    (align : Option Nat := none) : Sem ValueId := do
  let ptrVal ← Sem.lookupValue ptrId
  let addr ← match ptrVal with
    | .ptr a    => pure a
    | .nullPtr  => Sem.throwUB "Load: null pointer dereference"
    | _         => Sem.throwTypeError "Load: operand is not a pointer"
  -- Check for null
  if addr == 0 then Sem.throwUB "Load: null pointer dereference"
  -- Get byte size
  let byteSize ← match ty.byteSize with
    | some s => pure s
    | none   => Sem.throwTypeError "Load: type has no byte size"
  -- Check bounds
  let s ← Sem.getState
  if !s.memory.isInBounds addr byteSize then
    Sem.throwUB "Load: access is out of bounds"
  -- Check alignment (non-atomic accesses only).
  if isMisaligned align addr then
    Sem.throwUB "Load: unaligned access (address not aligned to declared alignment)"
  -- Read bytes. A fully-initialized range decodes as before. When some byte is
  -- uninitialized, a non-strict SCALAR load transports the partial byte image
  -- as poison (`.partial`); a strict load — or a non-scalar decode type — keeps
  -- the all-or-UB discipline.
  match s.memory.readBytes addr byteSize with
  | some bytes =>
    match decodeValue ty bytes with
    | some v => Sem.bindFresh v
    | none   => Sem.throwTypeError "Load: failed to decode bytes"
  | none =>
    if !strict && isPartialLoadTy ty then
      Sem.bindFresh (.partial (s.memory.readBytesMaybeUninit addr byteSize))
    else
      Sem.throwUB "Load: reading uninitialized memory"

-- =================================================================
-- Store semantics
-- =================================================================

/-- Evaluate a Store instruction.
    Encodes a typed value into bytes and writes them to memory at the
    pointer address.

    Safety checks:
    - Pointer is not null
    - Access is within a live allocation
    - Value can be encoded to bytes

    Initialization discipline (`strict`): a NON-strict store of a `.partial`
    (poison) value writes its byte IMAGE verbatim — uninitialized bytes stay
    uninitialized at the destination — the store half of copy-propagates-poison.
    A STRICT store (`strict = true`, VOLATILE plain stores; atomic stores keep
    their own encoder-based path in `Atomic.lean`) rejects a `.partial` value as
    UB. Every non-`.partial` value stores exactly as before.

    Alignment (`align`): as for `semLoad`, a non-atomic store whose address is
    under-aligned for the declared alignment is UB (`isMisaligned`).

    Mirrors Rust Inst::Store (`eval_store`'s `strict` flag, commit 530fdd5;
    `align` gate, commit dd27b78). -/
def semStore (ty : Ty) (ptrId valueId : ValueId) (strict : Bool := false)
    (align : Option Nat := none) : Sem Unit := do
  let ptrVal ← Sem.lookupValue ptrId
  let addr ← match ptrVal with
    | .ptr a    => pure a
    | .nullPtr  => Sem.throwUB "Store: null pointer dereference"
    | _         => Sem.throwTypeError "Store: first operand is not a pointer"
  -- Check for null
  if addr == 0 then Sem.throwUB "Store: null pointer dereference"
  -- Get byte size
  let byteSize ← match ty.byteSize with
    | some s => pure s
    | none   => Sem.throwTypeError "Store: type has no byte size"
  -- Check bounds
  let s ← Sem.getState
  if !s.memory.isInBounds addr byteSize then
    Sem.throwUB "Store: access is out of bounds"
  -- Check alignment (non-atomic accesses only).
  if isMisaligned align addr then
    Sem.throwUB "Store: unaligned access (address not aligned to declared alignment)"
  -- Look up the value being stored.
  let val ← Sem.lookupValue valueId
  if val.isPartial then
    -- Copy-propagates-poison transport: a partial byte image moves to memory
    -- verbatim (non-strict stores only). A strict (volatile/atomic) store of a
    -- poison value is UB.
    match val with
    | .partial image =>
      if strict then
        Sem.throwUB "Store: strict (atomic/volatile) store of a partially-initialized value"
      else if image.length != byteSize then
        Sem.throwTypeError "Store: partial image size does not match type size"
      else
        Sem.modifyState fun st =>
          { st with memory := st.memory.writeBytesMaybeUninit addr image }
    | _ => Sem.throwTypeError "Store: cannot encode value"
  else
    -- Encode value
    if !(fatPtrStoreValueValid ty val) then
      Sem.throwTypeError "Store: fat-pointer value does not inhabit the kind's canonical lanes"
    let encoded ← match encodeValue val with
      | some bs => pure bs
      | none    => Sem.throwTypeError "Store: cannot encode value"
    -- Verify encoded size matches type
    if encoded.length != byteSize then
      Sem.throwTypeError "Store: encoded size does not match type size"
    -- Write bytes
    let mem' := s.memory.writeBytes addr encoded
    Sem.modifyState fun st => { st with memory := mem' }

-- =================================================================
-- GEP (GetElementPtr) semantics
-- =================================================================

/-- Compute the byte offset for a GEP index given a pointee type.
    For arrays: offset = index * element_byte_size
    For structs: offset = field offset (requires struct metadata)

    In Phase 2 we handle the simple case: all indices multiply by
    the pointee type byte size. Struct field offsets are Phase 4. -/
def gepByteOffset (pointeeTy : Ty) (index : Int) : Except SemError Nat :=
  match pointeeTy.byteSize with
  | some elemSize =>
    if index < 0 then .error (.ub "GEP: negative index")
    else .ok (index.toNat * elemSize)
  | none => .error (.typeError "GEP: pointee type has no byte size")

/-- Evaluate a GEP (GetElementPtr) instruction.
    Computes a new pointer by adding type-aware offsets to a base pointer.

    GEP takes a base pointer and a list of indices. For Phase 2, we
    support the common case: a single index into an array of the
    pointee type. Multi-level indexing (struct then array) is Phase 4.

    This mirrors LLVM GEP: the first index offsets the base pointer
    by multiples of the pointee type size.

    Mirrors Rust Inst::GEP -/
def semGEP (pointeeTy : Ty) (baseId : ValueId) (indexIds : List ValueId) : Sem ValueId := do
  let baseVal ← Sem.lookupValue baseId
  let baseAddr ← match baseVal with
    | .ptr a    => pure a
    | .nullPtr  => Sem.throwUB "GEP: null base pointer"
    | _         => Sem.throwTypeError "GEP: base is not a pointer"
  -- Process indices: accumulate byte offset
  let mut totalOffset : Nat := 0
  for idxId in indexIds do
    let idxVal ← Sem.lookupValue idxId
    match idxVal with
    | .int _ idx =>
      match gepByteOffset pointeeTy idx with
      | .ok off => totalOffset := totalOffset + off
      | .error e => throw e
    | _ => Sem.throwTypeError "GEP: index is not an integer"
  -- Compute result address
  let resultAddr := baseAddr + totalOffset
  Sem.bindFresh (.ptr resultAddr)

-- =================================================================
-- Fat-pointer trio (PtrData / PtrMetadata / PtrFromParts)
-- =================================================================
--
-- Two regimes, keyed on the STATIC ptrTy:
--
--  * THIN pointer-like (`Ptr`/`Ref`/`RefMut`/`PtrConst`/`PtrMut`/`Rc`):
--    mirrors the Rust reference interpreter line-for-line
--    (crates/trust-ir/src/interpret.rs eval_ptr_data / eval_ptr_metadata /
--    eval_ptr_from_parts): the data lane is the pointer itself, the
--    metadata lane is Unit (`Value.aggregate []`), and the declared
--    metadataTy must be `Unit`.
--
--  * FAT (`Ty.FatPtr kind`): a real `(data, metadata)` runtime value
--    (`Value.fatPtr`). `PtrData`/`PtrMetadata` project, `PtrFromParts`
--    injects (guarded by `metadataInhabits`), and the round-trip
--    `PtrFromParts (PtrData p) (PtrMetadata p) = p` is proved at the value
--    level (`fatPtrFromParts_data_metadata`, Proofs/MemoryProps.lean) and
--    the Sem level (`semFatPtr_roundTrip`, Proofs/MemorySafety.lean).
--    The Rust reference interpreter implements the same three operations and
--    16-byte memory image. Executable fixtures on both sides pin the agreement.

/-- Unit value, the Lean denotation of `Ty.Unit`. Matches the
    `decodeValue .Unit` convention above. -/
def unitValue : Value := .aggregate []

/-- Does a declared metadata type match a fat-pointer kind's metadata
    type? Structural form of `metadataTy == kind.metadataTy` — spelled as
    a two-argument match (rather than through `Ty`'s derived `BEq`, which
    does not kernel-reduce) so proofs can discharge the reflexive
    instance `metadataTyMatches kind.metadataTy kind = true` by `rfl`.
    The static check the Rust validator performs via
    `check_pointer_metadata_ty` (crates/trust-ir-build/src/validate.rs). -/
def metadataTyMatches : Ty → FatPtrKind → Bool
  | .U64, .Slice _       => true
  | .U64, .Str           => true
  | .Ptr, .TraitObject _ => true
  | _,    _              => false

/-- Canonical thin-pointer value for a stored fat-pointer data address. -/
def fatPtrDataLane : Nat → Value
  | 0             => .nullPtr
  | Nat.succ data => .ptr (Nat.succ data)

/-- Value-level data projection of a fat-pointer value: the data lane as a
    thin pointer. `none` on every non-`.fatPtr` value. -/
def fatPtrDataValue : Value → Option Value
  | .fatPtr data _ => some (fatPtrDataLane data)
  | _              => none

/-- Value-level metadata projection of a fat-pointer value. -/
def fatPtrMetadataValue : Value → Option Value
  | .fatPtr _ metadata => some metadata
  | _                  => none

/-- Value-level fat-pointer injection: a (possibly null) thin data pointer
    plus a metadata value. `.nullPtr` injects as data address 0, and
    `fatPtrDataValue` maps that address back to `.nullPtr`. This matches the
    Rust interpreter's `NullPtr` lane and makes the pointer trio agree even at
    the null boundary. -/
def fatPtrFromPartsValue : Value → Value → Option Value
  | .ptr a,   m => some (.fatPtr a m)
  | .nullPtr, m => some (.fatPtr 0 m)
  | _,        _ => none

/-- Evaluate `PtrData`: extract the data-address lane.

    Fat path (`Ty.FatPtr`): project the data lane of a `.fatPtr` as a thin
    `.ptr`. Thin path: provenance-preserving identity on the pointer
    (mirrors interpret.rs eval_ptr_data). -/
def semPtrData (ptrTy : Ty) (ptrId : ValueId) : Sem ValueId := do
  match ptrTy with
  | .FatPtr kind => do
    let ptrVal ← Sem.lookupValue ptrId
    if !(fatPtrStoreValueValid (.FatPtr kind) ptrVal) then
      Sem.throwTypeError "PtrData: operand does not inhabit the fat-pointer kind"
    else
      match fatPtrDataValue ptrVal with
      | some v => Sem.bindFresh v
      | none   => Sem.throwTypeError "PtrData: operand is not a fat-pointer value"
  | _ =>
    if ptrTy.isPointerLike then do
      let ptrVal ← Sem.lookupValue ptrId
      match ptrVal with
      | .ptr a   => Sem.bindFresh (.ptr a)
      | .nullPtr => Sem.bindFresh .nullPtr
      | _        => Sem.throwTypeError "PtrData: operand is not a pointer value"
    else
      Sem.throwTypeError "PtrData: expected pointer-like type"

/-- Evaluate `PtrMetadata`: extract the metadata lane.

    Fat path: the declared metadataTy must match the kind's metadata type
    (the static check the Rust validator performs via
    `check_pointer_metadata_ty`); the stored metadata value is projected
    unchanged. Thin path: metadata is Unit (mirrors interpret.rs
    eval_ptr_metadata, including the `metadata_ty == Unit` guard). -/
def semPtrMetadata (ptrTy : Ty) (metadataTy : Ty) (ptrId : ValueId) : Sem ValueId := do
  match ptrTy with
  | .FatPtr kind => do
    if !(metadataTyMatches metadataTy kind) then
      Sem.throwTypeError "PtrMetadata: declared metadata type does not match the fat-pointer kind"
    else do
      let ptrVal ← Sem.lookupValue ptrId
      if !(fatPtrStoreValueValid (.FatPtr kind) ptrVal) then
        Sem.throwTypeError "PtrMetadata: operand does not inhabit the fat-pointer kind"
      else
        match fatPtrMetadataValue ptrVal with
        | some m => Sem.bindFresh m
        | none   => Sem.throwTypeError "PtrMetadata: operand is not a fat-pointer value"
  | _ =>
    if ptrTy.isPointerLike then do
      let ptrVal ← Sem.lookupValue ptrId
      match ptrVal with
      | .ptr _ | .nullPtr =>
        if metadataTy == .Unit then
          Sem.bindFresh unitValue
        else
          Sem.throwTypeError "PtrMetadata: thin pointer metadata is Unit"
      | _ => Sem.throwTypeError "PtrMetadata: operand is not a pointer value"
    else
      Sem.throwTypeError "PtrMetadata: expected pointer-like type"

/-- Evaluate `PtrFromParts`: rebuild a pointer from a data pointer and
    metadata.

    Fat path: the declared metadataTy must match the kind's metadata type,
    the metadata operand must structurally inhabit it
    (`metadataInhabits` — the dynamic injection guard), and the data
    operand must be a thin pointer; the result is a `.fatPtr`. Thin path:
    identity on the data pointer with a Unit metadata operand (mirrors
    interpret.rs eval_ptr_from_parts). -/
def semPtrFromParts (ptrTy : Ty) (metadataTy : Ty)
    (dataId metadataId : ValueId) : Sem ValueId := do
  match ptrTy with
  | .FatPtr kind => do
    if !(metadataTyMatches metadataTy kind) then
      Sem.throwTypeError "PtrFromParts: declared metadata type does not match the fat-pointer kind"
    else do
      let metaVal ← Sem.lookupValue metadataId
      if !(metadataInhabits kind.metadataTy metaVal) then
        Sem.throwTypeError "PtrFromParts: metadata operand does not inhabit the declared metadata type"
      else do
        let dataVal ← Sem.lookupValue dataId
        match fatPtrFromPartsValue dataVal metaVal with
        | some v => Sem.bindFresh v
        | none   => Sem.throwTypeError "PtrFromParts: data operand is not a thin pointer"
  | _ =>
    if ptrTy.isPointerLike then do
      if metadataTy != .Unit then
        Sem.throwTypeError "PtrFromParts: thin pointer metadata is Unit"
      else do
        let metaVal ← Sem.lookupValue metadataId
        match metaVal with
        | .aggregate [] => do
          let dataVal ← Sem.lookupValue dataId
          match dataVal with
          | .ptr a   => Sem.bindFresh (.ptr a)
          | .nullPtr => Sem.bindFresh .nullPtr
          | _        => Sem.throwTypeError "PtrFromParts: data operand is not a pointer"
        | _ => Sem.throwTypeError "PtrFromParts: metadata operand is not Unit"
    else
      Sem.throwTypeError "PtrFromParts: expected pointer-like type"

-- =================================================================
-- Dealloc semantics
-- =================================================================

/-- Find a live allocation whose base address equals the given address.
    Dealloc requires the pointer to identify the start of an allocation:
    freeing an interior pointer is UB (matches C/Rust semantics). -/
def Memory.findAllocationAtBase (mem : Memory) (addr : Addr) : Option Allocation :=
  mem.allocations.find? fun alloc => alloc.alive && alloc.base == addr

/-- Clear the permission entry for an allocation (set to none). Mirrors
    TrustIr.Semantics.ARC.clearPermission but scoped to generic dealloc. -/
def clearPermissionAt (permissions : PermissionMap) (allocId : AllocId) : PermissionMap :=
  fun id' => if id' == allocId then none else permissions id'

/-- Clear the refcount entry for an allocation (set to none). -/
def clearRefCountAt (refCounts : RefCountMap) (allocId : AllocId) : RefCountMap :=
  fun id' => if id' == allocId then none else refCounts id'

/-- Evaluate a Dealloc instruction.

    Frees the heap allocation identified by the pointer operand. The
    pointer MUST point exactly at the allocation's base address; freeing
    an interior pointer is UB, matching the C free and Rust
    Box::drop contracts. The allocation's permission must allow
    deallocation (Permission.canDealloc): Owned (Rust Box, C malloc)
    and rawPtr (C — allowed but treated as UB-prone) qualify; unique /
    shared borrows and ARC-managed refs do not. ARC allocations are
    freed through semRelease (TrustIr.Semantics.ARC).

    Observable effect: marks the allocation dead, clears its permission
    entry, and clears its refcount entry. Subsequent loads/stores on
    any address in the allocation raise UB via the alive check in
    Memory.isInBounds.

    Errors:
    - nullPtr / addr = 0 -> throwUB (double-free protection).
    - Non-pointer operand -> throwTypeError.
    - No live allocation at addr as base -> throwUB (double-free or
      freeing interior pointer).
    - Permission forbids dealloc (e.g. sharedBorrow) -> throwUB.

    Mirrors Rust Inst::Dealloc (crates/trust_ir/src/inst.rs). -/
def semDealloc (ptrId : ValueId) : Sem Unit := do
  let ptrVal ← Sem.lookupValue ptrId
  let addr ← match ptrVal with
    | .ptr a   => pure a
    | .nullPtr => Sem.throwUB "Dealloc: null pointer dereference"
    | _        => Sem.throwTypeError "Dealloc: operand is not a pointer"
  if addr == 0 then Sem.throwUB "Dealloc: null pointer dereference"
  let s ← Sem.getState
  -- Must free at the allocation's base: interior free is UB.
  let alloc ← match s.memory.findAllocationAtBase addr with
    | some a => pure a
    | none   => Sem.throwUB "Dealloc: no live allocation at base address (double-free or interior pointer)"
  -- The allocation's permission (if any is recorded) must allow dealloc.
  -- Untracked permissions are treated as UB — frontends that emit
  -- Dealloc must emit a matching Alloca or Borrow/ARC setup first.
  match s.permissions.get alloc.id with
  | none =>
    Sem.throwUB "Dealloc: allocation has no permission entry"
  | some perm =>
    if !perm.canDealloc then
      Sem.throwUB "Dealloc: permission does not allow deallocation"
    else
      -- Mark the allocation dead and clear its permission / refcount.
      let memory' :=
        { s.memory with
          allocations := s.memory.allocations.map (fun a =>
            if a.id == alloc.id then { a with alive := false } else a) }
      let permissions' := clearPermissionAt s.permissions alloc.id
      let refCounts' := clearRefCountAt s.refCounts alloc.id
      Sem.setState { s with
        memory := memory'
        permissions := permissions'
        refCounts := refCounts' }

-- =================================================================
-- Memory safety predicates (for theorem statements)
-- =================================================================

/-- Predicate: an address is within a live allocation.
    Used in memory safety theorems. -/
def isAllocatedPred (mem : Memory) (addr : Addr) : Prop :=
  mem.allocations.any fun alloc =>
    alloc.alive && addr >= alloc.base && addr < alloc.base + alloc.size

/-- Predicate: an address range is within bounds of a live allocation. -/
def isInBoundsPred (mem : Memory) (addr : Addr) (size : Nat) : Prop :=
  mem.allocations.any fun alloc =>
    alloc.alive && addr >= alloc.base && addr + size <= alloc.base + alloc.size

/-- Predicate: a pointer is not null. -/
def isNotNull (v : Value) : Prop :=
  match v with
  | .ptr addr => addr != 0
  | _ => False

/-- Predicate: an address is properly aligned for a type. -/
def isAligned (addr : Addr) (ty : Ty) : Prop :=
  match ty.byteSize with
  | some size => addr % size == 0
  | none => True  -- No alignment requirement for unsized types

end TrustIr
