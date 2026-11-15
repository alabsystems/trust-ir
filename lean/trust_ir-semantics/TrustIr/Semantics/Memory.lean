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
import TrustIr.Semantics.FloatFormat
import TrustIr.Semantics.IntRepresentation
import TrustIr.Semantics.TypedInteger

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

A float's byte image depends on its STATIC width, which the bare `Value` does
not carry, so floats are encoded and decoded only by the typed entry points
`encodeValueAt` / `decodeValueAt` (via `Semantics/FloatFormat.lean`). Every
memory access (plain, atomic, global initializer, SeqMap cell) goes through
them; the untyped `encodeValue` / `decodeValue` refuse floats.

## Safety model

All memory accesses check (`Sem.accessAddr`):
1. The pointer is not null (address 0 is in the reserved null page) and
   carries PROVENANCE: the allocation it was derived from
2. That allocation is live, the address is aligned, and the access lies
   within that allocation's bounds — never a neighbour's
3. The type matches what was stored (for Load)

Violations produce SemError.ub (undefined behavior).
-/

-- =================================================================
-- Byte size computation
-- =================================================================

/-- Declared metadata type of each fat-pointer kind at the model's fixed
    64-bit pointer width (`Ty.byteSize .Ptr = some 8`). Mirrors Rust
    `FatPtrKind::metadata_ty` (crates/trust-ir/src/shape.rs) at
    `pointer_bits = 64`: slice/str/container-len metadata is the
    element/byte count (`U64`); trait-object and container-vtable metadata is
    the vtable pointer (`Ptr`). The container-tail kinds are classified by
    what their METADATA means, never by what the data pointer addresses:
    `ContainerVtable` must never land on the length lane. -/
def FatPtrKind.metadataTy : FatPtrKind → Ty
  | .Slice _         => .U64
  | .Str             => .U64
  | .ContainerLen    => .U64
  | .TraitObject _   => .Ptr
  | .ContainerVtable => .Ptr

trustIrDenseMatch
/-- Shallow structural check that a runtime value inhabits a fat-pointer
    metadata type: a 64-bit int for `U64`, or a (possibly null) thin pointer
    for `Ptr`. Used both when constructing and when storing a fat pointer so
    malformed externally-supplied values fail closed at the memory boundary. -/
def metadataInhabits : Ty → Value → Bool
  | .U64, .int 64 _ => true
  | .Ptr, .ptr _ _  => true
  | .Ptr, .nullPtr  => true
  | _,    _         => false

/-- Dynamic well-formedness guard needed specifically at the typed Store
    boundary. Non-fat values retain the existing encoder contract; a fat type
    requires a fat value whose metadata inhabits that kind's canonical lane. -/
def fatPtrStoreValueValid : Ty → Value → Bool
  | .FatPtr kind, .fatPtr _ _ metadata => metadataInhabits kind.metadataTy metadata
  | .FatPtr _,    _                  => false
  | _,            _                  => true

trustIrDenseMatch
/-- The scalar lanes admitted by the module validator. Their memory images
    are packed without padding and their natural alignment is their byte size.
    Pointer-sized, pointer, 128-bit and nested-vector lanes are not admitted. -/
def vectorScalarByteSize : Ty → Option Nat
  | .Bool | .I8 | .U8 => some 1
  | .I16 | .U16 | .F16 => some 2
  | .I32 | .U32 | .F32 => some 4
  | .I64 | .U64 | .F64 => some 8
  | _ => none

trustIrDenseMatch
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
  | .Isize | .Usize => some 8
  | .Char  => some 4
  | .F16   => some 2
  | .F32   => some 4
  | .F64   => some 8
  | .Ptr   => some 8   -- 64-bit pointers
  | .Func _ => some 8  -- module-local code word, decoded only with context
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
  | .Vector count elemTy =>
    if count == 0 then none else (vectorScalarByteSize elemTy).map (count * ·)
  -- Never, Tuple, Enum, Struct, Array and ty aggregates: context-dependent
  | _         => none

trustIrDenseMatch
/-- Natural alignment of a type with a `Ty.byteSize`, over exactly
    `Ty.byteSize`'s domain: the reference interpreter's `byte_align_in`
    (crates/trust-ir/src/interpret.rs) at 64-bit pointers. -/
def Ty.byteAlign : Ty → Option Nat
  | .Bool | .I8 | .U8 => some 1
  | .I16 | .U16 | .F16 => some 2
  | .I32 | .U32 | .F32 | .Char => some 4
  | .I64 | .U64 | .F64 | .Isize | .Usize => some 8
  | .I128 | .U128 => some 16
  | .Ptr | .Func _ | .Ref _ | .RefMut _ | .PtrConst _ | .PtrMut _ | .Rc _ => some 8
  | .FatPtr _ => some 8
  | .Unit => some 1
  | .Vector count elemTy =>
    if count == 0 then none else vectorScalarByteSize elemTy
  | _ => none

/-- Round `n` up to a multiple of `a` (`a > 0`); the interpreter's `align_addr`. -/
def alignUp (n a : Nat) : Nat :=
  if a == 0 then n else (n + a - 1) / a * a

/-- `isPow2` with an explicit structural fuel: halve while even, succeed at 1.
    Structural (not well-founded) recursion, and no `&&&`, so a closed instance
    reduces in the kernel — trust's bridge replays this module in Clean's
    kernel. -/
def isPow2Fuel : Nat → Nat → Bool
  | 0, _ => false
  | _ + 1, 0 => false
  | _ + 1, 1 => true
  | fuel + 1, n + 2 => (n + 2) % 2 == 0 && isPow2Fuel fuel ((n + 2) / 2)

/-- Is `a` a nonzero power of two? The interpreter's `checked_align` gate.
    The fuel `a` suffices: each step halves `a`. -/
def isPow2 (a : Nat) : Bool := isPow2Fuel a a

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
  | .ptr addr _ =>
    -- 64-bit pointer encoded as 8 bytes LE (provenance is not stored:
    -- a decoded pointer recovers it by address, `Memory.resolveDecoded`)
    some (encodeIntBytes (Int.ofNat addr) 8)
  | .float _ =>
    -- A float has no width-free byte image: the typed `encodeValueAt` owns
    -- float images. (This arm used to write eight zero bytes for ANY float,
    -- so a stored `1.5` read back as `0.0`; WS2.23 fails it closed.)
    none
  | .nullPtr =>
    -- Null pointer = address 0 encoded as 8 bytes
    some (List.replicate 8 0)
  | .array _ => none       -- Structural aggregate byte images remain separate work
  | .aggregate _ => none   -- Aggregates: element-by-element in Phase 4
  | .vector _ => none      -- Vectors stay in SSA for this first executable path
  | .frame _ _ => none       -- Binding frames cannot be stored to memory (Rust-side validation)
  -- ty supremacy aggregate values live in SSA registers, not memory.
  -- No byte encoding is defined for them; frontends must lower these
  -- through explicit aggregate/scalar stores before hitting memory.
  | .set _ => none
  | .sequence _ => none
  | .record _ => none
  | .closure _ _ => none
  | .fnDef _ _ => none  -- a code word needs the module's source-order table
  | .typedClosure _ _ _ => none
  -- A fat pointer's byte image is its two 64-bit lanes back-to-back:
  -- data address followed by canonical metadata. The static Ty determines
  -- whether the second lane is a length or a vtable pointer when decoding;
  -- encoding therefore accepts exactly one 8-byte metadata image and fails
  -- closed on malformed Value.fatPtr payloads.
  | .fatPtr data _ metadata =>
    match metadata with
    | .int 64 value =>
      let modulus := (2 : Int) ^ 64
      let unsigned := ((value % modulus) + modulus) % modulus
      some (encodeIntBytes (Int.ofNat data) 8 ++ encodeIntBytes unsigned 8)
    | .ptr metadataAddr _ =>
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
  | .uninit => none        -- Crystal lane (E3b): an unwritten lane has no initialised bytes

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
  | .I32 | .U32 | .Char =>
    if bytes.length == 4 then some (.int 32 (Int.ofNat (decodeIntBytes bytes)))
    else none
  | .I64 | .U64 | .Isize | .Usize =>
    if bytes.length == 8 then some (.int 64 (Int.ofNat (decodeIntBytes bytes)))
    else none
  | .I128 | .U128 =>
    if bytes.length == 16 then some (.int 128 (Int.ofNat (decodeIntBytes bytes)))
    else none
  -- Float images decode only through the typed `decodeValueAt` (which routes
  -- to `decodeFloatAt`); these arms used to answer `0.0` for EVERY image.
  | .F32 => none
  | .F64 => none
  | .Ptr | .Ref _ | .RefMut _ | .PtrConst _ | .PtrMut _ | .Rc _ =>
    if bytes.length == 8 then
      let addr := decodeIntBytes bytes
      if addr == 0 then some .nullPtr
      else some (.ptr addr none)
    else none
  | .FatPtr kind =>
    if bytes.length == 16 then
      let data := decodeIntBytes (bytes.take 8)
      let metadataBytes := bytes.drop 8
      match kind with
      | .Slice _ | .Str | .ContainerLen =>
        some (.fatPtr data none (.int 64 (Int.ofNat (decodeIntBytes metadataBytes))))
      | .TraitObject _ | .ContainerVtable =>
        let metadataAddr := decodeIntBytes metadataBytes
        let metadata := if metadataAddr == 0 then .nullPtr else .ptr metadataAddr none
        some (.fatPtr data none metadata)
    else none
  | .Unit =>
    -- Unit is zero-sized; decode from empty byte list
    if bytes.length == 0 then some (.aggregate [])
    else none
  | _ => none  -- Struct, Array, Func, Never, Tuple, Enum, Set, Sequence, Record, Closure: not directly decodable

/-- One admitted vector lane. Boolean vectors use the physical mask image
    `0xFF` for true; scalar boolean storage continues to use `0x01`. Integer
    widths must match, and float images keep the typed float codec's checks. -/
def encodeVectorLane (elemTy : Ty) (lane : Value) : Except SemError (List UInt8) :=
  match vectorScalarByteSize elemTy with
  | none => .error (.typeError "vector memory requires an admitted scalar lane type")
  | some laneBytes => do
    let bytes ← match elemTy, lane with
      | .Bool, .bool value => pure [if value then 255 else 0]
      | _, .int width _ =>
        if elemTy.isInteger && elemTy.bitWidth == some width then
          match encodeValue lane with
          | some bytes => pure bytes
          | none => throw (.typeError "cannot encode vector integer lane")
        else throw (.typeError "vector integer lane has the wrong type or width")
      | _, .float value => encodeFloatAt elemTy value
      | _, _ => throw (.typeError "vector lane does not inhabit its declared scalar type")
    if bytes.length != laneBytes then
      throw (.typeError "vector lane byte count does not match its declared type")
    pure bytes

/-- Encode each supplied lane once, recursing on the actual value list. -/
def encodeVectorLanes (elemTy : Ty) : List Value → Except SemError (List UInt8)
  | [] => .ok []
  | lane :: lanes => do
    let first ← encodeVectorLane elemTy lane
    let rest ← encodeVectorLanes elemTy lanes
    pure (first ++ rest)

/-- Typed, packed scalar-vector image with exact lane and byte censuses. -/
def encodeScalarVectorAt (count : Nat) (elemTy : Ty) (value : Value) :
    Except SemError (List UInt8) := do
  if count == 0 then
    throw (.unsupported .vectorShape "zero-lane vectors are not executable")
  let laneBytes ← match vectorScalarByteSize elemTy with
    | some size => pure size
    | none => throw (.typeError "vector memory requires an admitted scalar lane type")
  let lanes ← match value with
    | .vector lanes => pure lanes
    | _ => throw (.typeError "vector memory requires a vector value")
  if lanes.length != count then
    throw (.typeError "vector value lane count does not match its declared type")
  let bytes ← encodeVectorLanes elemTy lanes
  if bytes.length != count * laneBytes then
    throw (.typeError "vector image byte count does not match its declared type")
  pure bytes

/-- Decode one admitted scalar lane. Pointer lanes never reach this helper,
    so a vector cannot bypass the scalar provenance-recovery boundary. -/
def decodeVectorLane (elemTy : Ty) (bytes : List UInt8) : Except SemError Value :=
  match vectorScalarByteSize elemTy with
  | none => .error (.typeError "vector memory requires an admitted scalar lane type")
  | some laneBytes =>
    if bytes.length != laneBytes then
      .error (.typeError "vector lane image has the wrong byte count")
    else if elemTy.isFloat then do
      let value ← decodeFloatAt elemTy bytes
      pure (.float value)
    else match decodeValue elemTy bytes with
      | some value => .ok value
      | none => .error (.typeError "cannot decode vector scalar lane")

/-- Decode the declared lane count structurally; a remaining or missing byte
    is refused rather than dropped or padded. -/
def decodeVectorLanes (elemTy : Ty) (laneBytes : Nat) :
    Nat → List UInt8 → Except SemError (List Value)
  | 0, [] => .ok []
  | 0, _ => .error (.typeError "vector image has trailing bytes")
  | count + 1, bytes => do
    let first ← decodeVectorLane elemTy (bytes.take laneBytes)
    let rest ← decodeVectorLanes elemTy laneBytes count (bytes.drop laneBytes)
    pure (first :: rest)

/-- A typed vector decoder requires its complete packed byte image. -/
def decodeScalarVectorAt (count : Nat) (elemTy : Ty) (bytes : List UInt8) :
    Except SemError Value := do
  if count == 0 then
    throw (.unsupported .vectorShape "zero-lane vectors are not executable")
  let laneBytes ← match vectorScalarByteSize elemTy with
    | some size => pure size
    | none => throw (.typeError "vector memory requires an admitted scalar lane type")
  if bytes.length != count * laneBytes then
    throw (.typeError "vector image byte count does not match its declared type")
  let lanes ← decodeVectorLanes elemTy laneBytes count bytes
  pure (.vector lanes)

/-- The typed byte image of `v` stored at `ty`: the ONE encoder every memory
    write uses. A float's image is width-dependent and is owned by
    `encodeFloatAt` (which refuses what it cannot model rather than writing a
    placeholder). A vector uses its declared scalar lane type; every other
    value keeps the untyped `encodeValue` image. -/
def encodeValueAt (ty : Ty) (v : Value) : Except SemError (List UInt8) :=
  match ty, v with
  -- The empty aggregate is the model's Unit value; its typed image is empty.
  -- Width-free aggregate encoding still refuses every aggregate.
  | .Unit, .aggregate [] => .ok []
  | .Vector count elemTy, value => encodeScalarVectorAt count elemTy value
  | _, .float f => encodeFloatAt ty f
  | _, _ =>
    match encodeValue v with
    | some bs => .ok bs
    | none => .error (.typeError "cannot encode value")

/-- A fully initialized Char image must represent a Unicode scalar value.
    Invalid images are UB at the typed memory-result boundary, even if the
    result is discarded. Partial non-strict loads bypass decoding and retain
    the existing poison transport. This does not validate other SSA producers
    or recursively impose a Char invariant on aggregate payloads. -/
def decodeCharImage (bytes : List UInt8) : Except SemError Value :=
  if bytes.length == 4 then
    let scalar := decodeIntBytes bytes
    if validChar scalar then .ok (.int 32 (Int.ofNat scalar))
    else .error (.ub "memory decode: invalid Unicode scalar value")
  else .error (.typeError "Char image must contain exactly four bytes")

/-- Decode a byte image read at `ty`, WITHOUT provenance: every pointer it
    yields is `.ptr addr none`. A float type decodes through `decodeFloatAt`;
    every other type keeps the untyped `decodeValue`. Byte-level lemmas state
    themselves over this; no memory read uses it directly — they go through
    `decodeValueAt`, which recovers provenance. -/
def decodeImageAt (ty : Ty) (bytes : List UInt8) : Except SemError Value :=
  match ty with
  | .Char => decodeCharImage bytes
  | .Vector count elemTy => decodeScalarVectorAt count elemTy bytes
  | _ =>
    if ty.isFloat then
      match decodeFloatAt ty bytes with
      | .ok f => .ok (.float f)
      | .error e => .error e
    else
      match decodeValue ty bytes with
      | some v => .ok v
      | none => .error (.typeError "failed to decode bytes")

/-- Give a DECODED value (whose pointers carry no provenance) the provenance
    its addresses recover in `mem` (`Memory.resolveAddr`): a thin pointer, a
    fat pointer's data lane and its vtable-pointer metadata lane. The
    interpreter's `decode_leaf`, which resolves every pointer word it decodes
    through `resolve_pointer_kind`. -/
def Memory.resolveDecoded (mem : Memory) : Value → Value
  | .ptr a _ => mem.resolveAddr a
  | .fatPtr d _ m =>
    let m' := match m with
      | .ptr ma _ => mem.resolveAddr ma
      | other => other
    .fatPtr d (if d == 0 then none else mem.provenanceAt d) m'
  | v => v

/-- Decode a byte image read at `ty` out of `mem`: the ONE decoder every
    memory read uses (`Load`, the atomics, the `SeqMap` element cell). Every
    pointer it yields recovers its provenance by address in `mem`
    (`Memory.resolveDecoded`), so no read can skip the recovery rule. -/
def decodeValueAt (mem : Memory) (ty : Ty) (bytes : List UInt8) : Except SemError Value :=
  match decodeImageAt ty bytes with
  | .ok v => .ok (mem.resolveDecoded v)
  | .error e => .error e

trustIrDenseMatch
def Ty.byteSizeAtModel (model : ByteModel) : Ty → Option Nat
  | .Isize | .Usize | .Ptr | .Func _ | .Ref _ | .RefMut _ | .PtrConst _ | .PtrMut _ | .Rc _ =>
    some model.pointerBytes
  | .FatPtr _ => some (2 * model.pointerBytes)
  | .Char => some 4
  | ty => ty.byteSize

trustIrDenseMatch
def Ty.byteAlignAtModel (model : ByteModel) : Ty → Option Nat
  | .Isize | .Usize | .Ptr | .Func _ | .Ref _ | .RefMut _ | .PtrConst _ | .PtrMut _ | .Rc _
  | .FatPtr _ => some model.pointerBytes
  | .Char => some 4
  | ty => ty.byteAlign

def FatPtrKind.metadataTyAtModel (model : ByteModel) : FatPtrKind → Ty
  | .Slice _ | .Str | .ContainerLen => model.lengthTy
  | .TraitObject _ | .ContainerVtable => .Ptr

def metadataInhabitsAtModel (model : ByteModel) : Ty → Value → Bool
  | .U32, .int 32 _ => model == .le32
  | .U64, .int 64 _ => model == .le64
  | .Ptr, .ptr a _ => a < model.addressLimit
  | .Ptr, .nullPtr => true
  | _, _ => false

def fatPtrStoreValueValidAtModel (model : ByteModel) : Ty → Value → Bool
  | .FatPtr kind, .fatPtr data _ metadata =>
    data < model.addressLimit && metadataInhabitsAtModel model (kind.metadataTyAtModel model) metadata
  | .FatPtr _, _ => false
  | _, _ => true

/-- Address conversion is checked before encoding, so a high address cannot
    be truncated into an unrelated low address. -/
def encodePointerWord (model : ByteModel) (address : Nat) : Option (List UInt8) :=
  if address < model.addressLimit then
    some (encodeIntBytes (Int.ofNat address) model.pointerBytes)
  else none

def decodePointerWord (model : ByteModel) (bytes : List UInt8) : Option Nat :=
  if bytes.length == model.pointerBytes then some (decodeIntBytes bytes)
  else none

/-- A metadata integer has the target's width; a vtable is a checked pointer
    word. Its interpretation is decided by the fat-pointer kind at decoding. -/
def encodeMetadataWord (model : ByteModel) : Value → Option (List UInt8)
  | .int width value =>
    if width == model.pointerBits then
      let modulus := (2 : Int) ^ width
      some (encodeIntBytes (((value % modulus) + modulus) % modulus) model.pointerBytes)
    else none
  | .ptr address _ => encodePointerWord model address
  | .nullPtr => some (List.replicate model.pointerBytes 0)
  | _ => none

/-- Target-indexed image of a value. The typed boundary below additionally
    checks that a fat pointer's metadata has the canonical kind. -/
def encodeValueAtModel (model : ByteModel) : Value → Option (List UInt8)
  | .ptr address _ => encodePointerWord model address
  | .nullPtr => some (List.replicate model.pointerBytes 0)
  | .fatPtr data _ metadata => do
    let first ← encodePointerWord model data
    let second ← encodeMetadataWord model metadata
    pure (first ++ second)
  | value => encodeValue value

def decodeValueAtModel (model : ByteModel) (ty : Ty) (bytes : List UInt8) : Option Value :=
  match ty with
  | .Ptr | .Ref _ | .RefMut _ | .PtrConst _ | .PtrMut _ | .Rc _ => do
    let address ← decodePointerWord model bytes
    pure (if address == 0 then .nullPtr else .ptr address none)
  | .FatPtr kind =>
    if bytes.length == 2 * model.pointerBytes then
      let data := decodeIntBytes (bytes.take model.pointerBytes)
      let metadata := decodeIntBytes (bytes.drop model.pointerBytes)
      match kind with
      | .Slice _ | .Str | .ContainerLen =>
        some (.fatPtr data none (.int model.pointerBits (Int.ofNat metadata)))
      | .TraitObject _ | .ContainerVtable =>
        some (.fatPtr data none (if metadata == 0 then .nullPtr else .ptr metadata none))
    else none
  | .Isize | .Usize =>
    if bytes.length == model.pointerBytes then
      some (.int model.pointerBits (Int.ofNat (decodeIntBytes bytes)))
    else none
  | .Char => decodeValue .Char bytes
  | _ => decodeValue ty bytes

def encodeTypedAtModel (model : ByteModel) (ty : Ty) (value : Value) :
    Except SemError (List UInt8) :=
  if !(fatPtrStoreValueValidAtModel model ty value) then
    .error (.typeError "fat pointer does not inhabit its target metadata kind")
  else match ty, value with
    | .Unit, .aggregate [] => .ok []
    | .Vector count elemTy, value => encodeScalarVectorAt count elemTy value
    | _, .float f => encodeFloatAt ty f
    | _, _ =>
      match encodeValueAtModel model value with
      | some bytes => .ok bytes
      | none => .error (.typeError "cannot encode value at target width")

def decodeImageAtModel (model : ByteModel) (ty : Ty) (bytes : List UInt8) :
    Except SemError Value :=
  match ty with
  | .Char => decodeCharImage bytes
  | .Vector count elemTy => decodeScalarVectorAt count elemTy bytes
  | _ =>
    if ty.isFloat then
      match decodeFloatAt ty bytes with
      | .ok f => .ok (.float f)
      | .error e => .error e
    else
      match decodeValueAtModel model ty bytes with
      | some value => .ok value
      | none => .error (.typeError "failed to decode bytes at target width")

/-- The same provenance recovery rule serves both widths. -/
def decodeTypedAtModel (model : ByteModel) (mem : Memory) (ty : Ty)
    (bytes : List UInt8) : Except SemError Value := do
  let value ← decodeImageAtModel model ty bytes
  pure (mem.resolveDecoded value)

/-- Layout selectors retain the original 64-bit size and alignment queries.
    The memory encoder below additionally checks physical pointer words. -/
def Ty.byteSizeFor (model : ByteModel) (ty : Ty) : Option Nat :=
  match model with
  | .le64 => ty.byteSize
  | .le32 => ty.byteSizeAtModel .le32

def Ty.byteAlignFor (model : ByteModel) (ty : Ty) : Option Nat :=
  match model with
  | .le64 => ty.byteAlign
  | .le32 => ty.byteAlignAtModel .le32

/-- The existing canonical memory domain is independent of producer
    aggregate descriptors. This is a semantic base-case classifier, including
    the existing positive packed scalar-vector domain. -/
def Ty.hasCanonicalMemoryLayout : Ty → _root_.Bool
  | .Bool | .I8 | .I16 | .I32 | .I64 | .I128 | .U8 | .U16 | .U32 | .U64 | .U128
  | .Isize | .Usize | .Char | .F16 | .F32 | .F64 | .Ptr | .PtrConst _ | .PtrMut _
  | .Ref _ | .RefMut _ | .Rc _ | .Func _ | .FatPtr _ | .Unit => true
  | .Vector count element => if count == 0 then false else (vectorScalarByteSize element).isSome
  | _ => false

theorem Ty.hasCanonicalMemoryLayout_eq (ty : Ty) (model : ByteModel) :
    ty.hasCanonicalMemoryLayout = (ty.byteSizeFor model).isSome := by
  trustIrCompilerProof {
    cases ty <;> cases model <;> try rfl
    all_goals
      rename_i count element
      cases h : vectorScalarByteSize element <;>
        by_cases zero : count = 0 <;>
          simp [hasCanonicalMemoryLayout, byteSizeFor, byteSizeAtModel, byteSize, h, zero]
  } {
    cases ty <;> cases model <;> try rfl
    all_goals
      rename_i count element
      cases count with
      | zero => rfl
      | succ count =>
        cases h : vectorScalarByteSize element <;>
          simp only [hasCanonicalMemoryLayout, byteSizeFor, byteSizeAtModel, byteSize, h] <;> rfl
  }

def fatPtrStoreValueValidFor (model : ByteModel) (ty : Ty) (value : Value) : Bool :=
  match model with
  | .le64 => fatPtrStoreValueValid ty value
  | .le32 => fatPtrStoreValueValidAtModel .le32 ty value

/-- Encoding observes physical pointer words, including both lanes of a fat
    pointer. Far pointers may be transported in SSA but cannot be truncated
    into a different address by a store. No liveness test is made here. -/
def checkPointerImageWords (model : ByteModel) (value : Value) : Except SemError Unit :=
  let check (address : Nat) : Except SemError Unit :=
    if address < model.addressLimit then .ok ()
    else .error (.ub "Store: pointer address exceeds the target width")
  match value with
  | .ptr address _ => check address
  | .fatPtr data _ metadata => do
    check data
    match metadata with
    | .ptr address _ => check address
    | _ => pure ()
  | _ => pure ()

def encodeMemoryAt (model : ByteModel) (ty : Ty) (value : Value) : Except SemError (List UInt8) :=
  (checkPointerImageWords model value).bind fun _ =>
    match model with
    | .le64 => encodeValueAt ty value
    | .le32 => encodeTypedAtModel .le32 ty value

def decodeMemoryAt (model : ByteModel) (mem : Memory) (ty : Ty) (bytes : List UInt8) :
    Except SemError Value :=
  match model with
  | .le64 => decodeValueAt mem ty bytes
  | .le32 => decodeTypedAtModel .le32 mem ty bytes

/-- Original module function order, including declarations and undecodable
    bodies. Absence means that no module code-address table was supplied. -/
abbrev FunctionAddressOrder := Option (List FuncId)

/-- First source position of an identity; numeric FuncIds are not addresses. -/
def functionAddressIndex (target : FuncId) : List FuncId → Option Nat
  | [] => none
  | head :: tail =>
    if head = target then some 0
    else (functionAddressIndex target tail).map Nat.succ

def checkedFunctionAddress (model : ByteModel) (index : Nat) : Except SemError Nat :=
  if index + 1 < model.addressLimit then .ok (index + 1)
  else .error (.typeError "Store: function address exceeds target pointer width")

def functionAddressOf (model : ByteModel) (order : FunctionAddressOrder)
    (target : FuncId) : Except SemError Nat := do
  let ids ← match order with
    | some ids => pure ids
    | none => .error (.unsupported .layout "function pointer Store requires a source function table")
  match functionAddressIndex target ids with
  | some index => checkedFunctionAddress model index
  | none => .error (.typeError "Store: undefined function pointer")

def functionTargetAt (model : ByteModel) (order : FunctionAddressOrder)
    (address : Nat) : Except SemError FuncId := do
  if address = 0 then
    .error (.typeError "Load: null word has no function identity")
  else if address < model.addressLimit then
    let ids ← match order with
      | some ids => pure ids
      | none => .error (.unsupported .layout "function pointer Load requires a source function table")
    match trustIrListGet? ids (address - 1) with
    | some target => pure target
    | none => .error (.typeError "Load: unregistered function pointer address")
  else .error (.typeError "Load: function address exceeds target pointer width")

/-- The contextual Func leaf stores one checked symbolic code word. Pure
    constants and the width-free encoder do not mint such an address. -/
def encodeMemoryWithFunctions (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (value : Value) : Except SemError (List UInt8) := do
  match ty with
  | .Func signature =>
    match value with
    | .fnDef held target =>
      if held = signature then
        let address ← functionAddressOf model order target
        pure (encodeIntBytes (Int.ofNat address) model.pointerBytes)
      else .error (.typeError "Store: function pointer signature does not match type")
    | .nullPtr => pure (List.replicate model.pointerBytes 0)
    | _ => .error (.typeError "Store: expected a function pointer value")
  | _ => encodeMemoryAt model ty value

/-- The load type supplies the function signature; the bytes hold only the
    source-table address. Unknown words never become dangling data pointers. -/
def decodeMemoryWithFunctions (model : ByteModel) (order : FunctionAddressOrder)
    (mem : Memory) (ty : Ty) (bytes : List UInt8) : Except SemError Value := do
  match ty with
  | .Func signature =>
    if bytes.length = model.pointerBytes then
      let address := decodeIntBytes bytes
      if address = 0 then pure .nullPtr
      else
        let target ← functionTargetAt model order address
        pure (.fnDef signature target)
    else .error (.typeError "Load: function pointer image has the wrong byte count")
  | _ => decodeMemoryAt model mem ty bytes

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
    interpreter's `MemoryState::read_image` (crates/trust-ir/src/interpret.rs;
    it was `Memory::read_maybe_uninit` at commit 530fdd5, before v50 made
    allocations sparse byte images). -/
def Memory.readBytesMaybeUninit (mem : Memory) (addr : Addr) (n : Nat)
    : List (Option UInt8) :=
  let rec go (remaining : Nat) (currentAddr : Addr) : List (Option UInt8) :=
    match remaining with
    | 0 => []
    | k + 1 => mem.bytes currentAddr :: go k (currentAddr + 1)
  go n addr

/-- Write one authoritative image without enumerating its logical bytes.
    Zero-length writes are exact no-ops, including unwritten records. -/
def Memory.writeImage (mem : Memory) (addr : Addr) (image : ByteImage) : Memory :=
  { mem with
    storage := if image.size = 0 then mem.storage else .write mem.storage addr image
    unwritten := if image.size = 0 then mem.unwritten
      else (mem.forgetUnwritten addr image.size).unwritten }

/-- Finite scalar/transport buffers use the same image store. An absent byte
    restores absence at its destination; it never means "leave unchanged". -/
def Memory.writeBytesMaybeUninit (mem : Memory) (addr : Addr)
    (image : List (Option UInt8)) : Memory :=
  mem.writeImage addr (ByteImage.ofList image)

/-- Store an actual finite initialized buffer through the authoritative image. -/
def Memory.writeBytes (mem : Memory) (addr : Addr) (data : List UInt8) : Memory :=
  mem.writeImage addr (ByteImage.ofList (data.map some))

@[simp] theorem Memory.readImage_size (mem : Memory) (addr count : Nat) :
    (mem.readImage addr count).size = count := ByteStore.size_snapshot mem.storage addr count

theorem Memory.readImage_get (mem : Memory) (addr count index : Nat) (inside : index < count) :
    (mem.readImage addr count).get index = mem.bytes (addr + index) :=
  ByteStore.get_snapshot mem.storage addr count index inside

theorem Memory.bytes_writeImage_inside (mem : Memory) (addr index : Nat) (image : ByteImage)
    (inside : index < image.size) :
    (mem.writeImage addr image).bytes (addr + index) = image.get index := by
  have nonempty : image.size ≠ 0 := by omega
  unfold Memory.writeImage
  rw [if_neg nonempty]
  change (ByteStore.write mem.storage addr image).get (addr + index) = image.get index
  rw [ByteStore.get_write_inside mem.storage addr (addr + index) image (by omega) (by omega)]
  simp only [Nat.add_sub_cancel_left]

theorem Memory.bytes_writeImage_outside (mem : Memory) (addr address : Nat) (image : ByteImage)
    (outside : address < addr ∨ addr + image.size ≤ address) :
    (mem.writeImage addr image).bytes address = mem.bytes address := by
  by_cases empty : image.size = 0
  · unfold Memory.writeImage
    rw [if_pos empty]
    rfl
  · unfold Memory.writeImage
    rw [if_neg empty]
    exact ByteStore.get_write_outside mem.storage addr address image outside

theorem Memory.bytes_writeBytes_inside (mem : Memory) (addr index : Nat) (data : List UInt8)
    (inside : index < data.length) :
    (mem.writeBytes addr data).bytes (addr + index) = some (data.get ⟨index, inside⟩) := by
  unfold Memory.writeBytes
  rw [Memory.bytes_writeImage_inside mem addr index _ (by simpa using inside)]
  rw [ByteImage.get_ofList]
  trustIrCompilerProof {
    first
    | rw [List.get?_map, List.get?_eq_get inside]
      rfl
    | simp [getElem?_def, inside]
  } {
    rw [CompilerCompat.listGetConstructive_map, CompilerCompat.listGet?_eq_get inside]
    rfl
  }

theorem Memory.bytes_writeBytes_outside (mem : Memory) (addr address : Nat) (data : List UInt8)
    (outside : address < addr ∨ addr + data.length ≤ address) :
    (mem.writeBytes addr data).bytes address = mem.bytes address := by
  unfold Memory.writeBytes
  apply Memory.bytes_writeImage_outside
  simpa using outside

/-- The snapshot is captured before the destination write, including overlap
    and absent source bytes. This theorem covers every offset, not samples. -/
theorem Memory.bytes_copyImage (mem : Memory) (dst src count index : Nat) (inside : index < count) :
    (mem.writeImage dst (mem.readImage src count)).bytes (dst + index) = mem.bytes (src + index) := by
  rw [Memory.bytes_writeImage_inside mem dst index _ (by simpa using inside)]
  exact Memory.readImage_get mem src count index inside

theorem Memory.bytes_fillImage (mem : Memory) (addr count index : Nat) (byte : Option UInt8)
    (inside : index < count) :
    (mem.writeImage addr (ByteImage.fill count byte)).bytes (addr + index) = byte := by
  rw [Memory.bytes_writeImage_inside mem addr index (ByteImage.fill count byte) inside,
    ByteImage.get_fill, if_pos inside]

@[simp] theorem Memory.writeImage_allocations (mem : Memory) (addr : Nat) (image : ByteImage) :
    (mem.writeImage addr image).allocations = mem.allocations := rfl

@[simp] theorem Memory.writeImage_nextAddr (mem : Memory) (addr : Nat) (image : ByteImage) :
    (mem.writeImage addr image).nextAddr = mem.nextAddr := rfl

@[simp] theorem Memory.writeImage_nextAllocId (mem : Memory) (addr : Nat) (image : ByteImage) :
    (mem.writeImage addr image).nextAllocId = mem.nextAllocId := rfl

/-- The defined fill of a heap allocation's slack tail: `0xFF`, hashbrown's
    EMPTY control byte (the interpreter's `SLACK_FILL`). -/
def slackFill : UInt8 := 0xFF

/-- The readable tail a `HeapAlloc` gets past the bytes it requested (the
    interpreter's `HEAP_USABLE_SLACK`); `Alloca`, globals and the `SeqMap`
    element cell get none. -/
def heapUsableSlack : Nat := 16

/-- The floor of a global's placement alignment (the interpreter's
    `GLOBAL_SECTION_ALIGN`, in `global_pointer`). -/
def globalSectionAlign : Nat := 16

/-- Create a new allocation in memory: the REFERENCE PLACEMENT the
    interpreter's `MemoryState::alloc_with_slack` makes. The base is the next
    free address rounded up to `align`; the allocation's footprint (`size`)
    is the `size` requested plus `slack` defined tail bytes (`slackFill`),
    and `requested` keeps the requested size; the next free address advances
    by the footprint, or by one byte for a zero-size allocation, so no two
    allocations share a base. Placement is a property of the two reference
    models, held equal by `address_layout_agrees_across_engines`, not a
    format rule (SPEC "A pointer operand names the allocation it was derived
    from"). Returns the base address and the updated memory. -/
def Memory.alloc (mem : Memory) (size align slack : Nat) (origin : AllocationOrigin)
    : Addr × Memory :=
  let allocId := AllocId.mk mem.nextAllocId
  let baseAddr := alignUp mem.nextAddr align
  let footprint := size + slack
  let allocation : Allocation :=
    { id        := allocId
    , base      := baseAddr
    , size      := footprint
    , alive     := true
    , origin    := origin
    , requested := size }
  let mem' : Memory :=
    { mem with
      allocations := allocation :: mem.allocations
      nextAddr    := baseAddr + max footprint 1
      nextAllocId := mem.nextAllocId + 1 }
  -- The heap slack tail is DEFINED (0xFF, hashbrown's EMPTY), as in the
  -- interpreter's `alloc_with_slack`.
  (baseAddr, if slack == 0 then mem' else mem'.writeImage (baseAddr + size) (ByteImage.fill slack (some slackFill)))

/-- The pointer a dereferencing operand carries: the interpreter's
    `expect_pointer`. A null pointer and a pointer with no provenance are UB
    (there is no allocation to touch); a non-pointer is a type error. Checked
    BEFORE the access type's byte size, so a null or dangling dereference is
    UB at an unmodelled type too, never demoted to `unsupported`. -/
def Sem.expectPointer (op : String) (ptrVal : Value) : Sem (Addr × AllocId) :=
  match ptrVal with
  | .nullPtr => Sem.throwUB s!"{op}: null pointer dereference"
  | .ptr addr none =>
    if addr == 0 then Sem.throwUB s!"{op}: null pointer dereference"
    else Sem.throwUB s!"{op}: pointer value {addr} has no allocation provenance"
  | .ptr addr (some id) => pure (addr, id)
  | _ => Sem.throwTypeError s!"{op}: operand is not a pointer"

/-- Enforce the new target's address domain; the legacy 64-bit path is unchanged. -/
def Sem.targetAddress (model : ByteModel) (op : String) (address : Nat) : Sem Nat :=
  match model with
  | .le64 => pure address
  | .le32 =>
    if address < model.addressLimit then pure address
    else Sem.throwUB (trustIrStringBuild s!"{op}: address is outside the target address space")

def Sem.checkTargetRange (model : ByteModel) (op : String) (address size : Nat) : Sem Unit :=
  match model with
  | .le64 => pure ()
  | .le32 =>
    if address < model.addressLimit && address + size ≤ model.addressLimit then pure ()
    else Sem.throwUB s!"{op}: access is outside the target address space"

/-- The interpreter's `checked_access`: the allocation `id` the pointer was
    derived from is known and LIVE, the address is aligned to `align`, and the
    `size`-byte access lies inside that allocation's footprint. Never a
    neighbour: the allocation is named by provenance, not found by address. -/
def Sem.checkedAccess (op : String) (addr : Addr) (id : AllocId) (size align : Nat) (model : ByteModel := .le64) :
    Sem Addr := do
  Sem.checkTargetRange model op addr size
  let s ← Sem.getState
  match s.memory.lookup id with
  | none => Sem.throwUB s!"{op}: unknown allocation"
  | some a =>
    if !a.alive then Sem.throwUB s!"{op}: use after dealloc"
    else if align != 0 && addr % align != 0 then
      Sem.throwUB s!"{op}: pointer address {addr} is not aligned to {align}"
    else if addr < a.base || addr - a.base + size > a.size then
      Sem.throwUB s!"{op}: access is out of bounds"
    else pure addr

/-- The allocation a dereferencing operand names and its address:
    `Sem.expectPointer` then `Sem.checkedAccess`. -/
def Sem.accessAddr (op : String) (ptrVal : Value) (size align : Nat) (model : ByteModel := .le64) : Sem Addr := do
  let (addr, id) ← Sem.expectPointer op ptrVal
  Sem.checkedAccess op addr id size align model

/-- One alignment table, two rules (`Sem.placementAlign`, `Sem.accessAlign`):
    the declared alignment, else the type's natural one (`Ty.byteAlign`), and
    a type error unless it is a nonzero power of two — the interpreter's
    `checked_align(align.unwrap_or(natural))`. -/
def Sem.declaredOrNaturalAlign (op : String) (ty : Ty) (align : Option Nat) (model : ByteModel := .le64) : Sem Nat :=
  let a := align.getD ((ty.byteAlignFor model).getD 1)
  if isPow2 a then pure a
  else Sem.throwTypeError s!"{op}: alignment {a} must be a non-zero power of two"

/-- The alignment an `Alloca` / `HeapAlloc` PLACES its allocation at
    (`eval_alloca`). Kept a separate name from `Sem.accessAlign` so a change to
    one rule is a change to one rule. -/
def Sem.placementAlign (op : String) (ty : Ty) (align : Option Nat) (model : ByteModel := .le64) : Sem Nat :=
  Sem.declaredOrNaturalAlign op ty align model

/-- The alignment a `Load` / `Store` / atomic access CHECKS its address
    against (`eval_load` / `eval_store` before `checked_access`): natural
    alignment when none is declared. -/
def Sem.accessAlign (op : String) (ty : Ty) (align : Option Nat) (model : ByteModel := .le64) : Sem Nat :=
  Sem.declaredOrNaturalAlign op ty align model

/-- Source layout and integer interpretation are independent inputs. The
    contextual reader supplies actual declarations; scalar helpers cannot
    infer a dynamic operand's signedness from its raw carrier. -/
structure MemoryTypeLayout where
  size : Nat
  alignment : Nat

abbrev MemoryLayoutQuery := Ty → Except SemError MemoryTypeLayout

trustIrDenseMatch
def scalarMemoryLayout (model : ByteModel) (ty : Ty) : Except SemError MemoryTypeLayout :=
  match ty.byteSizeFor model, ty.byteAlignFor model with
  | some size, some alignment => .ok ⟨size, alignment⟩
  | _, _ => .error (.unsupported .layout "type has no complete scalar/vector byte layout")

def Sem.fromMemoryExcept {α : Type} (result : Except SemError α) : Sem α :=
  match result with
  | .ok value => pure value
  | .error error => throw error

def checkedMemoryAlign (op : String) (natural : Nat) (declared : Option Nat) :
    Except SemError Nat :=
  let alignment := declared.getD natural
  if alignment ≤ word64Max && isPow2 alignment then .ok alignment
  else .error (.typeError (trustIrStringBuild s!"{op}: alignment must be a nonzero u64 power of two"))

/-- Match alloc_with_slack's order: footprint, aligned base, allocation-id
    increment, next-address increment, then the target's address domain. The
    u64 next-address counter must fit even on a 64-bit target. -/
def checkWordAllocation (model : ByteModel) (memory : Memory) (size alignment slack : Nat) :
    Except SemError Unit := do
  let footprint := size + slack
  if footprint > word64Max then throw (.outOfMemory "allocation footprint exceeds u64")
  let base := alignUp memory.nextAddr alignment
  if base > word64Max then throw (.outOfMemory "aligned allocation base exceeds u64")
  if memory.nextAllocId ≥ word64Max then throw (.ub "allocation identifier increment overflows u64")
  let next := base + max footprint 1
  if next > word64Max then throw (.outOfMemory "allocation next-address increment exceeds u64")
  if next - 1 ≥ model.addressLimit then
    throw (.outOfMemory "allocation exceeds the target address space")

/-- Every source of allocation capacity uses the same word and target
    checks, including contextual global materialization. -/
def Sem.checkTargetAllocation (model : ByteModel) (memory : Memory)
    (size alignment slack : Nat) : Sem Unit :=
  Sem.fromMemoryExcept (checkWordAllocation model memory size alignment slack)

def semAllocateUsing (layoutOf : MemoryLayoutQuery) (readInteger : IntegerOperandReader)
    (ty : Ty) (countId : Option ValueId) (align : Option Nat)
    (origin : AllocationOrigin) (refCounted : Bool) (slack : Nat) (model : ByteModel) :
    Sem ValueId := do
  -- The Rust dispatcher retrieves the operand before eval_alloca queries layout.
  let heldCount ← match countId with
    | none => pure none
    | some id => pure (some (id, ← Sem.lookupValue id))
  let layout ← Sem.fromMemoryExcept (layoutOf ty)
  let count ← match heldCount with
    | none => pure 1
    | some (id, value) => do
      let integer ← Sem.fromMemoryExcept (readInteger id value)
      Sem.fromMemoryExcept (checkedWord64Operand "Alloca" true integer)
  let size ← Sem.fromMemoryExcept (checkedWord64Mul "Alloca" layout.size count)
  let alignment ← Sem.fromMemoryExcept (checkedMemoryAlign "Alloca" layout.alignment align)
  let before ← Sem.getState
  Sem.fromMemoryExcept (checkWordAllocation model before.memory size alignment slack)
  let id := AllocId.mk before.memory.nextAllocId
  let (address, memory) := before.memory.alloc size alignment slack origin
  if refCounted then
    Sem.setState { before with
      memory := memory
      permissions := before.permissions.set id .arcRef
      refCounts := fun key => if key == id then some 1 else before.refCounts key }
  else
    Sem.setState { before with memory := memory, permissions := before.permissions.set id .owned }
  Sem.bindFresh (.ptr address (some id))

-- =================================================================
-- Alloca semantics
-- =================================================================

/-- Evaluate an Alloca instruction.
    Allocates stack space for count elements of type ty.
    Returns a pointer to the allocated memory.

    The allocator checks u64 arithmetic and the complete target address domain
    before allocation. Dynamic counts require their original declarations.
    The allocation is marked with AllocationOrigin.rustStack.

    Mirrors Rust Inst::Alloca -/
def semAllocaUsing (layoutOf : MemoryLayoutQuery) (readInteger : IntegerOperandReader)
    (ty : Ty) (countId : Option ValueId) (align : Option Nat := none)
    (model : ByteModel := .le64) : Sem ValueId :=
  semAllocateUsing layoutOf readInteger ty countId align .rustStack false 0 model

def semAlloca (ty : Ty) (countId : Option ValueId) (align : Option Nat := none)
    (model : ByteModel := .le64) : Sem ValueId :=
  semAllocaUsing (scalarMemoryLayout model) unknownIntegerOperand ty countId align model

/-- Map the IR-level `AllocOrigin` to the memory model's `AllocationOrigin`.
    `CleanHeap` (Clean's Perceus RC cells) maps to `cleanHeap`, whose refcount
    discipline is identical to `swiftHeap` — no origin-sensitive rule
    distinguishes them; the tag records which runtime owns the cell. -/
def AllocOrigin.toAllocationOrigin : AllocOrigin → AllocationOrigin
  | .RustHeap  => .rustHeap
  | .SwiftHeap => .swiftHeap
  | .CMalloc   => .cMalloc
  | .CleanHeap => .cleanHeap

/-- Is this heap origin a reference-counted one (`SwiftHeap` / `CleanHeap`)?
    A cell of an RC heap is what the RC runtime hands out: one owner, ARC
    discipline. `RustHeap` / `CMalloc` cells have no count. -/
def AllocOrigin.isRefCounted : AllocOrigin → Bool
  | .SwiftHeap => true
  | .CleanHeap => true
  | .RustHeap  => false
  | .CMalloc   => false

/-- Evaluate a HeapAlloc instruction. Like `semAlloca`, but the allocation is
    tagged with the heap `origin` (so `AllocationOrigin.rustHeap`/`.swiftHeap`/
    `.cleanHeap`/`.cMalloc` finally become reachable in the dynamic semantics).
    A `RustHeap` / `CMalloc` cell is `owned`; an RC-heap cell (`SwiftHeap` /
    `CleanHeap`, `AllocOrigin.isRefCounted`) is the fresh cell the RC runtime
    leaves — `arcRef` permission, refcount 1 (one owner) — so the ARC trio
    (`Retain` / `Release` / `IsUnique`) executes on it exactly as the reference
    interpreter executes it (WS2.19: until then every origin was `owned`, so
    `HeapAlloc CleanHeap` + `Retain` was UB here and `Ok` there — the first
    divergence the W5b oracle surfaced, on the `inst_borrow_arc` fixture's
    `clean_rc_lifecycle`). A non-RC cell keeps refusing the trio. -/
def semHeapAllocUsing (layoutOf : MemoryLayoutQuery) (readInteger : IntegerOperandReader)
    (ty : Ty) (countId : Option ValueId) (origin : AllocOrigin)
    (align : Option Nat := none) (model : ByteModel := .le64) : Sem ValueId :=
  semAllocateUsing layoutOf readInteger ty countId align origin.toAllocationOrigin
    origin.isRefCounted heapUsableSlack model

def semHeapAlloc (ty : Ty) (countId : Option ValueId) (origin : AllocOrigin)
    (align : Option Nat := none) (model : ByteModel := .le64) : Sem ValueId :=
  semHeapAllocUsing (scalarMemoryLayout model) unknownIntegerOperand ty countId origin align model

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
def semGlobalAddr (global : GlobalId) (model : ByteModel := .le64) : Sem ValueId := do
  let s ← Sem.getState
  match s.lookupGlobal global with
  | some (addr, allocId) => do
    let addr ← Sem.targetAddress model "GlobalAddr" addr
    Sem.bindFresh (.ptr addr (some allocId))
  | none =>
    Sem.checkTargetAllocation model s.memory 1 globalSectionAlign 0
    let (baseAddr, mem') := s.memory.alloc 1 globalSectionAlign 0 .rustHeap
    let allocId := AllocId.mk s.memory.nextAllocId
    let perms' := s.permissions.set allocId .owned
    Sem.setState { s with
      memory := mem'
      permissions := perms'
      globals := (global, baseAddr, allocId) :: s.globals }
    Sem.bindFresh (.ptr baseAddr (some allocId))

-- =================================================================
-- Load semantics
-- =================================================================

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

def isPartialLoadTyFor (model : ByteModel) (ty : Ty) : Bool :=
  match model with
  | .le64 => isPartialLoadTy ty
  | .le32 => match ty with
    | .Isize | .Usize | .Char => true
    | _ => isPartialLoadTy ty

/-- Evaluate a Load instruction.
    Reads ty.byteSize bytes from memory at the pointer address and
    decodes them into a typed value.

    Safety checks (`Sem.accessAddr`, the interpreter's `expect_pointer` +
    `checked_access`): the pointer is not null and carries provenance; the
    allocation it was derived from is live; the address is aligned
    (`Sem.accessAlign`); the access lies inside that allocation's footprint.

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

    Alignment (`align`): the declared alignment, else the type's NATURAL one
    (`Sem.accessAlign`), as the interpreter's `eval_load` passes
    `align.unwrap_or(natural)` to `checked_access`; an under-aligned address
    is UB.

    A loaded pointer recovers its provenance by address (`decodeValueAt`).

    Mirrors Rust Inst::Load (`eval_load`'s `strict` flag, commit 530fdd5;
    `align` gate, commit dd27b78). -/
def semLoadValueUsing (decode : Memory → List UInt8 → Except SemError Value)
    (ty : Ty) (ptrVal : Value) (strict : Bool := false)
    (align : Option Nat := none) (model : ByteModel := .le64) : Sem Value := do
  Sem.rejectPartial ptrVal "Load"
  let (ptrAddr, ptrAlloc) ← Sem.expectPointer "Load" ptrVal
  -- Get byte size
  let byteSize ← match (ty.byteSizeFor model) with
    | some s => pure s
    | none   => Sem.throwUnsupported .layout "Load: type has no byte size"
  let alignment ← Sem.accessAlign "Load" ty align model
  let addr ← Sem.checkedAccess "Load" ptrAddr ptrAlloc byteSize alignment model
  let s ← Sem.getState
  -- Read bytes. A fully-initialized range decodes as before. When some byte is
  -- uninitialized, a non-strict SCALAR load transports the partial byte image
  -- as poison (`.partial`); a strict load — or a non-scalar decode type — keeps
  -- the all-or-UB discipline.
  match s.memory.readBytes addr byteSize with
  | some bytes =>
    match decode s.memory bytes with
    | .ok v    => pure v
    | .error e => throw e
  | none =>
    if !strict && isPartialLoadTyFor model ty then
      pure (.partial (s.memory.readBytesMaybeUninit addr byteSize))
    else
      Sem.throwUB "Load: reading uninitialized memory"

/-- The instruction wrapper publishes exactly its final loaded value.
    Internal users can call the held-value core without private SSA aliases. -/
def semLoadUsing (decode : Memory → List UInt8 → Except SemError Value)
    (ty : Ty) (ptrId : ValueId) (strict : Bool := false)
    (align : Option Nat := none) (model : ByteModel := .le64) : Sem ValueId := do
  let pointer ← Sem.lookupValue ptrId
  let value ← semLoadValueUsing decode ty pointer strict align model
  Sem.bindFresh value

/-- Bare memory keeps its existing context-free codec. -/
def semLoad (ty : Ty) (ptrId : ValueId) (strict : Bool := false)
    (align : Option Nat := none) (model : ByteModel := .le64) : Sem ValueId :=
  semLoadUsing (fun mem bytes => decodeMemoryAt model mem ty bytes) ty ptrId strict align model

-- =================================================================
-- Store semantics
-- =================================================================

/-- Evaluate a Store instruction.
    Encodes a typed value into bytes and writes them to memory at the
    pointer address.

    Safety checks: `Sem.accessAddr`, as for `semLoad`; the value can be
    encoded to bytes.

    Initialization discipline (`strict`): a NON-strict store of a `.partial`
    (poison) value writes its byte IMAGE verbatim — uninitialized bytes stay
    uninitialized at the destination — the store half of copy-propagates-poison;
    a NON-strict store of an `.undef` (poison, roadmap WS2.10) writes `byteSize`
    uninitialized bytes. A STRICT store (`strict = true`, VOLATILE plain stores;
    atomic stores keep their own encoder-based path in `Atomic.lean`) rejects
    either poison value as UB. Every non-poison value stores exactly as before.

    Alignment (`align`): as for `semLoad`, the declared alignment, else the
    type's natural one (`Sem.accessAlign`).

    Mirrors Rust Inst::Store (`eval_store`'s `strict` flag, commit 530fdd5;
    `align` gate, commit dd27b78). -/
def semStoreValueUsing (layoutOf : MemoryLayoutQuery)
    (encode : Value → Except SemError (List UInt8))
    (ty : Ty) (ptrVal val : Value) (strict : Bool := false)
    (align : Option Nat := none) (model : ByteModel := .le64) : Sem Unit := do
  Sem.rejectPartial ptrVal "Store"
  let (ptrAddr, ptrAlloc) ← Sem.expectPointer "Store" ptrVal
  let layout ← Sem.fromMemoryExcept (layoutOf ty)
  let byteSize := layout.size
  let alignment ← Sem.fromMemoryExcept (checkedMemoryAlign "Store" layout.alignment align)
  let addr ← Sem.checkedAccess "Store" ptrAddr ptrAlloc byteSize alignment model
  let s ← Sem.getState
  if val.isPoison then
    -- Copy-propagates-poison transport: a partial byte image moves to memory
    -- verbatim, and an `Undef` writes `byteSize` UNINITIALIZED bytes (roadmap
    -- WS2.10), so a later plain reload observes the same poison (non-strict
    -- stores only). A strict (volatile/atomic) store of a poison value is UB.
    match val with
    | .partial image =>
      if strict then
        Sem.throwUB "Store: strict (atomic/volatile) store of a partially-initialized value"
      else if image.length != byteSize then
        Sem.throwTypeError "Store: partial image size does not match type size"
      else
        Sem.modifyState fun st =>
          { st with memory := st.memory.writeBytesMaybeUninit addr image }
    | .undef _ =>
      if strict then
        Sem.throwUB "Store: strict (atomic/volatile) store of an undef (poison) value"
      else
        Sem.modifyState fun st =>
          { st with memory := st.memory.writeBytesMaybeUninit addr (List.replicate byteSize none) }
    | _ => Sem.throwTypeError "Store: cannot encode value"
  else
    -- Encode value
    if !(fatPtrStoreValueValidFor model ty val) then
      Sem.throwTypeError "Store: fat-pointer value does not inhabit the kind's canonical lanes"
    let encoded ← match encode val with
      | .ok bs   => pure bs
      | .error e => throw e
    -- Verify encoded size matches type
    if encoded.length != byteSize then
      Sem.throwTypeError "Store: encoded size does not match type size"
    -- Write bytes
    let mem' := s.memory.writeBytes addr encoded
    Sem.modifyState fun st => { st with memory := mem' }

/-- Publish no SSA temporaries: values are already held by the dispatcher. -/
def semStoreUsing (encode : Value → Except SemError (List UInt8))
    (ty : Ty) (ptrId valueId : ValueId) (strict : Bool := false)
    (align : Option Nat := none) (model : ByteModel := .le64)
    (layoutOf : MemoryLayoutQuery := scalarMemoryLayout model) : Sem Unit := do
  let pointer ← Sem.lookupValue ptrId
  let value ← Sem.lookupValue valueId
  semStoreValueUsing layoutOf encode ty pointer value strict align model

/-- Bare memory keeps its existing context-free codec. -/
def semStore (ty : Ty) (ptrId valueId : ValueId) (strict : Bool := false)
    (align : Option Nat := none) (model : ByteModel := .le64) : Sem Unit :=
  semStoreUsing (encodeMemoryAt model ty) ty ptrId valueId strict align model

-- =================================================================
-- GEP (GetElementPtr) semantics
-- =================================================================

/-- Compute the byte offset for a GEP index given a pointee type.
    For arrays: offset = index * element_byte_size
    For structs: offset = field offset (requires struct metadata)

    In Phase 2 we handle the simple case: all indices multiply by
    the pointee type byte size. Struct field offsets are Phase 4. -/
def gepByteOffset (pointeeTy : Ty) (index : Int) (model : ByteModel := .le64) :
    Except SemError Nat := do
  let layout ← scalarMemoryLayout model pointeeTy
  let magnitude ← checkedWord64Operand "GEP" false index
  checkedWord64Mul "GEP" magnitude layout.size

/-- Shared pointer arithmetic after all integer conversions. A real pointer
    checks its allocation-relative offset; a dangling pointer checks its
    absolute address. Both use u64 arithmetic before the target-width test. -/
def semGEPAddress (base : Value) (delta : Nat) (model : ByteModel) : Sem Value := do
  Sem.rejectPartial base "GEP"
  match base with
  | .nullPtr => Sem.throwUB "GEP: null base pointer"
  | .ptr address none =>
    let result ← Sem.fromMemoryExcept (checkedWord64Add "GEP" address delta)
    if result ≥ model.addressLimit then Sem.throwUB "GEP: address is outside target space"
    pure (.ptr result none)
  | .ptr address (some id) =>
    let state ← Sem.getState
    let allocation ← match state.memory.lookup id with
      | some allocation => pure allocation
      | none => Sem.throwUnsupported .layout "GEP: provenance origin is absent from the memory model"
    if address < allocation.base then Sem.throwUB "GEP: negative allocation offset"
    let _ ← Sem.fromMemoryExcept (checkedWord64Add "GEP" (address - allocation.base) delta)
    let result := address + delta
    if model == .le32 && result ≥ model.addressLimit then
      Sem.throwUB "GEP: address is outside target space"
    pure (.ptr result (some id))
  | _ => Sem.throwTypeError "GEP: base is not a pointer"

/-- Layout and source-declared integer arithmetic form a pure checked plan.
    No state effect is introduced for an index or an instruction immediate. -/
def gepOffsetUsing {key : Type} (layoutOf : MemoryLayoutQuery)
    (reader : key → Value → Except SemError Int) (ty : Ty)
    (indices : List (key × Value)) : Except SemError Nat := do
  let layout ← layoutOf ty
  forIn indices (0 : Nat) fun input delta => do
    let integer ← reader input.1 input.2
    let magnitude ← checkedWord64Operand "GEP" false integer
    let offset ← checkedWord64Mul "GEP" layout.size magnitude
    let result ← checkedWord64Add "GEP" delta offset
    pure (.yield result)

/-- Shared GEP on held values lifts the checked plan once, then performs
    provenance-aware address arithmetic. It publishes no synthetic SSA ids. -/
def semGEPValuesUsing {key : Type} (layoutOf : MemoryLayoutQuery)
    (readInteger : key → Value → Except SemError Int) (pointeeTy : Ty)
    (base : Value) (indices : List (key × Value)) (model : ByteModel := .le64) : Sem Value := do
  let delta ← Sem.fromMemoryExcept (gepOffsetUsing layoutOf readInteger pointeeTy indices)
  semGEPAddress base delta model

def semGEPUsing (layoutOf : MemoryLayoutQuery) (readInteger : IntegerOperandReader)
    (pointeeTy : Ty) (baseId : ValueId) (indexIds : List ValueId)
    (model : ByteModel := .le64) : Sem ValueId := do
  let base ← Sem.lookupValue baseId
  let inputs ← indexIds.mapM (fun id => do pure (id, ← Sem.lookupValue id))
  let result ← semGEPValuesUsing layoutOf readInteger pointeeTy base inputs model
  Sem.bindFresh result

def semGEP (pointeeTy : Ty) (baseId : ValueId) (indexIds : List ValueId)
    (model : ByteModel := .le64) : Sem ValueId :=
  semGEPUsing (scalarMemoryLayout model) unknownIntegerOperand pointeeTy baseId indexIds model

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
  | .U64, .Slice _         => true
  | .U64, .Str             => true
  | .U64, .ContainerLen    => true
  | .Ptr, .TraitObject _   => true
  | .Ptr, .ContainerVtable => true
  | _,    _                => false

def metadataTyMatchesFor (model : ByteModel) (ty : Ty) (kind : FatPtrKind) : Bool :=
  match model with
  | .le64 => metadataTyMatches ty kind
  -- Like the original rule, use structural matches. Recursive Ty's derived
  -- BEq does not kernel-reduce; it cannot be a new proof-model authority.
  | .le32 => match ty, kind with
    | .U32, .Slice _ | .U32, .Str | .U32, .ContainerLen => true
    | .Ptr, .TraitObject _ | .Ptr, .ContainerVtable => true
    | _, _ => false

def metadataInhabitsFor (model : ByteModel) (kind : FatPtrKind) (value : Value) : Bool :=
  match model with
  | .le64 => metadataInhabits kind.metadataTy value
  | .le32 => metadataInhabitsAtModel .le32 (kind.metadataTyAtModel .le32) value

/-- Canonical thin-pointer value for a stored fat-pointer data address. -/
def fatPtrDataLane : Nat → Option AllocId → Value
  | 0,             _    => .nullPtr
  | Nat.succ data, prov => .ptr (Nat.succ data) prov

trustIrDenseMatch
/-- Value-level data projection of a fat-pointer value: the data lane as a
    thin pointer. `none` on every non-`.fatPtr` value. -/
def fatPtrDataValue : Value → Option Value
  | .fatPtr data prov _ => some (fatPtrDataLane data prov)
  | _              => none

trustIrDenseMatch
/-- Value-level metadata projection of a fat-pointer value. -/
def fatPtrMetadataValue : Value → Option Value
  | .fatPtr _ _ metadata => some metadata
  | _                  => none

trustIrDenseMatch
/-- Value-level fat-pointer injection: a (possibly null) thin data pointer
    plus a metadata value. `.nullPtr` injects as data address 0, and
    `fatPtrDataValue` maps that address back to `.nullPtr`. This matches the
    Rust interpreter's `NullPtr` lane and makes the pointer trio agree even at
    the null boundary. -/
def fatPtrFromPartsValue : Value → Value → Option Value
  | .ptr a p, m => some (.fatPtr a p m)
  | .nullPtr, m => some (.fatPtr 0 none m)
  | _,        _ => none

/-- Evaluate `PtrData`: extract the data-address lane.

    Fat path (`Ty.FatPtr`): project the data lane of a `.fatPtr` as a thin
    `.ptr`. Thin path: provenance-preserving identity on the pointer
    (mirrors interpret.rs eval_ptr_data). -/
def semPtrData (ptrTy : Ty) (ptrId : ValueId) (model : ByteModel := .le64) : Sem ValueId := do
  match ptrTy with
  | .FatPtr kind => do
    let ptrVal ← Sem.lookupValue ptrId
    if !(fatPtrStoreValueValidFor model (.FatPtr kind) ptrVal) then
      Sem.throwTypeError "PtrData: operand does not inhabit the fat-pointer kind"
    else
      match fatPtrDataValue ptrVal with
      | some v => Sem.bindFresh v
      | none   => Sem.throwTypeError "PtrData: operand is not a fat-pointer value"
  | _ =>
    if ptrTy.isPointerLike then do
      let ptrVal ← Sem.lookupValue ptrId
      match ptrVal with
      | .ptr a p => do
        let a ← Sem.targetAddress model "pointer projection/injection" a
        Sem.bindFresh (.ptr a p)
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
def semPtrMetadata (ptrTy : Ty) (metadataTy : Ty) (ptrId : ValueId) (model : ByteModel := .le64) : Sem ValueId := do
  match ptrTy with
  | .FatPtr kind => do
    if !(metadataTyMatchesFor model metadataTy kind) then
      Sem.throwTypeError "PtrMetadata: declared metadata type does not match the fat-pointer kind"
    else do
      let ptrVal ← Sem.lookupValue ptrId
      if !(fatPtrStoreValueValidFor model (.FatPtr kind) ptrVal) then
        Sem.throwTypeError "PtrMetadata: operand does not inhabit the fat-pointer kind"
      else
        match fatPtrMetadataValue ptrVal with
        | some m => Sem.bindFresh m
        | none   => Sem.throwTypeError "PtrMetadata: operand is not a fat-pointer value"
  | _ =>
    if ptrTy.isPointerLike then do
      let ptrVal ← Sem.lookupValue ptrId
      match ptrVal with
      | .ptr _ _ | .nullPtr =>
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
    (dataId metadataId : ValueId) (model : ByteModel := .le64) : Sem ValueId := do
  let dataVal ← Sem.lookupValue dataId
  let metaVal ← Sem.lookupValue metadataId
  Sem.rejectPartial dataVal "PtrFromParts data"
  Sem.rejectPartial metaVal "PtrFromParts metadata"
  match ptrTy with
  | .FatPtr kind => do
    if !(metadataTyMatchesFor model metadataTy kind) then
      Sem.throwTypeError "PtrFromParts: declared metadata type does not match the fat-pointer kind"
    else do
      if !(metadataInhabitsFor model kind metaVal) then
        Sem.throwTypeError "PtrFromParts: metadata operand does not inhabit the declared metadata type"
      else do
        match fatPtrFromPartsValue dataVal metaVal with
        | some v => Sem.bindFresh v
        | none   => Sem.throwTypeError "PtrFromParts: data operand is not a thin pointer"
  | _ =>
    if ptrTy.isPointerLike then do
      if metadataTy != .Unit then
        Sem.throwTypeError "PtrFromParts: thin pointer metadata is Unit"
      else do
        match metaVal with
        | .aggregate [] => do
          match dataVal with
          | .ptr a p => Sem.bindFresh (.ptr a p)
          | .nullPtr => Sem.bindFresh .nullPtr
          | _        => Sem.throwTypeError "PtrFromParts: data operand is not a pointer"
        | _ => Sem.throwTypeError "PtrFromParts: metadata operand is not Unit"
    else
      Sem.throwTypeError "PtrFromParts: expected pointer-like type"

-- =================================================================
-- Dealloc semantics
-- =================================================================

/-- Clear the permission entry for an allocation (set to none). Mirrors
    TrustIr.Semantics.ARC.clearPermission but scoped to generic dealloc. -/
def clearPermissionAt (permissions : PermissionMap) (allocId : AllocId) : PermissionMap :=
  fun id' => if id' == allocId then none else permissions id'

/-- Clear the refcount entry for an allocation (set to none). -/
def clearRefCountAt (refCounts : RefCountMap) (allocId : AllocId) : RefCountMap :=
  fun id' => if id' == allocId then none else refCounts id'

trustIrDenseMatch
/-- Evaluate a Dealloc instruction.

    Frees the allocation the pointer operand was DERIVED from (its
    provenance). The pointer MUST be that allocation's base address; freeing
    an interior or one-past-the-end pointer is UB, matching the C free and
    Rust Box::drop contracts — and it never frees a NEIGHBOUR that happens to
    start at that address. The allocation's permission must allow
    deallocation (Permission.canDealloc): Owned (Rust Box, C malloc)
    and rawPtr (C — allowed but treated as UB-prone) qualify; unique /
    shared borrows and ARC-managed refs do not. ARC allocations are
    freed through semRelease (TrustIr.Semantics.ARC).

    Observable effect: marks the allocation dead, clears its permission
    entry, and clears its refcount entry. A later access through any pointer
    derived from it raises UB at `Sem.accessAddr`'s liveness check.

    Errors:
    - nullPtr, or a pointer with no provenance -> throwUB.
    - Non-pointer operand -> throwTypeError.
    - The address is not the allocation's base -> throwUB.
    - The allocation is already dead -> throwUB (double free).
    - Permission forbids dealloc (e.g. sharedBorrow) -> throwUB.

    Mirrors Rust Inst::Dealloc (`MemoryState::dealloc`,
    crates/trust-ir/src/interpret.rs). -/
def semDealloc (ptrId : ValueId) : Sem Unit := do
  let ptrVal ← Sem.lookupValue ptrId
  let (addr, id) ← match ptrVal with
    | .ptr a (some id) => pure (a, id)
    | .ptr a none =>
      if a == 0 then Sem.throwUB "Dealloc: null pointer dereference"
      else Sem.throwUB (trustIrStringBuild s!"Dealloc: pointer value {a} has no allocation provenance")
    | .nullPtr => Sem.throwUB "Dealloc: null pointer dereference"
    | _        => Sem.throwTypeError "Dealloc: operand is not a pointer"
  let s ← Sem.getState
  let alloc ← match s.memory.lookup id with
    | some a => pure a
    | none   => Sem.throwUB "Dealloc: unknown allocation"
  if addr != alloc.base then
    Sem.throwUB "Dealloc: pointer must reference allocation base"
  if !alloc.alive then
    Sem.throwUB "Dealloc: allocation is already dead (double free)"
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
-- Bulk memory: MemCopy / MemSet (WS3.20, F-057)
-- =================================================================

/-- Two byte ranges `[a, a + n)` and `[b, b + n)` overlap (both non-empty). -/
def byteRangesOverlap (a b n : Nat) : Bool :=
  n != 0 && a < b + n && b < a + n

/-- The dynamic byte count of a bulk op: an unsigned integer value
    (`Usize`/`U64` by the validator's typing rule; here any non-negative
    `.int`). Inspecting a poison count is UB; a non-integer is a type error. -/
def bulkByteCount (op : String) (countId : ValueId) : Sem Nat := do
  let countVal ← Sem.lookupValue countId
  Sem.rejectPartial countVal op
  match countVal with
  | .int _ n =>
    if n < 0 then Sem.throwTypeError s!"{op}: byte count must be unsigned"
    else pure n.toNat
  | _ => Sem.throwTypeError s!"{op}: byte count is not an integer"

/-- The address a bulk op's pointer operand names, after the same
    `Sem.accessAddr` check a `Load`/`Store` makes over `count` bytes at
    alignment 1 (the interpreter reads and writes a bulk image with
    alignment 1): null, no provenance, a dead allocation or a range outside
    the allocation the pointer was derived from is UB. -/
def bulkPointer (op : String) (ptrId : ValueId) (count : Nat) (model : ByteModel := .le64) : Sem Addr := do
  let ptrVal ← Sem.lookupValue ptrId
  Sem.rejectPartial ptrVal op
  Sem.accessAddr op ptrVal count 1 model

/-- Evaluate a `MemCopy` instruction: copy `bytes` bytes from `src` to
    `dst`, carrying every byte's VALUE and INIT STATE — the image is read
    with `readBytesMaybeUninit` and written with `writeBytesMaybeUninit`,
    the same copy-propagates-poison pair a non-strict scalar `Load`+`Store`
    uses, so an uninitialized source byte stays uninitialized at the
    destination. A stored pointer is its address bytes, so a pointer copied
    through here recovers its provenance by address when it is loaded
    (`decodeValueAt`), as in the interpreter.

    UB: a poison count; either range outside the allocation its pointer was
    derived from (`bulkPointer`); and, with `overlap = false` (memcpy), overlapping
    ranges (`byteRangesOverlap`). With `overlap = true` (memmove) an
    overlapping copy is defined and as-if through a temporary — which it
    literally is: the whole image is read before anything is written. A zero
    count is a no-op that does not touch either pointer, matching
    `memcpy(p, q, 0)`. Alignment is not asserted: the copy is byte-granular.

    Mirrors Rust `Inst::MemCopy` (`eval_mem_copy`, crates/trust-ir/src/interpret.rs).
    `memcopy_preserves_bytes` (Proofs/MemoryProps.lean) states the byte-level
    contract of the write. -/
def semMemCopy (dstId srcId bytesId : ValueId) (overlap : Bool) (model : ByteModel := .le64) : Sem Unit := do
  let op := if overlap then "MemCopy(overlap)" else "MemCopy"
  let count ← bulkByteCount op bytesId
  if count == 0 then pure ()
  else
    let dst ← bulkPointer op dstId count model
    let src ← bulkPointer op srcId count model
    let s ← Sem.getState
    if !overlap && byteRangesOverlap dst src count then
      Sem.throwUB "MemCopy: source and destination overlap and the copy is not marked overlap (memmove)"
    let image := s.memory.readImage src count
    Sem.modifyState fun st =>
      { st with memory := st.memory.writeImage dst image }

/-- Evaluate a `MemSet` instruction: write the `U8` fill `byte` to each of
    `bytes` bytes at `dst`; every written byte becomes INITIALIZED (a stored
    pointer whose bytes are overwritten is destroyed, as under a byte store).
    UB: a poison count or fill; a range outside the allocation the pointer
    was derived from. A zero count is a no-op. Mirrors Rust `Inst::MemSet` (`eval_mem_set`). -/
def semMemSet (dstId byteId bytesId : ValueId) (model : ByteModel := .le64) : Sem Unit := do
  let count ← bulkByteCount "MemSet" bytesId
  let fillVal ← Sem.lookupValue byteId
  Sem.rejectPartial fillVal "MemSet fill byte"
  let fill ← match fillVal with
    | .int 8 b => pure (UInt8.ofNat b.toNat)
    | _ => Sem.throwTypeError "MemSet: fill byte is not a u8"
  if count == 0 then pure ()
  else
    let dst ← bulkPointer "MemSet" dstId count model
    Sem.modifyState fun st =>
      { st with memory := st.memory.writeImage dst (ByteImage.fill count (some fill)) }

-- =================================================================
-- Memory safety predicates (for theorem statements)
-- =================================================================

/-- Predicate: a pointer is not null. -/
def isNotNull (v : Value) : Prop :=
  match v with
  | .ptr addr _ => addr != 0
  | _ => False

/-- Predicate: an address is properly aligned for a type. -/
def isAligned (addr : Addr) (ty : Ty) : Prop :=
  match ty.byteSize with
  | some size => addr % size == 0
  | none => True  -- No alignment requirement for unsized types

end TrustIr

#trustIrAxiomsExact TrustIr.vectorScalarByteSize == []
#trustIrAxiomsExact TrustIr.Ty.byteSize == []
#trustIrAxiomsExact TrustIr.Ty.byteAlign == []
#trustIrAxiomsExact TrustIr.Ty.byteSizeAtModel == []
#trustIrAxiomsExact TrustIr.Ty.byteAlignAtModel == []

#trustIrAxiomsExact TrustIr.checkedMemoryAlign == []

#trustIrAxiomsExact TrustIr.semDealloc == []
#trustIrAxiomsExact TrustIr.metadataInhabits == []
#trustIrAxiomsExact TrustIr.Sem.targetAddress == []

#trustIrAxiomsExact TrustIr.fatPtrDataValue == []
#trustIrAxiomsExact TrustIr.fatPtrMetadataValue == []
#trustIrAxiomsExact TrustIr.fatPtrFromPartsValue == []
