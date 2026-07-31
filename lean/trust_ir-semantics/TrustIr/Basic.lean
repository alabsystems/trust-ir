-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Basic types for TrustIr formalization.
-- Mirrors: crates/trust_ir/src/value.rs (typed IDs)
--          crates/trust_ir/src/ty.rs (type system)

namespace TrustIr

/-!
# Basic Types

These types mirror the Rust TrustIr crate's type system exactly.
Each typed ID is a wrapper around Nat (corresponding to Rust's u32).
The type enum mirrors `trust_ir::Ty`.

## Mapping from Rust to Lean

| Rust type      | Lean type   | Notes                           |
|----------------|-------------|---------------------------------|
| `ValueId(u32)` | `ValueId`   | SSA value reference             |
| `BlockId(u32)` | `BlockId`   | Basic block reference           |
| `FuncId(u32)`  | `FuncId`    | Function reference              |
| `StructId(u32)`| `StructId`  | Struct definition reference     |
| `TyId(u32)`    | `TyId`      | Type reference (for arrays)     |
| `FuncTyId(u32)`| `FuncTyId`  | Function type reference         |
| `ProofId(u32)` | `ProofId`   | Proof annotation reference      |
| `ProofTag(u32)`| `ProofTag`  | Custom proof tag                |
-/

/-- SSA value reference. Index into a function's value table.
    Mirrors Rust: `pub struct ValueId(pub u32)` -/
structure ValueId where
  index : Nat
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- Basic block reference. Index into a function's block list.
    Mirrors Rust: `pub struct BlockId(pub u32)` -/
structure BlockId where
  index : Nat
  deriving DecidableEq, Hashable, Repr

/-- Function reference. Index into a module's function list.
    Mirrors Rust: `pub struct FuncId(pub u32)` -/
structure FuncId where
  index : Nat
  deriving DecidableEq, Hashable, Repr

/-- Global definition reference. Index into a module's globals table.
    Materialized as an SSA pointer by `Inst.GlobalAddr`; the first address-of a
    given global reserves an address and caches it, so repeats alias.
    Mirrors Rust: `pub struct GlobalId(pub u32)` -/
structure GlobalId where
  index : Nat
  deriving DecidableEq, BEq, Hashable, Repr

/-- Struct definition reference.
    Mirrors Rust: `pub struct StructId(pub u32)` -/
structure StructId where
  index : Nat
  deriving DecidableEq, Hashable, Repr

/-- Type reference. Index into a module's type table.
    Mirrors Rust: `pub struct TyId(pub u32)` -/
structure TyId where
  index : Nat
  deriving DecidableEq, Hashable, Repr

/-- Function type reference.
    Mirrors Rust: `pub struct FuncTyId(pub u32)` -/
structure FuncTyId where
  index : Nat
  deriving DecidableEq, Hashable, Repr

/-- Proof annotation reference.
    Mirrors Rust: `pub struct ProofId(pub u32)` -/
structure ProofId where
  index : Nat
  deriving DecidableEq, Hashable, Repr

/-- Custom proof tag for extensible proof annotations.
    Mirrors Rust: pub struct ProofTag in ty.rs -/
structure ProofTag where
  index : Nat
  deriving DecidableEq, Hashable, Repr

/-- Enum definition reference.
    Mirrors Rust: pub struct EnumId in value.rs -/
structure EnumId where
  index : Nat
  deriving DecidableEq, Hashable, Repr

/-- Record definition reference (ty-style named-field record).
    Mirrors Rust: pub struct RecordId in value.rs. Distinct from StructId
    even when indices collide -- records have no layout metadata and compare
    by field-set, structs have C-style layout. -/
structure RecordId where
  index : Nat
  deriving DecidableEq, Hashable, Repr

/-- Refinement predicate reference. Index into a module's CONTENT-INTERNED
    `predicates` table.
    Mirrors Rust: pub struct PredId in value.rs.

    Content-interned means the id is a function of the predicate's content
    alone: two predicates with the same meaning are the same id no matter
    which proof cited them. That is the structural fix for the join-drop
    miscompile class, where two carriers over an identical universe failed to
    merge at a control-flow join because different proofs had minted them,
    the shape was dropped, and the value silently reverted to the raw
    encoding convention. -/
structure PredId where
  index : Nat
  deriving DecidableEq, Hashable, Repr

/-- Universe reference. Index into a module's CONTENT-INTERNED `universes`
    table.
    Mirrors Rust: pub struct UnivId in value.rs.

    Content-interned for exactly the reason `PredId` is: a universe's identity
    is its EXTENSION, with no name, provenance or citing-proof id. Two
    carriers over the same universe therefore hold the same id and cannot
    fail to merge at a control-flow join. The predicate lattice that consumes
    this id is modelled in TrustIr/Pred.lean. -/
structure UnivId where
  index : Nat
  deriving DecidableEq, Hashable, Repr

/-- Closure type definition reference.
    Mirrors Rust: pub struct ClosureTyId in value.rs.
    A closure type is a bare FuncTyId plus an explicit captured-env frame
    (see ClosureTy). Captures are part of the type identity so self-
    referential FuncDefs route captured state through the type system
    instead of an opaque env pointer (ty issue 4145 soundness lesson). -/
structure ClosureTyId where
  index : Nat
  deriving DecidableEq, Hashable, Repr

/-- Binding-frame reference. Index into a function's local
    frame-definition table. Mirrors Rust BindingFrameId(u32) from
    crates/trust_ir/src/value.rs.

    Each Inst.OpenFrame declares a fresh BindingFrameId; the definition
    (slot layout) is carried inline on the instruction, not in a
    module-level registry. Frame handles flow through SSA as
    Value.frame; there is no first-class Ty.BindingFrame variant (issue
    #55 aligned Lean Ty with Rust, which never had one either). -/
structure BindingFrameId where
  index : Nat
  deriving DecidableEq, Hashable, Repr

/-!
# Type System

Mirrors Rust trust_ir::Ty from crates/trust_ir/src/ty.rs.

TrustIr types are explicit -- no implicit conversions. All casts are
separate instructions. Integer types carry both their bit width and
signedness as part of the type (I8..I128 signed, U8..U128 unsigned).

## Design note: Signed vs Unsigned

TrustIr carries signedness on the type (like Rust) rather than on each
instruction (like LLVM). The Lean Ty mirrors the Rust enum exactly,
with separately-typed I8..I128 / U8..U128 variants. Width-polymorphic
signedness decisions still happen at the instruction level (SDiv vs
UDiv, Slt vs Ult) so instructions can operate generically across both
families, but the static type identifies the signed/unsigned
interpretation of a value.

Resolving the Rust/Lean divergence for unsigned types is issue #53 --
without U8..U128 in the Lean Ty, any safety proof over a Rust module
containing unsigned ints was vacuous on the Lean side.
-/

/-- Representation hint for Ty.Set.
    Mirrors Rust trust_ir::SetRepr in ty.rs.

    Small-scalar sets (e.g. Set U8) can be lowered as bitsets when the
    universe is bounded; unbounded / recursive element types fall through
    to a boxed runtime representation. The repr is part of type identity
    so lowering decisions are stable and cannot be silently aliased. -/
inductive SetRepr where
  /-- Flat bitset lowering (small bounded scalar elements). -/
  | Bitset : SetRepr
  /-- Boxed runtime container (hash set / sorted vec). Default conservative
      choice; frontends may refine to Bitset when they can prove the
      universe is small and dense. -/
  | Boxed  : SetRepr
  deriving DecidableEq, Hashable, Repr, BEq

/-- Default set representation is Boxed (the conservative choice). -/
instance : Inhabited SetRepr := ⟨.Boxed⟩

/-- Wide/fat pointer kind. Mirrors Rust `trust_ir::ty::FatPtrKind`
    (`Slice(TyId)` / `Str` / `TraitObject { trait_id }`). Carried by
    `Ty.FatPtr`. The Lean operational model gives all three kinds a two-lane
    `(data, metadata)` value, the pointer decomposition/recomposition trio, and
    the fixed 64-bit target's 16-byte memory image. -/
inductive FatPtrKind where
  | Slice       : TyId -> FatPtrKind
  | Str         : FatPtrKind
  | TraitObject : UInt32 -> FatPtrKind
  deriving Repr, DecidableEq

/-- TrustIr type. Mirrors Rust trust_ir::Ty exactly (issue #53 closes the
    unsigned-integer divergence; issue #55 closes the Void/BindingFrame
    divergence).

    Every value in TrustIr has an explicit type. Integer types carry both
    bit width and signedness as part of the type identity: I8..I128 are
    signed, U8..U128 are unsigned. This matches the Rust trust_ir::Ty enum
    at crates/trust_ir/src/ty.rs:40-97.

    New aggregate types (Set, Sequence, Record, Closure) were added to
    support ty-style IR lowering -- see
    designs/2026-04-18-ty-supremacy-trust_ir-scope.md section 3.3.

    Binding-frame types do not appear in Ty: BindingFrameId is carried
    inline on Inst.OpenFrame, and frame values live in SSA as Value.frame
    (not as a first-class Ty). The prior Lean-only Ty.Void variant has
    also been removed -- context-dependent aggregate/frame types surface
    via Ty.Unit sentinels on Value.ty, not via a distinct Void
    constructor. -/
inductive Ty where
  -- Signed integers
  | I8      : Ty
  | I16     : Ty
  | I32     : Ty
  | I64     : Ty
  | I128    : Ty
  -- Unsigned integers (issue #53: mirror Rust Ty::U{8,16,32,64,128})
  | U8      : Ty
  | U16     : Ty
  | U32     : Ty
  | U64     : Ty
  | U128    : Ty
  -- v25 B1 scalars (mirror Rust Ty::Isize/Usize/Char/Error). Isize/Usize are
  -- pointer-width integers; this executable model pins the 64-bit targets
  -- (the same convention as Ptr below). Char is a 32-bit unsigned carrier
  -- whose Unicode-scalar valid range is the validator's checked claim.
  -- Error is the producer-internal fail-closed typing placeholder: never
  -- wire-legal, no semantics (every helper returns none/false for it).
  | Isize   : Ty
  | Usize   : Ty
  | Char    : Ty
  | Error   : Ty
  -- Floating-point
  | F16     : Ty
  | F32     : Ty
  | F64     : Ty
  -- Special primitives
  | Bool    : Ty
  | Ptr     : Ty
  -- Wide/fat pointer (two-lane executable value and memory representation).
  | FatPtr  : FatPtrKind -> Ty
  -- Composite types
  | Struct   : StructId -> Ty
  | Array    : TyId -> Nat -> Ty          -- element type id, length
  | Func     : FuncTyId -> Ty
  -- Special types (Rust Unit = (), Never = !)
  | Unit     : Ty
  | Never    : Ty
  -- Aggregate types
  | Tuple    : List Ty -> Ty
  | Enum     : EnumId -> Ty
  /-- Fixed-width SIMD/vector value with `lanes` elements of `elemTy`.
      This first executable Lean path supports a bounded subset:
      `<4 x i32>`, `<2 x i64>`, `<4 x bool>`, and `<2 x bool>`. -/
  | Vector   : Nat -> Ty -> Ty
  -- Reference types (Rust borrowing)
  | Ref      : Ty -> Ty                   -- immutable reference
  | RefMut   : Ty -> Ty                   -- mutable reference
  -- Raw pointer types (C semantics)
  | PtrConst : Ty -> Ty                   -- const pointer
  | PtrMut   : Ty -> Ty                   -- mutable pointer
  -- Reference counted (Swift ARC)
  | Rc       : Ty -> Ty                   -- reference counted
  -- ty supremacy aggregates (designs/2026-04-18-ty-supremacy-trust_ir-scope.md)
  /-- Unordered homogeneous set. Element type is referenced via TyId and
      the SetRepr hint is part of type identity. -/
  | Set       : TyId -> SetRepr -> Ty
  /-- Ordered variable-length sequence (TLA+ Seq of T). -/
  | Sequence  : TyId -> Ty
  /-- Named-field record (ty semantics). Distinct from Struct: no fixed
      layout, no offsets, equality by field-set. -/
  | Record    : RecordId -> Ty
  /-- First-class closure: bare function signature bundled with a typed
      captured-environment frame. -/
  | Closure   : ClosureTyId -> Ty
  /-- Refinement type: a value of the base type (referenced by TyId) that
      additionally satisfies the predicate (referenced by PredId).

      REPRESENTATION-PRESERVING: `Refine b p` has EXACTLY the representation
      of `b` — same width, same layout, same value semantics. The predicate is
      proof surface only, so every operational rule delegates to the base type
      and no evaluation step can observe the refinement. See `Ty.refineBase`.

      Its purpose is to put an encoding CONVENTION in the type. When a
      producer hand-encodes sums, products, functions and sets into anonymous
      integer lanes, "this lane is an INDEX into universe U, not a MEMBER of
      U" is part of the value's MEANING, not a precision claim: dropping it
      REINTERPRETS the value rather than widening it. Carried here, a dropped
      fact becomes the lattice top and fails its consumption site instead. -/
  | Refine    : TyId -> PredId -> Ty
  deriving Repr, BEq

/-- Returns the bit width of a type, or none for compound types.
    Mirrors Rust Ty::bit_width. -/
def Ty.bitWidth : Ty -> Option Nat
  | .Bool     => some 1
  | .I8       => some 8
  | .I16      => some 16
  | .I32      => some 32
  | .I64      => some 64
  | .I128     => some 128
  -- Issue #53: unsigned integer widths match their signed counterparts.
  | .U8       => some 8
  | .U16      => some 16
  | .U32      => some 32
  | .U64      => some 64
  | .U128     => some 128
  -- v25: pointer-width integers at the model's 64-bit pin; char is 32-bit.
  | .Isize    => some 64
  | .Usize    => some 64
  | .Char     => some 32
  | .F16      => some 16
  | .F32      => some 32
  | .F64      => some 64
  | .Vector lanes elemTy =>
    match elemTy.bitWidth with
    | some elemWidth => some (lanes * elemWidth)
    | none => none
  | .Ptr      => some 64
  -- Pointer-like types are 64-bit
  | .Ref _    => some 64
  | .RefMut _ => some 64
  | .PtrConst _ => some 64
  | .PtrMut _ => some 64
  | .Rc _     => some 64
  -- Zero-sized and compound types have no fixed bit width
  | _         => none

/-- Returns true if the type is a signed integer type (I8..I128).
    Mirrors Rust Ty::is_signed. -/
def Ty.isSigned : Ty → _root_.Bool
  | .I8 | .I16 | .I32 | .I64 | .I128 | .Isize => true
  | _ => false

/-- Returns true if the type is an unsigned integer type (U8..U128).
    Mirrors Rust Ty::is_unsigned. -/
def Ty.isUnsigned : Ty → _root_.Bool
  | .U8 | .U16 | .U32 | .U64 | .U128 | .Usize | .Char => true
  | _ => false

/-- Returns true if the type is an integer type (signed or unsigned).
    Mirrors Rust Ty::is_integer. Issue #53 widened this to include
    U8..U128 alongside I8..I128. -/
def Ty.isInteger : Ty → _root_.Bool
  | .I8 | .I16 | .I32 | .I64 | .I128
  | .U8 | .U16 | .U32 | .U64 | .U128
  | .Isize | .Usize | .Char => true
  | _ => false

/-- Returns true if the type is a floating-point type.
    Mirrors Rust `Ty::is_float()`. -/
def Ty.isFloat : Ty → _root_.Bool
  | .F16 | .F32 | .F64 => true
  | _ => false

/-- Returns true if the type is numeric (integer or float).
    Mirrors Rust `Ty::is_numeric()`. -/
def Ty.isNumeric (ty : Ty) : _root_.Bool :=
  ty.isInteger || ty.isFloat

/-- Returns true for reference types: Ref, RefMut, PtrConst, PtrMut, Rc.
    Mirrors Rust Ty::is_reference. -/
def Ty.isReference : Ty -> _root_.Bool
  | .Ref _ | .RefMut _ | .PtrConst _ | .PtrMut _ | .Rc _ => true
  | _ => false

/-- Returns true for any pointer-like type (Ptr, Ref, RefMut, PtrConst, PtrMut, Rc). -/
def Ty.isPointerLike : Ty -> _root_.Bool
  | .Ptr => true
  | ty   => ty.isReference

/-- Returns true for aggregate / collection types: Set, Sequence, Record,
    Tuple, Array, Struct, Enum. Mirrors Rust Ty.is_aggregate. -/
def Ty.isAggregate : Ty -> _root_.Bool
  | .Set _ _    => true
  | .Sequence _ => true
  | .Record _   => true
  | .Tuple _    => true
  | .Array _ _  => true
  | .Struct _   => true
  | .Enum _     => true
  | .Vector _ _ => true
  | _           => false

/-- Returns true for closure types (function with captured environment).
    Mirrors Rust Ty.is_closure. -/
def Ty.isClosure : Ty -> _root_.Bool
  | .Closure _ => true
  | _          => false

/-- Returns true for refinement types. Mirrors Rust Ty.is_refine. -/
def Ty.isRefine : Ty -> _root_.Bool
  | .Refine _ _ => true
  | _           => false

/-- The base type reference a refinement delegates to, or none.
    Mirrors Rust `Ty::refinement`.

    Every operational question about a `Refine b p` — width, layout, value
    semantics — is the corresponding question about the module type table's
    entry at `b`. This is what makes the construct unable to move a byte: it
    adds proof surface and nothing else. Note that `Ty.bitWidth` returns none
    for it for the SAME reason it does for `Array`/`Set`/`Sequence`: the
    answer needs the module type table, which these context-free helpers do
    not have. -/
def Ty.refineBase : Ty -> Option TyId
  | .Refine base _ => some base
  | _              => none

/-- The predicate a refinement carries, or none.
    Mirrors Rust `Ty::predicate`.

    A `none` here is the lattice TOP — "no information" — at a consumption
    site, NEVER "no constraint to check". -/
def Ty.refinePred : Ty -> Option PredId
  | .Refine _ pred => some pred
  | _              => none

/-- Function type definition. Mirrors Rust trust_ir::FuncTy. -/
structure FuncTyDef where
  params   : List Ty
  returns  : List Ty
  isVararg : Bool
  deriving BEq, Repr

/-- Struct field definition. Mirrors Rust trust_ir::FieldDef. -/
structure FieldDef where
  name   : String
  ty     : Ty
  offset : Option Nat
  deriving BEq, Repr

/-- Struct type definition. Mirrors Rust trust_ir::StructDef. -/
structure StructDef where
  id     : StructId
  name   : String
  fields : List FieldDef
  size   : Option Nat
  align  : Option Nat
  deriving Repr

/-- Enum tag-representation hint. Mirrors Rust trust_ir::EnumTagRepr. -/
inductive EnumTagRepr where
  | u8 | u16 | u32 | u64 | i8 | i16 | i32 | i64
  deriving BEq, Repr

/-- How an enum's discriminant is represented in memory. Mirrors Rust
    trust_ir::EnumTagEncoding (wire v31). -/
inductive EnumTagEncoding where
  | direct (tagOffset : Nat)
  | niche (untaggedVariant nicheVariantsStart nicheVariantsEnd : Nat)
      (nicheStart : Nat) (nicheOffset : Nat) (nicheTy : EnumTagRepr)
  deriving BEq, Repr

/-- Producer-supplied concrete enum layout. It is normative when present.
    Field offsets are grouped by variant and follow source field order. -/
structure EnumLayoutDescriptor where
  encoding : EnumTagEncoding
  size : Nat
  align : Nat
  variantFieldOffsets : List (List Nat)
  deriving BEq, Repr

/-- A single variant of an enum type. Mirrors Rust trust_ir::EnumVariant.
    `fieldNames` is fidelity metadata parallel to `fields`; empty means
    positional. -/
structure EnumVariantDef where
  name       : String
  fields     : List Ty
  fieldNames : List String := []
  deriving Repr

/-- Enum (sum) type definition. Mirrors Rust trust_ir::EnumDef. The trailing
    fields carry explicit discriminants, an optional tag representation, and
    the normative wire-v31 concrete layout descriptor. -/
structure EnumDef where
  id            : EnumId
  name          : String
  variants      : List EnumVariantDef
  discriminants : List (Option Int) := []
  tagRepr       : Option EnumTagRepr := none
  layout        : Option EnumLayoutDescriptor := none
  deriving Repr

/-- Definition of a named-field record (ty-style). Mirrors Rust
    trust_ir::RecordDef.

    Records are structurally typed labeled tuples with no layout metadata.
    Field order in the fields list is canonical (typically sorted by name)
    so that records with the same field-set compare equal by value.
    Frontends that need C-style struct layout (offsets, size, alignment)
    should use StructDef instead.

    Invariant: each field offset is none -- records have no layout. -/
structure RecordDef where
  id     : RecordId
  name   : String
  fields : List FieldDef
  deriving Repr

/-- First-class closure type: a bare function signature bundled with an
    explicit captured-environment frame. Mirrors Rust trust_ir::ClosureTy.

    The captures list records the types of values captured from the
    enclosing scope at closure-creation time. Captures are part of the
    type identity because TrustIr closures route captured state through the
    state partition explicitly -- cached closure bodies that reference
    stale captured state are the soundness bug pattern ty issue 4145
    hit for SA of bb in Ballot recursive defs.

    Bare function pointers (no captures) use Ty.Func FuncTyId directly;
    Ty.Closure ClosureTyId is for any function value with captured env. -/
structure ClosureTy where
  func     : FuncTyId
  captures : List Ty
  deriving Repr

namespace ClosureTy

/-- Closure with no captures (equivalent in semantics to a bare function
    pointer but with closure-typed value identity). -/
def bare (f : FuncTyId) : ClosureTy := { func := f, captures := [] }

/-- Number of captured-env slots. -/
def captureCount (c : ClosureTy) : Nat := c.captures.length

end ClosureTy

end TrustIr

/-!
# Bitwise operations on Int

Lean 4.8.0 does not include Int.land, Int.lor, Int.xor in the standard
library.  We define them here via conversion to Nat.  For the TrustIr
semantics all integer values are kept in the unsigned range [0, 2^w)
after truncation, so the Nat path is always taken in practice.
-/
namespace Int

/-- Bitwise AND of two integers via Nat. -/
def land (a b : Int) : Int :=
  match a, b with
  | .ofNat m, .ofNat n => .ofNat (Nat.land m n)
  | _, _ => 0

/-- Bitwise OR of two integers via Nat. -/
def lor (a b : Int) : Int :=
  match a, b with
  | .ofNat m, .ofNat n => .ofNat (Nat.lor m n)
  | _, _ => 0

/-- Bitwise XOR of two integers via Nat. -/
def xor (a b : Int) : Int :=
  match a, b with
  | .ofNat m, .ofNat n => .ofNat (Nat.xor m n)
  | _, _ => 0

-- Commutativity lemmas: correct but proof requires Nat.bitwise_comm
-- which is not available in Lean 4.8.0 / Mathlib v4.8.0 standard library.
-- These reduce to Nat.land/lor/xor commutativity which requires bitwise induction.
-- Local helper: Nat.land is commutative.
-- Proved via testBit decomposition: (m &&& n).testBit i = (n &&& m).testBit i.
private theorem nat_land_comm (m n : Nat) : Nat.land m n = Nat.land n m := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [show Nat.land m n = m &&& n from rfl, show Nat.land n m = n &&& m from rfl]
  rw [Nat.testBit_and, Nat.testBit_and, Bool.and_comm]

-- Local helper: Nat.lor is commutative.
private theorem nat_lor_comm (m n : Nat) : Nat.lor m n = Nat.lor n m := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [show Nat.lor m n = m ||| n from rfl, show Nat.lor n m = n ||| m from rfl]
  rw [Nat.testBit_or, Nat.testBit_or, Bool.or_comm]

-- Local helper: Nat.xor is commutative.
private theorem nat_xor_comm (m n : Nat) : Nat.xor m n = Nat.xor n m := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [show Nat.xor m n = m ^^^ n from rfl, show Nat.xor n m = n ^^^ m from rfl]
  rw [Nat.testBit_xor, Nat.testBit_xor]
  simpa using Bool.xor_comm (m.testBit i) (n.testBit i)

theorem land_comm (a b : Int) : land a b = land b a := by
  unfold land
  cases a with
  | ofNat m => cases b with
    | ofNat n => exact congrArg Int.ofNat (nat_land_comm m n)
    | negSucc n => rfl
  | negSucc m => cases b with
    | ofNat n => rfl
    | negSucc n => rfl

theorem lor_comm (a b : Int) : lor a b = lor b a := by
  unfold lor
  cases a with
  | ofNat m => cases b with
    | ofNat n => exact congrArg Int.ofNat (nat_lor_comm m n)
    | negSucc n => rfl
  | negSucc m => cases b with
    | ofNat n => rfl
    | negSucc n => rfl

theorem xor_comm (a b : Int) : xor a b = xor b a := by
  unfold xor
  cases a with
  | ofNat m => cases b with
    | ofNat n => exact congrArg Int.ofNat (nat_xor_comm m n)
    | negSucc n => rfl
  | negSucc m => cases b with
    | ofNat n => rfl
    | negSucc n => rfl

end Int
