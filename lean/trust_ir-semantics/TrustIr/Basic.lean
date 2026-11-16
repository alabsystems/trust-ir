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
    (`Slice(TyId)` / `Str` / `TraitObject { trait_id }` / `ContainerLen` /
    `ContainerVtable`). Carried by `Ty.FatPtr`. The Lean operational model
    gives every kind a two-lane `(data, metadata)` value, the pointer
    decomposition/recomposition trio, and the fixed 64-bit target's 16-byte
    memory image.

    The two container-tail kinds (wire v38 / v40) differ from their siblings
    only in what the DATA pointer addresses (the container header, not the
    DST content), never in the metadata lane, so they are classified by what
    their metadata MEANS, exactly as Rust `PointerMetadataShape::metadata_ty`
    (crates/trust-ir/src/shape.rs) classifies them:

    * `ContainerLen` joins `Slice`/`Str` on the unsigned-length `U64` lane;
    * `ContainerVtable` joins `TraitObject` on the opaque vtable `Ptr` lane,
      and must NEVER join a length arm — a vtable word read as a length is a
      type confusion (`FatPtrKind.metadataTy` / `metadataTyMatches` /
      `decodeValue`, Semantics/Memory.lean).

    Neither carries a payload: the tail type is not what either kind is about
    (Rust carries no `TyId` / trait id for them either). The addressed
    container has an unsized tail, which no `StructDef` can describe, so
    consumers reach into it with explicit `GEP` / typed `Load`. Unsized-tail
    pointee ids are a DECISION GATE (finding F-123, AD-1'), not drift; adding
    one is a coordinated Rust + Lean + wire change. -/
inductive FatPtrKind where
  | Slice           : TyId -> FatPtrKind
  | Str             : FatPtrKind
  | TraitObject     : UInt32 -> FatPtrKind
  | ContainerLen    : FatPtrKind
  | ContainerVtable : FatPtrKind
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
  /-- Exact nominal semantic identity. No Core layout or operational rule is
      implied; explicit checked dialect legalization must eliminate it. -/
  | Dialect   : String -> String -> UInt32 -> Ty
  /-- Nominal opaque runtime handle (v43, mirrors Rust `Ty::Handle(HandleTy)`):
      the exact `(name, runtime)` pair of a trusted runtime's opaque value. One
      pointer word at the machine level (see `Ty.bitWidth`), but NOT
      pointer-like: no memory, cast or arithmetic rule accepts it, so the only
      operational rules that touch a handle are exact-typed transport (copy,
      select, call, return, branch). Its origin is a pinned runtime entry
      point the model does not execute; a module using one is outside the
      proven subset (`bridge.rs` excludes it). -/
  | Handle    : String -> String -> Ty
  /-- Addressable possibly-uninitialized geometry; excluded from by-value lowering. -/
  | Storage : Nat -> Nat -> Ty
  /-- A nominal zero-byte function item. The source function header supplies
      its unique identity and signature; this is not a function pointer. -/
  | FnItem : FuncId -> Ty
  deriving Repr, BEq

/-- One exhaustive width policy for fixed scalars, pointer words and vectors.
Every new type constructor must make an explicit width decision. The supplied
pointer width is a mathematical parameter; supported runtime models remain
exactly ByteModel.le32/le64. -/
@[reducible] def Ty.bitWidthAtPointerBits (pointerBits : Nat) : Ty → Option Nat
  | .I8 => some 8
  | .I16 => some 16
  | .I32 => some 32
  | .I64 => some 64
  | .I128 => some 128
  | .U8 => some 8
  | .U16 => some 16
  | .U32 => some 32
  | .U64 => some 64
  | .U128 => some 128
  | .Isize => some pointerBits
  | .Usize => some pointerBits
  | .Char => some 32
  | .Error => none
  | .F16 => some 16
  | .F32 => some 32
  | .F64 => some 64
  | .Bool => some 1
  | .Ptr => some pointerBits
  | .FatPtr _ => none
  | .Struct _ => none
  | .Array _ _ => none
  | .Func _ => none
  | .FnItem _ => none
  | .Unit => none
  | .Never => none
  | .Tuple _ => none
  | .Enum _ => none
  | .Vector lanes elem => (elem.bitWidthAtPointerBits pointerBits).map (lanes * ·)
  | .Ref _ => some pointerBits
  | .RefMut _ => some pointerBits
  | .PtrConst _ => some pointerBits
  | .PtrMut _ => some pointerBits
  | .Rc _ => some pointerBits
  | .Set _ _ => none
  | .Sequence _ => none
  | .Record _ => none
  | .Closure _ => none
  | .Refine _ _ => none
  | .Dialect _ _ _ => none
  | .Handle _ _ => some pointerBits
  | .Storage _ _ => none

/-- Legacy default width, sharing the same policy as target-width queries. -/
def Ty.bitWidth (ty : Ty) : Option Nat := ty.bitWidthAtPointerBits 64

/-- The two canonical little-endian pointer representations. -/
inductive ByteModel where
  | le32
  | le64
  deriving Repr, DecidableEq, BEq

def ByteModel.pointerBytes : ByteModel → Nat
  | .le32 => 4
  | .le64 => 8

/-- Kept as a computation in compiled code, like `Sem.addrBits`, rather than
    storing a closed large integer's platform padding in an olean. -/
@[noinline] def ByteModel.pointerBits (model : ByteModel) : Nat :=
  8 * model.pointerBytes

def ByteModel.addressLimit (model : ByteModel) : Nat :=
  256 ^ model.pointerBytes

/-- No malformed width or byte order can construct a supported model. The
    caller must additionally establish the module's canonical scalar ABI. -/
def ByteModel.ofRepresentation : Nat → Bool → Option ByteModel
  | 4, true => some .le32
  | 8, true => some .le64
  | _, _ => none

def ByteModel.lengthTy : ByteModel → Ty
  | .le32 => .U32
  | .le64 => .U64

/-- Pointer-width integers and pointer representations use the selected
    width. All fixed-width scalar types retain their existing meanings. -/
def Ty.bitWidthAtModel (model : ByteModel) (ty : Ty) : Option Nat :=
  ty.bitWidthAtPointerBits model.pointerBits

/-- The default remains definitionally the legacy width query. -/
def Ty.bitWidthFor (model : ByteModel) (ty : Ty) : Option Nat :=
  match model with
  | .le64 => ty.bitWidth
  | .le32 => ty.bitWidthAtModel .le32

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

/-- Test only the Bool constructor without recursive type equality. -/
def Ty.isBool : Ty → _root_.Bool
  | .Bool => true
  | _ => false

theorem Ty.isBool_iff (ty : Ty) : ty.isBool = true ↔ ty = .Bool := by
  cases ty <;> simp [Ty.isBool]

/-- Returns true if the type is an integer type (signed or unsigned).
    Mirrors Rust Ty::is_integer. Issue #53 widened this to include
    U8..U128 alongside I8..I128. -/
def Ty.isInteger : Ty → _root_.Bool
  | .I8 | .I16 | .I32 | .I64 | .I128
  | .U8 | .U16 | .U32 | .U64 | .U128
  | .Isize | .Usize | .Char => true
  | _ => false

/-- The `Char` VALIDITY INVARIANT (lowering-target subset v4, WS2.17).

    `Ty.Char` is a 32-bit unsigned carrier, but its inhabitants are exactly
    the Unicode SCALAR VALUES: `v < 0x110000` and `v` outside the surrogate
    block `0xD800..=0xDFFF`. Nothing in the arithmetic model rules a
    surrogate out — the carrier is just an integer — so the invariant is a
    separate predicate every `Char` origin must re-establish.

    Mirrors the reference interpreter's `check_char_validity`
    (`crates/trust-ir/src/interpret.rs`), which reports a violation as
    UNDEFINED BEHAVIOUR at every SSA bind site, and the STATIC half of the
    same rule, subset v4 structural condition 6
    (`ConformanceSubset::char_origin_excluded`), which admits only a
    range-validated `Const` and `Cast ZExt` of a `U8` as origins. -/
def validChar (v : Nat) : Prop :=
  v < 0x110000 ∧ ¬(0xD800 ≤ v ∧ v ≤ 0xDFFF)

instance (v : Nat) : Decidable (validChar v) := by
  unfold validChar; infer_instance

/-- Every `u8` is a Unicode scalar value, so the ONE admitted computed
    `Char` origin — `zext u8 -> char`, subset v4 condition 6 — establishes
    [`validChar`] by construction. This is the theorem the condition rests
    on: no range check is needed on that edge. -/
theorem validChar_of_lt_256 {v : Nat} (h : v < 256) : validChar v := by
  refine ⟨by omega, ?_⟩
  rintro ⟨hlo, -⟩
  omega

/-- The mutation control: the first surrogate is NOT a valid `char`, so a
    `Char` constant of `0xD800` is refused. A model that dropped the
    surrogate conjunct from [`validChar`] would accept it. -/
theorem not_validChar_surrogate : ¬ validChar 0xD800 := by
  rintro ⟨-, hsur⟩
  exact hsur ⟨by omega, by omega⟩

/-- The other mutation control: `0x110000` is one past the last code point.
    A model that dropped the range conjunct would accept it. -/
theorem not_validChar_above_max : ¬ validChar 0x110000 := by
  rintro ⟨hlt, -⟩
  omega

/-- The `Char` carrier is 32 bits wide, so [`validChar`] is a STRICTLY
    stronger property than "fits the carrier": the carrier admits values the
    type does not. -/
theorem validChar_lt_two_pow_32 {v : Nat} (h : validChar v) : v < 2 ^ 32 := by
  have := h.1
  omega

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

/-- Calling convention of an indirect call site. Mirrors Rust
    `trust_ir::CallingConv` (crates/trust-ir/src/lib.rs; default `C`).
    Carried by `Inst.CallIndirect`. It is an ABI fact for the backend: the
    executable model, like the reference interpreter, resolves the callee by
    address and signature, and no convention changes a call's VALUE
    semantics. It is carried so the Lean instruction is not a lossy image of
    the Rust one (WS2.18 field-level parity). -/
inductive CallingConv where
  | C : CallingConv
  | Fast : CallingConv
  | Cold : CallingConv
  | Rust : CallingConv
  | Swift : CallingConv
  -- v45 (WS3.12): recorded ABI facts; `CUnwind` carries no unwind semantics
  -- under the ratified panic=abort policy.
  | CUnwind : CallingConv
  | SysV64 : CallingConv
  | Win64 : CallingConv
  | Aapcs : CallingConv
  | EfiApi : CallingConv
  | VectorCall : CallingConv
  | RustCold : CallingConv
  deriving Repr, DecidableEq, BEq

/-- Producer ABI claims. These records confer no proof authority. Natural
    number fields mirror bounded Rust integers; the JSON decoder checks their
    u8/u32/u64 bounds. Execution with typed ABI metadata is currently refused
    until the transport semantics checks all of these facts. -/
structure AbiTarget where
  triple : String
  dataLayout : String
  abi : String
  cpu : String
  features : List String
  targetSpec : String
  pointerBytes : Nat
  littleEndian : Bool
  deriving BEq, Repr

structure AbiFrontend where
  name : String
  revision : String
  deriving BEq, Repr

inductive AbiBindingPlace where
  | Parameter (index : Nat)
  | Result (index : Nat)
  | HiddenResult (index : Nat)
  deriving BEq, Repr

structure AbiBinding where
  place : AbiBindingPlace
  sourceOffset : Nat
  sourceBytes : Nat
  carrierOffset : Nat
  carrierBytes : Nat
  deriving BEq, Repr

inductive AbiExtension where
  | None | Sign | Zero
  deriving BEq, Repr

inductive AbiCapture where
  | Any | ReadOnly | Address | None
  deriving BEq, Repr

structure AbiAttributes where
  extension : AbiExtension
  inReg : Bool
  noAlias : Bool
  nonnull : Bool
  readonly : Bool
  noUndef : Bool
  writable : Bool
  noFree : Bool
  capture : AbiCapture
  pointeeSize : Nat
  pointeeAlign : Option Nat
  deriving BEq, Repr

inductive AbiRegisterClass where
  | Integer | Float | Vector
  deriving BEq, Repr

structure AbiRegister where
  regClass : AbiRegisterClass
  bytes : Nat
  deriving BEq, Repr

structure AbiScalar where
  register : AbiRegister
  sourceOffset : Nat
  sourceBytes : Nat
  valueBits : Nat
  attributes : AbiAttributes
  deriving BEq, Repr

structure AbiUniform where
  unit : AbiRegister
  total : Nat
  consecutive : Bool
  deriving BEq, Repr

inductive AbiPassMode where
  | Ignore
  | Direct (scalar : AbiScalar)
  | Pair (first second : AbiScalar)
  | Cast (padI32 : Bool) (prefixRegs : List AbiRegister) (restOffset : Option Nat)
      (rest : AbiUniform) (attributes : AbiAttributes)
  | Indirect (attributes : AbiAttributes) (metadataAttributes : Option AbiAttributes)
      (onStack callerCopy : Bool)
  deriving BEq, Repr

structure AbiArgument where
  size : Nat
  align : Nat
  mode : AbiPassMode
  bindings : List AbiBinding
  deriving BEq, Repr

structure SignatureAbi where
  target : AbiTarget
  frontend : AbiFrontend
  convention : String
  loweredConvention : CallingConv
  sourceAbi : String
  canUnwind : Bool
  variadic : Bool
  fixedCount : Nat
  arguments : List AbiArgument
  result : AbiArgument
  deriving BEq, Repr

/-- Function type definition. Mirrors Rust trust_ir::FuncTy. -/
structure FuncTyDef where
  params   : List Ty
  returns  : List Ty
  isVararg : Bool
  abi : Option SignatureAbi := none
  deriving BEq, Repr

/-- Original signature and calling convention, independent of whether a
    function has an executable body. No CFG or synthetic body is stored. -/
structure FunctionHeader where
  signature : FuncTyDef
  callingConv : CallingConv

/-- An original nominal item declaration, retaining its actual signature id.
    A duplicate source row cannot authenticate an item identity. -/
structure FunctionItemHeader where
  signatureId : FuncTyId
  header : FunctionHeader

/-- Struct field definition. Mirrors Rust trust_ir::FieldDef. -/
structure FieldDef where
  name   : String
  ty     : Ty
  offset : Option Nat
  deriving BEq, Repr

/-- Producer-declared struct representation. Packed alignment is a normative
    clamp on field alignment, not a request to synthesize a different image. -/
inductive StructRepr where
  | rust
  | c
  | transparent
  | packed (align : Nat)
  deriving BEq, Repr

/-- Struct type definition. Mirrors Rust trust_ir::StructDef's execution
    layout fields. The absent serde representation defaults to Rust. -/
structure StructDef where
  id     : StructId
  name   : String
  fields : List FieldDef
  size   : Option Nat
  align  : Option Nat
  repr   : StructRepr := .rust
  deriving Repr

/-- A v42 declared tuple image. The source type id resolves to the exact
    inline tuple; physical field order need not equal logical element order. -/
structure TupleLayoutDescriptor where
  tupleType : TyId
  size : Nat
  align : Nat
  fieldOffsets : List Nat
  deriving BEq, Repr

/-- Enum tag-representation hint. Mirrors Rust trust_ir::EnumTagRepr. -/
inductive EnumTagRepr where
  | u8 : EnumTagRepr
  | u16 : EnumTagRepr
  | u32 : EnumTagRepr
  | u64 : EnumTagRepr
  | i8 : EnumTagRepr
  | i16 : EnumTagRepr
  | i32 : EnumTagRepr
  | i64 : EnumTagRepr
  -- v45 (WS3.14(b)): the 128-bit tag lanes. `u128` spells only the
  -- non-negative half, since a discriminant is an i128. One constructor per
  -- line, because the Rust<->Lean parity gate reads them line by line.
  | u128 : EnumTagRepr
  | i128 : EnumTagRepr
  deriving BEq, Repr

/-- Physical storage of an impossible source field; this is not its value layout. -/
structure FieldStorageLayout where
  size : Nat
  align : Nat
  deriving BEq, Repr

/-- Full physical extent of a proved-dead variant, in source-field order.
    Offsets remain solely in `EnumLayoutDescriptor.variantFieldOffsets`. -/
structure UninhabitedVariantLayout where
  variant : Nat
  size : Nat
  align : Nat
  fields : List FieldStorageLayout
  deriving BEq, Repr

/-- How an enum's discriminant is represented in memory. Mirrors Rust
    trust_ir::EnumTagEncoding (wire v31; `untagged` in v37,
    `singleInhabited` in v65, `directWithUninhabited` in v67). -/
inductive EnumTagEncoding where
  | direct (tagOffset : Nat)
  | niche (untaggedVariant nicheVariantsStart nicheVariantsEnd : Nat)
      (nicheStart : Nat) (nicheOffset : Nat) (nicheTy : EnumTagRepr)
  /-- No stored tag: the image is the sole variant's payload alone. Well-formed
      only for a one-variant enum, since nothing in the image discriminates. -/
  | untagged
  /-- No stored tag, retaining every logical variant. Only the selected variant
      is inhabited; all others require a finite structural uninhabitedness fact. -/
  | singleInhabited (variant : Nat) : EnumTagEncoding
  /-- A real tag and checked physical extents for the proved-dead declarations.
      These source fields retain their identity without acquiring value codecs. -/
  | directWithUninhabited (tagOffset : Nat) (variants : List UninhabitedVariantLayout)
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

/-- A single typed slot in a binding frame. Mirrors Rust
    trust_ir::inst::BindingSlot from crates/trust_ir/src/inst.rs.

    Each slot has a name (diagnostics / text format) and a declared Ty.
    The position in BindingFrameDef.slots is the slot index used by
    Inst.BindSlot and Inst.LoadSlot. -/
structure BindingSlot where
  name : String
  ty   : Ty
  deriving Repr

/-- Declaration of a binding frame's slot layout. Inline in
    Inst.OpenFrame, matching Rust trust_ir::inst::BindingFrameDef
    (crates/trust_ir/src/inst.rs).

    The id is unique within a function. Source-bound execution retains the
    entire declaration and rejects absent, ambiguous or changed originals. -/
structure BindingFrameDef where
  id    : BindingFrameId
  name  : String
  slots : List BindingSlot
  deriving Repr

namespace BindingFrameDef

/-- Number of declared slots. -/
def slotCount (d : BindingFrameDef) : Nat := d.slots.length

end BindingFrameDef

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

/-- info: 'TrustIr.Ty.isBool_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.Ty.isBool_iff
