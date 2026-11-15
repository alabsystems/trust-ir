-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Cast semantics: Trunc, ZExt, SExt, float casts.
-- Phase 1 of the formalization roadmap.

import TrustIr.CastOp
import TrustIr.Semantics.Arith
import TrustIr.Semantics.TypedInteger

namespace TrustIr

/-!
# Cast Semantics

## Integer-to-integer casts
- Trunc: truncate to narrower type (drop high bits)
- ZExt: zero-extend to wider type (pad with zeros)
- SExt: sign-extend to wider type (replicate sign bit)

## Float casts
FPTrunc/FPExt/UIToFP/SIToFP are width-exact: the operand must inhabit the
source float type (`checkFloatAt`) and the result is rounded to the
destination float type exactly once (`roundFloatAt` / `roundIntToFloatAt`,
`Semantics/FloatFormat.lean`); a width the model does not round refuses with
`unsupported.float` rather than answering at binary64.
The float→int casts — both the raw FPToSI/FPToUI in-range paths and the
SATURATING twins (FPToSISat / FPToUISat) — are exact, not axiomatized:
truncation-toward-zero is computed from the frExp mantissa decomposition
(see `floatTruncNat`). The raw/saturating pairs differ ONLY in their UB
envelope (raw: NaN/out-of-range is UB; saturating: total on floats).

## Pointer casts
- PtrToInt: observe a physical target address, then reduce it to the integer
  destination width. It drops provenance; the null pointer is address 0.
- IntToPtr: integer to pointer. The integer becomes an address as the
  interpreter makes one (`Sem.addrOfInt`: the unsigned value at the source
  width, UB at or above 2^64), and the address recovers provenance by the
  one rule (`Memory.resolveAddr`: containment, then one past the end,
  oldest first; zero is null). The same conversion and recovery serve an
  int → pointer `Bitcast` and an int → `Ptr` `Transmute`.
- Bitcast: reinterpret bits (same bit width required); a pointer → pointer
  bitcast keeps the pointer, provenance included
-/

/-- The width of an address in bits: 64 (`u64`, the interpreter's address
    type).

    A named constant, not a literal, so that `2 ^ Sem.addrBits` stays a
    computation in compiled code. Written `2 ^ 64`, the compiler folds the bound
    into a closed term holding the bignum 18446744073709551616, and Lean 4.8.0's
    object compactor writes a bignum into the .olean with its uninitialised
    struct padding (the non-GMP `mpz`: `bool m_sign`, seven padding bytes,
    `size_t m_size`), so this module's .olean differed on every build of the same
    source. Trust vendors `Cast.olean` by digest (its Lean-Clean bridge closure).
    `@[noinline]` keeps the compiler from folding it back. -/
@[noinline] def Sem.addrBits : Nat := 64

/-- An INTEGER as an ADDRESS: the unsigned value of `v` at its source width
    `w`, refused as undefined behaviour at or above 2^64. The interpreter's
    `int.as_unsigned()` then `u64::try_from` (interpret.rs, `IntToPtr` and the
    int → pointer arm of `eval_bitcast`), so a negative signed integer is a
    large address, never the null pointer. -/
def Sem.addrOfInt (op : String) (w : Nat) (v : Int) (model : ByteModel := .le64) : Sem Nat :=
  let u := (v % (2 ^ w)).toNat
  if u < 2 ^ Sem.addrBits then
    match model with
    | .le64 => pure u
    | .le32 =>
      if u < model.addressLimit then pure u
      else Sem.throwUB s!"{op}: address is outside the target address space"
  else Sem.throwUB s!"{op}: address {u} does not fit u64"

/-- The scalar types the executable `Transmute` model reinterprets between:
    `I8`–`I128` / `U8`–`U128` / `Ptr` (lowering-target subset v3, structural
    condition 1). Mirrors `transmute_scalar_ty` (`crates/trust-ir/src/bridge.rs`)
    and `is_transmute_scalar` (`crates/trust-ir-conformance/src/subset.rs`);
    the reference interpreter executes `Transmute` on exactly this set and
    answers `UnsupportedCast` outside it.

    `F32` / `F64` / `Bool` are deliberately ABSENT on BOTH sides (subset v3
    soundness erratum, WS2.9): the model has no byte buffer, so it can neither
    read a float's bits nor re-establish a `Bool`'s 0/1 invariant. Reinterpret
    an int as a float with `Bitcast`, which goes through `floatFromBitsAt`.
    Pointer-width ints and `Char` are absent because their executable
    semantics are the still-open B1 depth-ledger entry. -/
def transmuteScalarTy : Ty → _root_.Bool
  | .I8 | .I16 | .I32 | .I64 | .I128
  | .U8 | .U16 | .U32 | .U64 | .U128
  | .Ptr => true
  | _ => false

/-- Get the bit width of a type, or throw a type error. -/
def getTyWidth (ty : Ty) (model : ByteModel := .le64) : Except SemError Nat :=
  match ty.bitWidthFor model with
  | some w => .ok w
  | none   => .error (.typeError s!"type {repr ty} has no bit width")

/-- Resolving an allocation-derived pointer checks its target address bound
    before narrowing to the destination integer. -/
def Sem.bindPointerInteger (op : String) (dstTy : Ty) (address : Nat)
    (model : ByteModel) : Sem ValueId := do
  let width ← match getTyWidth dstTy model with
    | .ok width => pure width
    | .error error => throw error
  if address < model.addressLimit then
    Sem.bindFresh (Value.intAt width (Int.ofNat address))
  else Sem.throwUB s!"{op}: pointer address exceeds the target width"

/-- Rust exposes a no-provenance pointer's raw u64 address directly. Its
    integer destination still has the actual target's width (including Usize).
    Allocation-derived pointers retain the target address check. Store, ICmp
    and GEP have their own stricter address checks even without provenance. -/
def Sem.bindPointerIntegerWithProvenance (op : String) (dstTy : Ty) (address : Nat)
    (provenance : Option AllocId) (model : ByteModel) : Sem ValueId :=
  match provenance with
  | none => do
    let width ← match getTyWidth dstTy model with
      | .ok width => pure width
      | .error error => throw error
    if address < word64Limit then
      Sem.bindFresh (Value.intAt width (Int.ofNat address))
    else Sem.throwUB s!"{op}: pointer address exceeds the u64 carrier"
  | some _ => Sem.bindPointerInteger op dstTy address model

/-- Exact truncation-toward-zero of a positive finite `Float`, as a `Nat`.

    Every finite double is exactly `m * 2^(e - 53)` with `m < 2^53` under the
    `frExp` normalization (the `floatExactString` idiom in
    `Semantics/ExecutableFixtures.lean`), so the truncated integer is a pure
    `Nat` shift — exact at EVERY destination width including 128 bits, with
    no width-limited `toUInt64` round trip on the value itself. NaN,
    infinities, and non-positive inputs return 0 (callers guard them; the
    guard here keeps the function deterministic and total). -/
def floatTruncNat (v : Float) : Nat :=
  if v.isNaN || v.isInf || v ≤ 0.0 then 0
  else
    let (frac, e) := v.frExp
    let m := (frac.scaleB 53).toUInt64.toNat
    if e ≥ 53 then m <<< (e - 53).toNat else m >>> (53 - e).toNat

/-- Exact truncation-toward-zero of a finite `Float`, as an `Int`. -/
def floatTruncInt (v : Float) : Int :=
  if v < 0.0 then -(Int.ofNat (floatTruncNat (-v))) else Int.ofNat (floatTruncNat v)

/-- Saturating float→signed-int conversion at width `w`, as the value model's
    canonical unsigned (two's-complement) encoding. Mirrors the reference
    interpreter EXACTLY (interpret.rs `CastOp::FPToSISat`; Rust `f as iN`,
    LLVM `fptosi.sat`; docs/ub-numerics-policy.md §2): NaN → 0;
    `v ≥ 2^(w-1)` saturates to `iN::MAX` (raw `2^(w-1) - 1`); `v < -2^(w-1)`
    saturates to `iN::MIN` (raw `2^(w-1)`; note `-2^(w-1)` itself IS
    representable, so equality truncates in-range); in-range values truncate
    toward zero. The `±2^(w-1)` bounds are powers of two, hence exact as
    `Float`s at every width. -/
def fpToSISatRaw (w : Nat) (v : Float) : Int :=
  let half := (2 : Int) ^ (w - 1)
  if v.isNaN then 0
  else if v ≥ Float.ofInt half then half - 1
  else if v < Float.ofInt (-half) then half
  else ((floatTruncInt v % (2 : Int) ^ w) + (2 : Int) ^ w) % (2 : Int) ^ w

/-- Saturating float→unsigned-int conversion at width `w`. Mirrors the
    reference interpreter EXACTLY (interpret.rs `CastOp::FPToUISat`; Rust
    `f as uN`, LLVM `fptoui.sat`; docs/ub-numerics-policy.md §2): NaN → 0;
    `v ≥ 2^w` saturates to `uN::MAX` (`2^w - 1`); every negative (including
    `-inf`) saturates to 0; in-range values truncate toward zero (`-0.0` is
    in range and truncates to 0). -/
def fpToUISatRaw (w : Nat) (v : Float) : Int :=
  let limit := (2 : Int) ^ w
  if v.isNaN then 0
  else if v ≥ Float.ofInt limit then limit - 1
  else if v < 0.0 then 0
  else Int.ofNat (floatTruncNat v)

/-- Evaluate a cast operation in the semantic monad.
    Matches all 17 Rust `trust_ir::CastOp` variants. -/
def semCast (op : CastOp) (srcTy dstTy : Ty) (operandId : ValueId) (model : ByteModel := .le64) : Sem ValueId := do
  let operand ← Sem.lookupValue operandId
  -- A cast inspects (reinterprets) the operand's content: poison is UB.
  Sem.rejectPartial operand "Cast"
  match op with
  | .Trunc =>
    match operand with
    | .int _ v =>
      if dstTy.isBool then
        Sem.bindFresh (.bool (truncateUnsigned v 1 == 1))
      else
        match getTyWidth dstTy model with
        | .ok dstW => Sem.bindFresh (.int dstW (truncateUnsigned v dstW))
        | .error e => throw e
    | _ => Sem.throwTypeError "Trunc: non-integer operand"

  | .ZExt =>
    match operand with
    | .int _ v =>
      match getTyWidth dstTy model with
      | .ok dstW =>
        -- Zero extension: value is already non-negative in unsigned representation
        Sem.bindFresh (.int dstW (truncateUnsigned v dstW))
      | .error e => throw e
    | .bool b =>
      match getTyWidth dstTy model with
      | .ok dstW => Sem.bindFresh (.int dstW (if b then 1 else 0))
      | .error e => throw e
    | _ => Sem.throwTypeError "ZExt: non-integer operand"

  | .SExt =>
    match operand with
    | .int srcW v =>
      match getTyWidth dstTy model with
      | .ok dstW =>
        -- Sign extension: interpret as signed, then re-encode in wider width
        let signed := toSigned v srcW
        let modulus := (2 : Int) ^ dstW
        let wrapped := ((signed % modulus) + modulus) % modulus
        Sem.bindFresh (.int dstW wrapped)
      | .error e => throw e
    | .bool b =>
      match getTyWidth dstTy model with
      | .ok dstW =>
        let signed : Int := if b then -1 else 0
        let modulus := (2 : Int) ^ dstW
        let wrapped := ((signed % modulus) + modulus) % modulus
        Sem.bindFresh (.int dstW wrapped)
      | .error e => throw e
    | _ => Sem.throwTypeError "SExt: non-integer operand"

  -- Float-to-float casts: the operand must inhabit the source width and the
  -- result is rounded to the destination width exactly once. `FPExt` is exact
  -- (every narrower value is a wider one), `FPTrunc` rounds (RNE).
  | .FPTrunc =>
    match operand with
    | .float v =>
      match checkFloatAt srcTy v, roundFloatAt dstTy v with
      | .ok (), .ok r => Sem.bindFresh (.float r)
      | .error e, _ => throw e
      | _, .error e => throw e
    | _ => Sem.throwTypeError "FPTrunc: non-float operand"

  | .FPExt =>
    match operand with
    | .float v =>
      match checkFloatAt srcTy v, roundFloatAt dstTy v with
      | .ok (), .ok r => Sem.bindFresh (.float r)
      | .error e, _ => throw e
      | _, .error e => throw e
    | _ => Sem.throwTypeError "FPExt: non-float operand"

  | .FPToUI =>
    match operand with
    | .float v =>
      match checkFloatAt srcTy v with
      | .error e => throw e
      | .ok () =>
      match getTyWidth dstTy model with
      | .ok dstW =>
        -- NaN or out-of-range float-to-unsigned is UNDEFINED (matches Rust
        -- `eval_cast` and docs/ub-numerics-policy.md §2). Bounds mirror the Rust
        -- reference interpreter exactly (lo = 0, hi = 2^dstW) so the two engines
        -- agree; LLVM `fptoui` rounds toward zero, defined on [0, 2^dstW).
        -- In-range values (including -0.0, which is NOT < 0.0) truncate toward
        -- zero via the exact frExp path (interpret.rs `float_to_u128`
        -- `.trunc()`), exact at every width — no axiomatized toUInt64.
        if v.isNaN || v < 0.0 || v ≥ Float.ofInt ((2 : Int) ^ dstW) then
          Sem.throwUB "FPToUI: NaN or out-of-range float-to-unsigned conversion"
        else
          Sem.bindFresh (.int dstW (Int.ofNat (floatTruncNat v)))
      | .error e => throw e
    | _ => Sem.throwTypeError "FPToUI: non-float operand"

  | .FPToSI =>
    match operand with
    | .float v =>
      match checkFloatAt srcTy v with
      | .error e => throw e
      | .ok () =>
      match getTyWidth dstTy model with
      | .ok dstW =>
        -- NaN or out-of-range float-to-signed is UNDEFINED (matches Rust
        -- `eval_cast` and docs/ub-numerics-policy.md §2). Bounds mirror the Rust
        -- reference interpreter exactly (lo = -2^(dstW-1), hi = 2^(dstW-1));
        -- v = -2^(dstW-1) itself IS representable, hence in-range.
        -- In-range values truncate toward zero via the exact frExp path and
        -- re-encode as the canonical unsigned (two's-complement) raw, exactly
        -- as the interpreter's `float_to_i128 as u128` + width mask
        -- (interpret.rs) — negative in-range inputs wrap, e.g. -5.0 as i32
        -- is raw 4294967291, not 0.
        if v.isNaN || v < Float.ofInt (-(2 : Int) ^ (dstW - 1))
            || v ≥ Float.ofInt ((2 : Int) ^ (dstW - 1)) then
          Sem.throwUB "FPToSI: NaN or out-of-range float-to-signed conversion"
        else
          Sem.bindFresh (.int dstW
            (((floatTruncInt v % (2 : Int) ^ dstW) + (2 : Int) ^ dstW)
              % (2 : Int) ^ dstW))
      | .error e => throw e
    | _ => Sem.throwTypeError "FPToSI: non-float operand"

  -- Saturating float→int twins (Rust `f as iN`/`uN`, LLVM fptosi.sat /
  -- fptoui.sat). Unlike the raw FPToUI/FPToSI above (NaN/out-of-range = UB),
  -- these are TOTAL on floats: NaN → 0, out-of-range clamps to MIN/MAX,
  -- in-range truncates toward zero — the exact interpreter mirror
  -- (interpret.rs `CastOp::FPToUISat | CastOp::FPToSISat`), with the
  -- truncation computed exactly via the frExp mantissa decomposition
  -- (fpToSISatRaw / fpToUISatRaw above), the same exact path the raw
  -- casts' in-range conversion uses.
  | .FPToSISat =>
    match operand with
    | .float v =>
      match checkFloatAt srcTy v with
      | .error e => throw e
      | .ok () =>
      match getTyWidth dstTy model with
      | .ok dstW => Sem.bindFresh (.int dstW (fpToSISatRaw dstW v))
      | .error e => throw e
    | _ => Sem.throwTypeError "FPToSISat: non-float operand"

  | .FPToUISat =>
    match operand with
    | .float v =>
      match checkFloatAt srcTy v with
      | .error e => throw e
      | .ok () =>
      match getTyWidth dstTy model with
      | .ok dstW => Sem.bindFresh (.int dstW (fpToUISatRaw dstW v))
      | .error e => throw e
    | _ => Sem.throwTypeError "FPToUISat: non-float operand"

  -- Int-to-float casts round the EXACT integer to the destination width once
  -- (`roundIntToFloatAt`), never through a wider float intermediate.
  | .UIToFP =>
    match operand with
    | .int _ v =>
      match roundIntToFloatAt dstTy (Int.ofNat v.toNat) with
      | .ok r => Sem.bindFresh (.float r)
      | .error e => throw e
    | _ => Sem.throwTypeError "UIToFP: non-integer operand"

  | .SIToFP =>
    match operand with
    | .int w v =>
      match roundIntToFloatAt dstTy (toSigned v w) with
      | .ok r => Sem.bindFresh (.float r)
      | .error e => throw e
    | _ => Sem.throwTypeError "SIToFP: non-integer operand"

  | .PtrToInt =>
    match operand with
    | .ptr addr prov => Sem.bindPointerIntegerWithProvenance "PtrToInt" dstTy addr prov model
    | .nullPtr => Sem.bindPointerInteger "PtrToInt" dstTy 0 model
    | _ => Sem.throwTypeError "PtrToInt: non-pointer operand"

  | .IntToPtr =>
    match operand with
    | .int w v => do
      -- An integer address recovers the provenance it names in THIS layout
      -- (the interpreter's `resolve_pointer_kind`); zero is null.
      let a ← Sem.addrOfInt "IntToPtr" w v model
      let s ← Sem.getState
      Sem.bindFresh (s.memory.resolveAddr a)
    | _ => Sem.throwTypeError "IntToPtr: non-integer operand"

  | .Bitcast =>
    -- Bitcast: reinterpret bits. In our model, just re-tag the value.
    -- Requires same bit width (checked by validator, not enforced here).
    -- A float on either side reinterprets through the IEEE bit pattern
    -- (`floatFromBitsAt` / `floatToBitsAt`, `Semantics/FloatFormat.lean`),
    -- never by re-tagging: an int re-tagged as `F32` would be an int-shaped
    -- value of float type. Reading a NaN's bits refuses (payload unobservable).
    if srcTy.isFloat && dstTy.isPointerLike then
      Sem.throwTypeError "Bitcast: float bits cannot form a pointer"
    else if srcTy.isFloat || dstTy.isFloat then
      match operand with
      | .int _ v =>
        match floatFromBitsAt dstTy v with
        | .ok f => Sem.bindFresh (.float f)
        | .error e => throw e
      | .float f =>
        match floatToBitsAt srcTy f with
        | .error e => throw e
        | .ok bits =>
          if dstTy.isFloat then
            match floatFromBitsAt dstTy (Int.ofNat bits) with
            | .ok g => Sem.bindFresh (.float g)
            | .error e => throw e
          else
            match getTyWidth dstTy model with
            | .ok dstW => Sem.bindFresh (.int dstW (Int.ofNat bits))
            | .error e => throw e
      | _ => Sem.throwTypeError "Bitcast: float bitcast of a non-scalar operand"
    else
    -- A pointer-like destination (`Ptr`, `PtrConst`, `PtrMut`, `Ref`,
    -- `RefMut`, `Rc` — `Ty.isPointerLike`, the same set as the reference
    -- interpreter's `is_pointer_like_ty`) binds a POINTER value (WS2.9
    -- review). Before it only `.Ptr` was recognised on the `.int` side and
    -- NO pointer type on the `.ptr` side: `Bitcast ptr -> ptr` re-tagged the
    -- operand as `.int 64 addr` — an integer-shaped value at a pointer type
    -- — and `Bitcast u64 -> *const u8` bound `.int 64 v`, while
    -- `eval_bitcast` transports / re-resolves the pointer for every
    -- pointer-like destination.
    match operand with
    | .int w v =>
      if dstTy.isPointerLike then do
        let a ← Sem.addrOfInt "Bitcast" w v model
        let s ← Sem.getState
        Sem.bindFresh (s.memory.resolveAddr a)
      else match getTyWidth dstTy model with
        | .ok dstW => Sem.bindFresh (.int dstW v)
        | .error e => throw e
    | .ptr addr prov =>
      if dstTy.isPointerLike then Sem.bindFresh (.ptr addr prov)
      else Sem.bindPointerIntegerWithProvenance "Bitcast" dstTy addr prov model
    -- The null pointer is address 0 (`eval_bitcast`: `NullPtr` is raw 0, and
    -- stays `NullPtr` at a pointer-like destination).
    | .nullPtr =>
      if dstTy.isPointerLike then Sem.bindFresh .nullPtr
      else Sem.bindPointerInteger "Bitcast" dstTy 0 model
    | _ => Sem.throwTypeError "Bitcast: unsupported operand type"

  | .PtrToPtr =>
    -- Pointer-to-pointer cast: the address AND its provenance are unchanged;
    -- the null pointer stays null.
    match operand with
    | .ptr addr prov => Sem.bindFresh (.ptr addr prov)
    | .nullPtr => Sem.bindFresh .nullPtr
    | _ => Sem.throwTypeError "PtrToPtr: non-pointer operand"

  | .Transmute =>
    -- Transmute: same-size byte reinterpret (Rust core::mem::transmute).
    -- Validated identically to Bitcast on the Rust side
    -- (crates/trust-ir/src/shape.rs routes Bitcast | Transmute through one
    -- branch requiring src.size_bits == dst.size_bits). The Lean Value model
    -- has no byte buffer / encode-decode, so this is a SCALAR-ONLY PARTIAL
    -- model: it reinterprets scalar int<->int, int<->ptr and ptr<->ptr
    -- exactly like Bitcast, and rejects every shape the model cannot
    -- byte-reinterpret. NOT faked: the rejected cases error, they do not
    -- silently succeed.
    --
    -- The gate is TWO-SIDED (lowering-target subset v3, WS2.9). The operand
    -- match below already refuses a float or bool SOURCE, because `.float`
    -- and `.bool` are their own Value constructors. The DESTINATION had no
    -- gate at all beyond `getTyWidth`, which MISTRANSLATED: `transmute
    -- u32 -> f32` bound `.int 32 v` — an integer value at a float type — and
    -- `transmute u8 -> bool` bound `.int 1 v` with `v` possibly greater
    -- than 1. `transmuteScalarTy` now narrows both sides to the same set the
    -- Rust classifier pins (`transmute_scalar_ty`, bridge.rs; the reference
    -- interpreter answers `UnsupportedCast` on exactly this complement).
    -- The sanctioned replacement for an int<->float reinterpret is Bitcast,
    -- which goes through the IEEE bit pattern above.
    -- One refusal, `unsupported.cast`, on either side: the reference
    -- interpreter answers a single `UnsupportedCast` for every off-set
    -- shape, float destinations included (its scalar-set check runs before
    -- any float rule), so the model must not split the code by side or by
    -- float-ness.
    if !transmuteScalarTy dstTy then
      Sem.throwUnsupported .cast
        "Transmute: destination outside the executable scalar set (I8-I128 / U8-U128 / Ptr; int<->float is Bitcast)"
    else if !transmuteScalarTy srcTy then
      Sem.throwUnsupported .cast
        "Transmute: source outside the executable scalar set (I8-I128 / U8-U128 / Ptr; int<->float is Bitcast)"
    else
      match operand with
      | .int w v =>
        if dstTy == .Ptr then do
          let a ← Sem.addrOfInt "Transmute" w v model
          let s ← Sem.getState
          Sem.bindFresh (s.memory.resolveAddr a)
        else match getTyWidth dstTy model with
          | .ok dstW => Sem.bindFresh (.int dstW v)
          | .error e => throw e
      | .ptr addr prov =>
        -- A `Ptr` destination stays a POINTER value: re-tagging it as an
        -- integer here would make `transmute *const u8 -> *const i8` disagree
        -- with the reference interpreter, which transports the pointer.
        if dstTy == .Ptr then Sem.bindFresh (.ptr addr prov)
        else Sem.bindPointerIntegerWithProvenance "Transmute" dstTy addr prov model
      | .nullPtr =>
        if dstTy == .Ptr then Sem.bindFresh .nullPtr
        else Sem.bindPointerInteger "Transmute" dstTy 0 model
      | _ =>
        Sem.throwUnsupported .vectorShape
          "Transmute: non-scalar/byte-level reinterpret outside the executable subset"

  | .ReifyFnPointer =>
    -- A typed function identity is not a native code address. The model has
    -- no linker/address-allocation relation with which to reify one.
    -- The legacy untyped closure arm preserves constant metadata only; that
    -- value is not an admissible contextual CallIndirect callee and grants
    -- no typed function or native-address transport authority.
    match operand with
    | .fnDef _ _ =>
      Sem.throwUnsupported .cast
        "ReifyFnPointer: native code address representation is not modeled"
    | .closure fn caps => Sem.bindFresh (.closure fn caps)
    | _ => Sem.throwTypeError "ReifyFnPointer: source is not a function item"

end TrustIr
