-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Cast semantics: Trunc, ZExt, SExt, float casts.
-- Phase 1 of the formalization roadmap.

import TrustIr.CastOp
import TrustIr.Semantics.Arith

namespace TrustIr

/-!
# Cast Semantics

## Integer-to-integer casts
- Trunc: truncate to narrower type (drop high bits)
- ZExt: zero-extend to wider type (pad with zeros)
- SExt: sign-extend to wider type (replicate sign bit)

## Float casts
FPTrunc/FPExt/UIToFP/SIToFP are axiomatized via Lean's Float conversions.
The float→int casts — both the raw FPToSI/FPToUI in-range paths and the
SATURATING twins (FPToSISat / FPToUISat) — are exact, not axiomatized:
truncation-toward-zero is computed from the frExp mantissa decomposition
(see `floatTruncNat`). The raw/saturating pairs differ ONLY in their UB
envelope (raw: NaN/out-of-range is UB; saturating: total on floats).

## Pointer casts
- PtrToInt: pointer to integer (returns the address)
- IntToPtr: integer to pointer (creates a pointer)
- Bitcast: reinterpret bits (same bit width required)
-/

/-- Get the bit width of a type, or throw a type error. -/
def getTyWidth (ty : Ty) : Except SemError Nat :=
  match ty.bitWidth with
  | some w => .ok w
  | none   => .error (.typeError s!"type {repr ty} has no bit width")

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
def semCast (op : CastOp) (_srcTy dstTy : Ty) (operandId : ValueId) : Sem ValueId := do
  let operand ← Sem.lookupValue operandId
  -- A cast inspects (reinterprets) the operand's content: poison is UB.
  Sem.rejectPartial operand "Cast"
  match op with
  | .Trunc =>
    match operand with
    | .int _ v =>
      if dstTy == .Bool then
        Sem.bindFresh (.bool (truncateUnsigned v 1 == 1))
      else
        match getTyWidth dstTy with
        | .ok dstW => Sem.bindFresh (.int dstW (truncateUnsigned v dstW))
        | .error e => throw e
    | _ => Sem.throwTypeError "Trunc: non-integer operand"

  | .ZExt =>
    match operand with
    | .int _ v =>
      match getTyWidth dstTy with
      | .ok dstW =>
        -- Zero extension: value is already non-negative in unsigned representation
        Sem.bindFresh (.int dstW (truncateUnsigned v dstW))
      | .error e => throw e
    | .bool b =>
      match getTyWidth dstTy with
      | .ok dstW => Sem.bindFresh (.int dstW (if b then 1 else 0))
      | .error e => throw e
    | _ => Sem.throwTypeError "ZExt: non-integer operand"

  | .SExt =>
    match operand with
    | .int srcW v =>
      match getTyWidth dstTy with
      | .ok dstW =>
        -- Sign extension: interpret as signed, then re-encode in wider width
        let signed := toSigned v srcW
        let modulus := (2 : Int) ^ dstW
        let wrapped := ((signed % modulus) + modulus) % modulus
        Sem.bindFresh (.int dstW wrapped)
      | .error e => throw e
    | .bool b =>
      match getTyWidth dstTy with
      | .ok dstW =>
        let signed : Int := if b then -1 else 0
        let modulus := (2 : Int) ^ dstW
        let wrapped := ((signed % modulus) + modulus) % modulus
        Sem.bindFresh (.int dstW wrapped)
      | .error e => throw e
    | _ => Sem.throwTypeError "SExt: non-integer operand"

  -- Float casts: axiomatized via Lean's Float
  | .FPTrunc =>
    match operand with
    | .float v => Sem.bindFresh (.float v)  -- Lean Float is always f64; axiomatized
    | _ => Sem.throwTypeError "FPTrunc: non-float operand"

  | .FPExt =>
    match operand with
    | .float v => Sem.bindFresh (.float v)  -- axiomatized
    | _ => Sem.throwTypeError "FPExt: non-float operand"

  | .FPToUI =>
    match operand with
    | .float v =>
      match getTyWidth dstTy with
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
      match getTyWidth dstTy with
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
      match getTyWidth dstTy with
      | .ok dstW => Sem.bindFresh (.int dstW (fpToSISatRaw dstW v))
      | .error e => throw e
    | _ => Sem.throwTypeError "FPToSISat: non-float operand"

  | .FPToUISat =>
    match operand with
    | .float v =>
      match getTyWidth dstTy with
      | .ok dstW => Sem.bindFresh (.int dstW (fpToUISatRaw dstW v))
      | .error e => throw e
    | _ => Sem.throwTypeError "FPToUISat: non-float operand"

  | .UIToFP =>
    match operand with
    | .int _ v => Sem.bindFresh (.float (Float.ofNat v.toNat))
    | _ => Sem.throwTypeError "UIToFP: non-integer operand"

  | .SIToFP =>
    match operand with
    | .int w v =>
      let signed := toSigned v w
      Sem.bindFresh (.float (Float.ofInt signed))
    | _ => Sem.throwTypeError "SIToFP: non-integer operand"

  | .PtrToInt =>
    match operand with
    | .ptr addr =>
      match getTyWidth dstTy with
      | .ok dstW => Sem.bindFresh (.int dstW (Int.ofNat addr))
      | .error e => throw e
    | _ => Sem.throwTypeError "PtrToInt: non-pointer operand"

  | .IntToPtr =>
    match operand with
    | .int _ v => Sem.bindFresh (.ptr v.toNat)
    | _ => Sem.throwTypeError "IntToPtr: non-integer operand"

  | .Bitcast =>
    -- Bitcast: reinterpret bits. In our model, just re-tag the value.
    -- Requires same bit width (checked by validator, not enforced here).
    match operand with
    | .int _ v =>
      if dstTy == .Ptr then Sem.bindFresh (.ptr v.toNat)
      else match getTyWidth dstTy with
        | .ok dstW => Sem.bindFresh (.int dstW v)
        | .error e => throw e
    | .ptr addr =>
      match getTyWidth dstTy with
      | .ok dstW => Sem.bindFresh (.int dstW (Int.ofNat addr))
      | .error e => throw e
    | _ => Sem.throwTypeError "Bitcast: unsupported operand type"

  | .PtrToPtr =>
    -- Pointer-to-pointer cast: the address is unchanged (provenance retag).
    match operand with
    | .ptr addr => Sem.bindFresh (.ptr addr)
    | _ => Sem.throwTypeError "PtrToPtr: non-pointer operand"

  | .Transmute =>
    -- Transmute: same-size byte reinterpret (Rust core::mem::transmute).
    -- Validated identically to Bitcast on the Rust side
    -- (crates/trust-ir/src/shape.rs:842 routes Bitcast | Transmute through
    -- one branch requiring src.size_bits == dst.size_bits). The Lean Value
    -- model has no byte buffer / encode-decode, so this is a SCALAR-ONLY
    -- PARTIAL model: it reinterprets scalar int<->int and int<->ptr exactly
    -- like Bitcast, and rejects every value shape the model cannot
    -- byte-reinterpret (float, bool, aggregate, vector, set/sequence/
    -- record/closure, frame, undef, nullPtr). This mirrors the Rust
    -- reference interpreter, which itself returns UnsupportedCast for
    -- Transmute (crates/trust-ir/src/interpret.rs:2115-2121). NOT faked:
    -- the rejected cases error, they do not silently succeed.
    match operand with
    | .int _ v =>
      if dstTy == .Ptr then Sem.bindFresh (.ptr v.toNat)
      else match getTyWidth dstTy with
        | .ok dstW => Sem.bindFresh (.int dstW v)
        | .error e => throw e
    | .ptr addr =>
      match getTyWidth dstTy with
      | .ok dstW => Sem.bindFresh (.int dstW (Int.ofNat addr))
      | .error e => throw e
    | _ =>
      Sem.throwUnsupported .vectorShape
        "Transmute: non-scalar/byte-level reinterpret outside the executable subset"

  | .ReifyFnPointer =>
    -- ReifyFnPointer: function item (Ty::Func) -> thin function pointer.
    -- On the Rust side the source MUST be Ty::Func(_)
    -- (crates/trust-ir/src/shape.rs:857-872, NotFunctionPointerSource). In
    -- the Lean Value model a function item is a bare closure:
    -- Value.closure fn [] (zero captures; cf. ClosureTy.bare,
    -- TrustIr/Basic.lean, and closureFunc/closureCaptures in
    -- TrustIr/Semantics/Aggregate.lean).
    --
    -- PARTIAL: producing a Call-resolvable pointer address requires
    -- registering fn -> addr in state (the FuncPtrTable consumed by
    -- semCallIndirect), which semCast has no access to (its signature is
    -- op/srcTy/dstTy/operandId only). We preserve the fn-item value
    -- unchanged: the result is still Value.closure fn caps, carrying the
    -- FuncId so a later pass with FuncPtrTable access can finish the
    -- reification. Every non-fn-item operand is rejected, mirroring the
    -- Rust NotFunctionPointerSource check. Faithful and total, not faked.
    match operand with
    | .closure fn caps => Sem.bindFresh (.closure fn caps)
    | _ => Sem.throwTypeError "ReifyFnPointer: source is not a function item"

end TrustIr
