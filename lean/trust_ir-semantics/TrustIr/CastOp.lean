-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Cast operation enum.
-- Mirrors: crates/trust_ir/src/inst.rs (CastOp)

namespace TrustIr

/-!
# Cast Operations

Mirrors Rust `trust_ir::CastOp` (17 variants).
All type conversions in TrustIr are explicit.

## Integer-to-integer
- Trunc: truncate to narrower type (drop high bits); Bool is a one-bit target
- ZExt: zero-extend to wider type; Bool is a one-bit source (false=0, true=1)
- SExt: sign-extend to wider type; Bool true sign-extends to all one bits

## Float-to-float
- FPTrunc: truncate float precision (e.g., f64 -> f32)
- FPExt: extend float precision (e.g., f32 -> f64)

## Int-float conversions
- FPToUI: float to unsigned integer (raw — NaN/out-of-range is UB)
- FPToSI: float to signed integer (raw — NaN/out-of-range is UB)
- UIToFP: unsigned integer to float
- SIToFP: signed integer to float
- FPToSISat: SATURATING float to signed integer (Rust `f as iN`, LLVM
  fptosi.sat): NaN → 0, out-of-range clamps to `iN::MIN`/`iN::MAX`,
  in-range truncates toward zero. Total on floats, unlike raw FPToSI.
- FPToUISat: SATURATING float to unsigned integer (Rust `f as uN`, LLVM
  fptoui.sat): NaN → 0, negative → 0, above-range → `uN::MAX`. The
  unsigned twin of FPToSISat; contrast the raw FPToUI.

## Pointer conversions
- PtrToInt: pointer to integer
- IntToPtr: integer to pointer
- Bitcast: reinterpret bits (same size required)
- PtrToPtr: provenance retag (address unchanged)
- Transmute: same-size byte reinterpret (Rust core::mem::transmute).
  Validated like Bitcast (size_bits must match). Modelled scalar-only;
  see TrustIr/Semantics/Cast.lean.
- ReifyFnPointer: function item (Ty::Func) to a thin function pointer.
  Source value is a fn-item; modelled as Value.closure with no captures.
-/

/-- Cast operation. Mirrors Rust `trust_ir::CastOp` (17 variants). -/
inductive CastOp where
  | Trunc    : CastOp
  | ZExt     : CastOp
  | SExt     : CastOp
  | FPTrunc  : CastOp
  | FPExt    : CastOp
  | FPToUI   : CastOp
  | FPToSI   : CastOp
  | UIToFP   : CastOp
  | SIToFP   : CastOp
  | PtrToInt : CastOp
  | IntToPtr : CastOp
  | Bitcast        : CastOp
  | PtrToPtr       : CastOp
  | Transmute      : CastOp
  | ReifyFnPointer : CastOp
  | FPToSISat      : CastOp
  | FPToUISat      : CastOp
  deriving DecidableEq, Repr

end TrustIr
