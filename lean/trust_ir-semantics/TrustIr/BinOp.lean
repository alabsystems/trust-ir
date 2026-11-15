-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Binary, unary, and overflow operation enums.
-- Mirrors: crates/trust_ir/src/inst.rs (BinOp, UnOp, OverflowOp)

namespace TrustIr

/-!
# Arithmetic Operation Enums

These enums mirror the supported Rust arithmetic operators. The operator
axes in `lean_schema_parity.rs` check their names. Constructor presence alone does not
establish executable coverage at every type or width.

## OverflowOp (3 variants)
AddOverflow, SubOverflow, MulOverflow
Returns a pair: (result, overflow_flag)
-/

/-- Binary operation: the modeled subset of Rust `trust_ir::BinOp`. -/
inductive BinOp where
  -- Integer arithmetic
  | Add   : BinOp
  | Sub   : BinOp
  | Mul   : BinOp
  | UDiv  : BinOp
  | SDiv  : BinOp
  | URem  : BinOp
  | SRem  : BinOp
  -- Floating-point arithmetic
  | FAdd  : BinOp
  | FSub  : BinOp
  | FMul  : BinOp
  | FDiv  : BinOp
  | FRem  : BinOp
  | FMin  : BinOp
  | FMax  : BinOp
  -- Bitwise operations
  | And   : BinOp
  | Or    : BinOp
  | Xor   : BinOp
  | Shl   : BinOp
  | LShr  : BinOp
  | AShr  : BinOp
  -- Boolean connectives. DISTINCT from the bitwise `And`/`Or`/`Xor` above, which
  -- denote `Int.land`/`Int.lor`/`Int.xor` -- opaque carriers that say nothing
  -- about a SYMBOLIC operand. A Rust `bool` is carried here as the Int 0/1
  -- value, and MIR spells `BitAnd`/`BitOr`/`BitXor` for both the Bool connective
  -- and the integer operator, distinguishing them only by operand TYPE. A
  -- frontend that lowered a Bool connective onto the bitwise variants would
  -- produce a refinement that closes by `rfl` while asserting nothing a consumer
  -- contract (`ensures r == (a || b)`) could ever discharge against. These three
  -- are the honest target: total, computable, and decidable on the carrier.
  | BAnd  : BinOp
  | BOr   : BinOp
  | BXor  : BinOp
  -- WS3.20 (F-057) bit intrinsics. Rotates are TOTAL integer ops: the amount
  -- is reduced modulo the width (Rust `rotate_left`, LLVM `fshl(x, x, n)`),
  -- so unlike the shifts there is no out-of-range UB. `FCopySign` is IEEE
  -- copySign on the float carrier (magnitude of lhs, sign of rhs).
  | RotL  : BinOp
  | RotR  : BinOp
  | FCopySign : BinOp
  deriving DecidableEq, Repr

/-- Unary operation. Mirrors Rust `trust_ir::UnOp` (the integer and modeled float
    operators).
    WS3.20 (F-057) adds the TOTAL bit intrinsics: `ctlz 0 = cttz 0 = width`
    (one spelling, no poison operand), `bswap` reverses the `width / 8`
    bytes, `bitreverse` reverses all `width` bits. -/
inductive UnOp where
  | Neg   : UnOp
  | FNeg  : UnOp
  | FAbs  : UnOp
  | FSqrt : UnOp
  | FFloor : UnOp
  | FCeil : UnOp
  | FTrunc : UnOp
  | Not   : UnOp
  | CtPop : UnOp
  | CtLz  : UnOp
  | CtTz  : UnOp
  | BSwap : UnOp
  | BitReverse : UnOp
  deriving DecidableEq, Repr

/-- Overflow-checked operation. Mirrors Rust `trust_ir::OverflowOp` (3 variants).
    Returns (result, overflow_flag : Bool). -/
inductive OverflowOp where
  | AddOverflow : OverflowOp
  | SubOverflow : OverflowOp
  | MulOverflow : OverflowOp
  deriving DecidableEq, Repr

/-- Returns true if the binary operation is commutative.
    Used in proof obligations and optimizations. -/
def BinOp.isCommutative : BinOp → Bool
  | .Add | .Mul | .FAdd | .FMul | .And | .Or | .Xor => true
  | .BAnd | .BOr | .BXor => true
  | _ => false

/-- Returns true if the binary operation is an integer operation. -/
def BinOp.isInteger : BinOp → Bool
  | .Add | .Sub | .Mul | .UDiv | .SDiv | .URem | .SRem => true
  | .And | .Or | .Xor | .Shl | .LShr | .AShr => true
  | .RotL | .RotR => true
  -- The Bool connectives operate on the Int 0/1 carrier, so they are integer
  -- ops for typing purposes (and NOT float ops -- `binop_progress` discharges
  -- the float cases by contradiction against this predicate).
  | .BAnd | .BOr | .BXor => true
  | _ => false

/-- Returns true if the binary operation is a floating-point operation. -/
def BinOp.isFloat : BinOp → Bool
  | .FAdd | .FSub | .FMul | .FDiv | .FRem | .FMin | .FMax | .FCopySign => true
  | _ => false

/-- These operations can consume a signed-zero choice from the execution input. -/
def BinOp.isMinMax : BinOp → Bool
  | .FMin | .FMax => true
  | _ => false

end TrustIr
