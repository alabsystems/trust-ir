-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Binary, unary, and overflow operation enums.
-- Mirrors: crates/trust_ir/src/inst.rs (BinOp, UnOp, OverflowOp)

namespace TrustIr

/-!
# Arithmetic Operation Enums

These enums mirror the Rust TrustIr instruction set exactly.

## BinOp (18 variants)
Integer: Add, Sub, Mul, UDiv, SDiv, URem, SRem
Float:   FAdd, FSub, FMul, FDiv, FRem
Bitwise: And, Or, Xor, Shl, LShr, AShr

## UnOp (4 variants)
Neg, FNeg, Not, CtPop

## OverflowOp (3 variants)
AddOverflow, SubOverflow, MulOverflow
Returns a pair: (result, overflow_flag)
-/

/-- Binary operation. Mirrors Rust `trust_ir::BinOp` (18 variants). -/
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
  -- Bitwise operations
  | And   : BinOp
  | Or    : BinOp
  | Xor   : BinOp
  | Shl   : BinOp
  | LShr  : BinOp
  | AShr  : BinOp
  deriving DecidableEq, Repr

/-- Unary operation. Mirrors Rust `trust_ir::UnOp` (4 variants). -/
inductive UnOp where
  | Neg   : UnOp
  | FNeg  : UnOp
  | Not   : UnOp
  | CtPop : UnOp
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
  | _ => false

/-- Returns true if the binary operation is an integer operation. -/
def BinOp.isInteger : BinOp → Bool
  | .Add | .Sub | .Mul | .UDiv | .SDiv | .URem | .SRem => true
  | .And | .Or | .Xor | .Shl | .LShr | .AShr => true
  | _ => false

/-- Returns true if the binary operation is a floating-point operation. -/
def BinOp.isFloat : BinOp → Bool
  | .FAdd | .FSub | .FMul | .FDiv | .FRem => true
  | _ => false

end TrustIr
