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
  | .BAnd | .BOr | .BXor => true
  | _ => false

/-- Returns true if the binary operation is an integer operation. -/
def BinOp.isInteger : BinOp → Bool
  | .Add | .Sub | .Mul | .UDiv | .SDiv | .URem | .SRem => true
  | .And | .Or | .Xor | .Shl | .LShr | .AShr => true
  -- The Bool connectives operate on the Int 0/1 carrier, so they are integer
  -- ops for typing purposes (and NOT float ops -- `binop_progress` discharges
  -- the float cases by contradiction against this predicate).
  | .BAnd | .BOr | .BXor => true
  | _ => false

/-- Returns true if the binary operation is a floating-point operation. -/
def BinOp.isFloat : BinOp → Bool
  | .FAdd | .FSub | .FMul | .FDiv | .FRem => true
  | _ => false

end TrustIr
