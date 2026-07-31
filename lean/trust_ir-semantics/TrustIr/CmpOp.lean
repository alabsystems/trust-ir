-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Comparison operation enums.
-- Mirrors: crates/trust_ir/src/inst.rs (ICmpOp, FCmpOp)

namespace TrustIr

/-!
# Comparison Operations

## ICmpOp (10 variants)
Integer comparisons. Signedness is in the operation, not the type.
- Eq, Ne: equality (sign-independent for two's complement)
- Ult, Ule, Ugt, Uge: unsigned comparisons
- Slt, Sle, Sgt, Sge: signed comparisons

## FCmpOp (12 variants)
IEEE 754 floating-point comparisons.
- O-prefix: ordered (false if either operand is NaN)
- U-prefix: unordered (true if either operand is NaN)
-/

/-- Integer comparison operation. Mirrors Rust `trust_ir::ICmpOp` (10 variants). -/
inductive ICmpOp where
  | Eq   : ICmpOp
  | Ne   : ICmpOp
  | Ult  : ICmpOp
  | Ule  : ICmpOp
  | Ugt  : ICmpOp
  | Uge  : ICmpOp
  | Slt  : ICmpOp
  | Sle  : ICmpOp
  | Sgt  : ICmpOp
  | Sge  : ICmpOp
  deriving DecidableEq, Repr

/-- Floating-point comparison operation. Mirrors Rust `trust_ir::FCmpOp` (12 variants).
    O = ordered (false if NaN), U = unordered (true if NaN). -/
inductive FCmpOp where
  | OEq  : FCmpOp
  | ONe  : FCmpOp
  | OLt  : FCmpOp
  | OLe  : FCmpOp
  | OGt  : FCmpOp
  | OGe  : FCmpOp
  | UEq  : FCmpOp
  | UNe  : FCmpOp
  | ULt  : FCmpOp
  | ULe  : FCmpOp
  | UGt  : FCmpOp
  | UGe  : FCmpOp
  deriving DecidableEq, Repr

/-- Returns the negation of an integer comparison. -/
def ICmpOp.negate : ICmpOp → ICmpOp
  | .Eq  => .Ne
  | .Ne  => .Eq
  | .Ult => .Uge
  | .Ule => .Ugt
  | .Ugt => .Ule
  | .Uge => .Ult
  | .Slt => .Sge
  | .Sle => .Sgt
  | .Sgt => .Sle
  | .Sge => .Slt

/-- Double negation of ICmpOp is identity. -/
theorem ICmpOp.negate_negate (op : ICmpOp) : op.negate.negate = op := by
  cases op <;> rfl

end TrustIr
