-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Arithmetic properties: commutativity, associativity, etc.
-- Phase 1 proofs from the formalization roadmap.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 6 Phase 1

import TrustIr.Semantics.Arith

namespace TrustIr

/-!
# Arithmetic Properties

These theorems establish key algebraic properties of TrustIr's arithmetic
instructions. They are the Phase 1 proof deliverables.

## Proved properties

1. Integer addition commutativity
2. Integer multiplication commutativity
3. Bitwise AND/OR/XOR commutativity
4. ICmpOp double negation (in CmpOp.lean)
5. Truncate-unsigned is idempotent

## Design note

These proofs operate on the pure functions (semIntBinOp, truncateUnsigned)
rather than the monadic wrappers (semBinOp). This keeps the proofs
clean and composable. Lifting to the monadic level is mechanical.
-/

-- =================================================================
-- Commutativity
-- =================================================================

/-- Integer addition wraps around `2^width`, so `a + b ≡ b + a (mod 2^w)`.
    This is the wrapping addition commutativity theorem. -/
theorem add_comm_int (width : Nat) (a b : Int) :
    semIntBinOp .Add width a b = semIntBinOp .Add width b a := by
  simp [semIntBinOp, Int.add_comm]

/-- Integer multiplication commutativity under modular arithmetic. -/
theorem mul_comm_int (width : Nat) (a b : Int) :
    semIntBinOp .Mul width a b = semIntBinOp .Mul width b a := by
  simp [semIntBinOp, Int.mul_comm]

/-- Bitwise AND commutativity. -/
theorem and_comm_int (width : Nat) (a b : Int) :
    semIntBinOp .And width a b = semIntBinOp .And width b a := by
  simp [semIntBinOp, Int.land_comm]

/-- Bitwise OR commutativity. -/
theorem or_comm_int (width : Nat) (a b : Int) :
    semIntBinOp .Or width a b = semIntBinOp .Or width b a := by
  simp [semIntBinOp, Int.lor_comm]

/-- Bitwise XOR commutativity. -/
theorem xor_comm_int (width : Nat) (a b : Int) :
    semIntBinOp .Xor width a b = semIntBinOp .Xor width b a := by
  simp [semIntBinOp, Int.xor_comm]

-- =================================================================
-- Truncation properties
-- =================================================================

/-- Truncating an already-truncated value is idempotent.
    truncateUnsigned (truncateUnsigned v w) w = truncateUnsigned v w -/
theorem truncate_idempotent (v : Int) (w : Nat) :
    truncateUnsigned (truncateUnsigned v w) w = truncateUnsigned v w := by
  simp [truncateUnsigned, Int.emod_emod_of_dvd]

-- =================================================================
-- Division safety
-- =================================================================

/-- Unsigned division by nonzero always succeeds. -/
theorem udiv_nonzero_ok (width : Nat) (a b : Int) (hb : b ≠ 0) :
    ∃ r, semIntBinOp .UDiv width a b = .ok r := by
  simp [semIntBinOp, hb]

/-- Signed division by a nonzero divisor succeeds **except** for the one
    overflowing case `INT_MIN / -1`, which is undefined behavior (matches the
    Rust reference interpreter and LLVM `sdiv`; see docs/ub-numerics-policy.md
    §1). The `hov` hypothesis is exactly the `NoOverflow` obligation a frontend
    must discharge for an unconstrained signed division. -/
theorem sdiv_nonzero_ok (width : Nat) (a b : Int) (hb : b ≠ 0)
    (hov : ¬(toSigned a width = -((2 : Int) ^ (width - 1)) ∧ toSigned b width = -1)) :
    ∃ r, semIntBinOp .SDiv width a b = .ok r := by
  have hb' : (b == 0) = false := by simpa using hb
  simp only [semIntBinOp, hb', if_false]
  split
  · rename_i hbad
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hbad
    exact absurd hbad hov
  · exact ⟨_, rfl⟩

-- =================================================================
-- Future work stubs (Phase 1 completeness claims)
-- =================================================================

/-
## Theorems to prove in subsequent iterations

1. **Associativity of wrapping addition:**
   `semIntBinOp .Add w (semIntBinOp .Add w a b) c = semIntBinOp .Add w a (semIntBinOp .Add w b c)`
   Requires extracting the .ok value from the Except.

2. **Cast round-trip (ZExt after Trunc):**
   When upper bits are zero and n <= m:
   `semCast .ZExt n m (semCast .Trunc m n x) = semCast .ZExt n m x`

3. **Determinism (trivially true for pure instructions):**
   `stepInst inst s = stepInst inst s`

4. **Progress (well-typed pure instructions always produce a result):**
   For well-typed arithmetic instructions, stepInst never returns typeError.
-/

end TrustIr
