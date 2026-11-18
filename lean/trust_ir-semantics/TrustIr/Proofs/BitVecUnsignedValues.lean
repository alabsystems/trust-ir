-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.CompilerCompat
import Init.Data.BitVec.Lemmas

/-! Shared core word-value facts. These retain their original public names
and proofs; operator semantics need no SMT term, printer or solver axioms. -/

namespace TrustIr.TrustIrExpr

/-- Core BitVec conversion retains the actual unsigned residue. -/
theorem bitvec_ofInt_toNat (width : Nat) (value : Int)
    (nonnegative : 0 ≤ value) (bound : value < (2 : Int) ^ width) :
    Int.ofNat (BitVec.ofInt width value).toNat = value := by
  change Int.ofNat (value % Int.ofNat (2 ^ width)).toNat = value
  have power : Int.ofNat (2 ^ width) = (2 : Int) ^ width := Int.natCast_pow 2 width
  rw [power, Int.emod_eq_of_lt nonnegative bound]
  exact Int.toNat_of_nonneg nonnegative

/-- Core unsigned division retains the full natural quotient of canonical operands. -/
theorem bitvec_udiv_value (width : Nat) (left right : Int)
    (leftRange : 0 ≤ left ∧ left < (2 : Int) ^ width)
    (rightRange : 0 ≤ right ∧ right < (2 : Int) ^ width) :
    Int.ofNat (BitVec.udiv (BitVec.ofInt width left) (BitVec.ofInt width right)).toNat = left / right := by
  have leftNat : ((BitVec.ofInt width left).toNat : Int) = left :=
    bitvec_ofInt_toNat width left leftRange.1 leftRange.2
  have rightNat : ((BitVec.ofInt width right).toNat : Int) = right :=
    bitvec_ofInt_toNat width right rightRange.1 rightRange.2
  change (((BitVec.ofInt width left).toNat / (BitVec.ofInt width right).toNat : Nat) : Int) = _
  trustIrCompilerProof
    { rw [Int.ofNat_ediv, leftNat, rightNat] }
    { rw [Int.natCast_ediv, leftNat, rightNat] }

/-- Core unsigned remainder retains the full natural remainder, including divisor zero. -/
theorem bitvec_umod_value (width : Nat) (left right : Int)
    (leftRange : 0 ≤ left ∧ left < (2 : Int) ^ width)
    (rightRange : 0 ≤ right ∧ right < (2 : Int) ^ width) :
    Int.ofNat (BitVec.umod (BitVec.ofInt width left) (BitVec.ofInt width right)).toNat = left % right := by
  have leftNat : ((BitVec.ofInt width left).toNat : Int) = left :=
    bitvec_ofInt_toNat width left leftRange.1 leftRange.2
  have rightNat : ((BitVec.ofInt width right).toNat : Int) = right :=
    bitvec_ofInt_toNat width right rightRange.1 rightRange.2
  change (((BitVec.ofInt width left).toNat % (BitVec.ofInt width right).toNat : Nat) : Int) = _
  trustIrCompilerProof
    { rw [Int.ofNat_emod, leftNat, rightNat] }
    { rw [Int.natCast_emod, leftNat, rightNat] }

end TrustIr.TrustIrExpr
