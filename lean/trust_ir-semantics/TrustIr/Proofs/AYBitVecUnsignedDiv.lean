-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYBitVecArithmetic

namespace TrustIr.TrustIrExpr

private theorem word_trunc {width : Nat} (word : BitVec width) :
    (((Int.ofNat word.toNat % (2 : Int) ^ width) + (2 : Int) ^ width) % (2 : Int) ^ width) =
      Int.ofNat word.toNat := by
  have bound : Int.ofNat word.toNat < (2 : Int) ^ width := by
    have cast := Int.ofNat_lt.mpr word.isLt
    simpa only [Int.natCast_pow] using cast
  have nonnegative : 0 ≤ Int.ofNat word.toNat := Int.ofNat_nonneg _
  simp only [Int.add_emod, Int.emod_emod, Int.emod_self, Int.add_zero]
  exact Int.emod_eq_of_lt nonnegative bound

private theorem allOnes_trunc (width : Nat) :
    Int.ofNat (BitVec.allOnes width).toNat =
      (((-1 : Int) % (2 : Int) ^ width) + (2 : Int) ^ width) % (2 : Int) ^ width := by
  have positive : (0 : Int) < 2 ^ width := by
    have power : (2 : Int) ^ width = ((2 ^ width : Nat) : Int) := (Int.natCast_pow 2 width).symm
    rw [power]
    trustIrCompilerProof
      { exact Int.ofNat_pos.mpr (Nat.two_pow_pos width) }
      { exact Int.natCast_pos.mpr (Nat.two_pow_pos width) }
  have residue : (-1 : Int) % (2 : Int) ^ width = (2 : Int) ^ width - 1 := by
    trustIrCompilerProof {
      rw [Int.neg_emod]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    } {
      rw [Int.neg_emod_eq_sub_emod]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    }
  simp only [Int.add_emod, Int.emod_emod, Int.emod_self, Int.add_zero]
  rw [residue, BitVec.toNat_allOnes]
  change ((2 ^ width - 1 : Nat) : Int) = _
  rw [Int.ofNat_sub (Nat.two_pow_pos width), Int.natCast_pow]
  rfl

private theorem word_zero_iff (width : Nat) (value : Int)
    (range : 0 ≤ value ∧ value < (2 : Int) ^ width) :
    BitVec.ofInt width value = 0 ↔ value = 0 := by
  constructor
  · intro zero
    have exactValue := bitvec_ofInt_toNat width value range.1 range.2
    rw [zero] at exactValue
    change 0 = value at exactValue
    exact exactValue.symm
  · intro zero
    rw [zero]
    apply BitVec.eq_of_toNat_eq
    simp

/-- Actual total SMT division agrees exactly with core smtUDiv, including
its all-ones answer at divisor zero. Typing supplies both operand carriers. -/
theorem bvUDiv_bitvec_value (width : Nat) (left right : TrustIrExpr)
    (leftTyped : SMTSorted width left (.bv width))
    (rightTyped : SMTSorted width right (.bv width)) (env : SMTEnv) :
    Int.ofNat (BitVec.smtUDiv (BitVec.ofInt width (left.evalAt env width))
      (BitVec.ofInt width (right.evalAt env width))).toNat =
      (.bvUDiv left right : TrustIrExpr).evalAt env width := by
  have leftRange := SMTSorted.eval_value_valid width left (.bv width) leftTyped env
  have rightRange := SMTSorted.eval_value_valid width right (.bv width) rightTyped env
  by_cases zero : right.evalAt env width = 0
  · have wordZero := (word_zero_iff width _ rightRange).mpr zero
    rw [BitVec.smtUDiv, if_pos wordZero]
    simp only [TrustIrExpr.evalAt, zero, beq_self_eq_true, if_true]
    exact allOnes_trunc width
  · have wordNonzero : BitVec.ofInt width (right.evalAt env width) ≠ 0 := by
      intro h
      exact zero ((word_zero_iff width _ rightRange).mp h)
    rw [BitVec.smtUDiv, if_neg wordNonzero]
    have boolean : (right.evalAt env width == 0) = false := by simp [zero]
    simp only [TrustIrExpr.evalAt, boolean, Bool.false_eq_true, if_false]
    change Int.ofNat (BitVec.udiv _ _).toNat =
      (((left.evalAt env width / right.evalAt env width) % (2 : Int) ^ width) + (2 : Int) ^ width) % (2 : Int) ^ width
    rw [← bitvec_udiv_value width _ _ leftRange rightRange]
    exact (word_trunc _).symm

/-- Actual total SMT remainder agrees exactly with core umod. Divisor zero
returns the dividend, rather than introducing an IR definedness premise. -/
theorem bvURem_bitvec_value (width : Nat) (left right : TrustIrExpr)
    (leftTyped : SMTSorted width left (.bv width))
    (rightTyped : SMTSorted width right (.bv width)) (env : SMTEnv) :
    Int.ofNat (BitVec.umod (BitVec.ofInt width (left.evalAt env width))
      (BitVec.ofInt width (right.evalAt env width))).toNat =
      (.bvURem left right : TrustIrExpr).evalAt env width := by
  have leftRange := SMTSorted.eval_value_valid width left (.bv width) leftTyped env
  have rightRange := SMTSorted.eval_value_valid width right (.bv width) rightTyped env
  by_cases zero : right.evalAt env width = 0
  · have boolean : (right.evalAt env width == 0) = true := by simp [zero]
    simp only [TrustIrExpr.evalAt, boolean, if_true]
    change Int.ofNat (BitVec.umod _ _).toNat =
      (((left.evalAt env width % (2 : Int) ^ width) + (2 : Int) ^ width) % (2 : Int) ^ width)
    rw [bitvec_umod_value width _ _ leftRange rightRange, zero, Int.emod_zero]
    rw [← bitvec_ofInt_toNat width _ leftRange.1 leftRange.2]
    exact (word_trunc _).symm
  · have boolean : (right.evalAt env width == 0) = false := by simp [zero]
    simp only [TrustIrExpr.evalAt, boolean, Bool.false_eq_true, if_false]
    change Int.ofNat (BitVec.umod _ _).toNat =
      (((left.evalAt env width % right.evalAt env width) % (2 : Int) ^ width) + (2 : Int) ^ width) % (2 : Int) ^ width
    rw [← bitvec_umod_value width _ _ leftRange rightRange]
    exact (word_trunc _).symm

/-- Successful bvUDiv requests retain the exact core result at their returned
width, deriving the operand carriers from actual serializer admission. -/
theorem toSMTRequest_bvUDiv_value (width : Nat) (left right : TrustIrExpr)
    (request : SMTRequest) (built : (.bvUDiv left right : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    Int.ofNat (BitVec.smtUDiv (BitVec.ofInt request.width (left.evalAt env request.width))
      (BitVec.ofInt request.width (right.evalAt env request.width))).toNat =
      (.bvUDiv left right : TrustIrExpr).evalAt env request.width := by
  have metadata := toSMTRequest_metadata (.bvUDiv left right) width request built
  rw [metadata.1]
  have typed := toSMTRequest_sorted (.bvUDiv left right) width request built
  generalize request.sort = sort at typed
  cases typed with
  | bvUDiv leftTyped rightTyped => exact bvUDiv_bitvec_value width left right leftTyped rightTyped env

/-- Successful bvURem requests retain the exact core result at their returned
width, deriving the operand carriers from actual serializer admission. -/
theorem toSMTRequest_bvURem_value (width : Nat) (left right : TrustIrExpr)
    (request : SMTRequest) (built : (.bvURem left right : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    Int.ofNat (BitVec.umod (BitVec.ofInt request.width (left.evalAt env request.width))
      (BitVec.ofInt request.width (right.evalAt env request.width))).toNat =
      (.bvURem left right : TrustIrExpr).evalAt env request.width := by
  have metadata := toSMTRequest_metadata (.bvURem left right) width request built
  rw [metadata.1]
  have typed := toSMTRequest_sorted (.bvURem left right) width request built
  generalize request.sort = sort at typed
  cases typed with
  | bvURem leftTyped rightTyped => exact bvURem_bitvec_value width left right leftTyped rightTyped env

end TrustIr.TrustIrExpr

/-- info: 'TrustIr.TrustIrExpr.bitvec_udiv_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.bitvec_udiv_value

/-- info: 'TrustIr.TrustIrExpr.bitvec_umod_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.bitvec_umod_value

/-- info: 'TrustIr.TrustIrExpr.bvUDiv_bitvec_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.bvUDiv_bitvec_value

/-- info: 'TrustIr.TrustIrExpr.bvURem_bitvec_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.bvURem_bitvec_value

/-- info: 'TrustIr.TrustIrExpr.toSMTRequest_bvUDiv_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.toSMTRequest_bvUDiv_value

/-- info: 'TrustIr.TrustIrExpr.toSMTRequest_bvURem_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.toSMTRequest_bvURem_value

