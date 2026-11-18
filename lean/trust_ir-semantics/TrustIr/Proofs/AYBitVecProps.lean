-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYValueProps
import TrustIr.Proofs.BitVecUnsignedValues

namespace TrustIr.TrustIrExpr

/-- The actual two's-complement interpretation agrees with core BitVec.toInt. -/
theorem bitvec_ofInt_toSigned (width : Nat) (positive : 0 < width) (value : Int)
    (nonnegative : 0 ≤ value) (bound : value < (2 : Int) ^ width) :
    (BitVec.ofInt width value).toInt = toSigned value width := by
  have exactValue : ((BitVec.ofInt width value).toNat : Int) = value :=
    bitvec_ofInt_toNat width value nonnegative bound
  have power : (2 : Int) ^ width = 2 * (2 : Int) ^ (width - 1) := by
    have successor : width = (width - 1) + 1 := by omega
    calc
      (2 : Int) ^ width = 2 ^ ((width - 1) + 1) := congrArg (fun n => (2 : Int) ^ n) successor
      _ = 2 * (2 : Int) ^ (width - 1) := by rw [Int.pow_succ, Int.mul_comm]
  have castPower : ((2 ^ width : Nat) : Int) = (2 : Int) ^ width := Int.natCast_pow 2 width
  have threshold : (2 * (BitVec.ofInt width value).toNat < 2 ^ width) ↔
      ¬ value ≥ (2 : Int) ^ (width - 1) := by
    have cast : ((2 * (BitVec.ofInt width value).toNat : Nat) : Int) = 2 * value := by
      rw [Int.natCast_mul, exactValue]
      rfl
    constructor
    · intro h
      have h' := Int.ofNat_lt.mpr h
      rw [cast, castPower, power] at h'
      omega
    · intro h
      apply Int.ofNat_lt.mp
      rw [cast, castPower, power]
      omega
  simp only [BitVec.toInt, toSigned, Int.emod_eq_of_lt nonnegative bound]
  rw [exactValue, castPower]
  by_cases high : value ≥ (2 : Int) ^ (width - 1)
  · have low : ¬ 2 * (BitVec.ofInt width value).toNat < 2 ^ width := by
      intro h; exact (threshold.mp h) high
    rw [if_neg low, if_pos high]
  · have low := threshold.mpr high
    rw [if_pos low, if_neg high]

/-- Target predicates use the pinned core's independent BitVec operations. -/
def bitvecICmp {width : Nat} (op : ICmpOp) (x y : BitVec width) : Bool :=
  match op with
  | .Eq => decide (x = y) | .Ne => decide (x ≠ y)
  | .Ult => x.ult y | .Ule => x.ule y | .Ugt => y.ult x | .Uge => y.ule x
  | .Slt => x.slt y | .Sle => x.sle y | .Sgt => y.slt x | .Sge => y.sle x

/-- All ten actual predicates agree with the independent core BitVec relations. -/
theorem semICmp_bitvec (op : ICmpOp) (width : Nat) (positive : 0 < width)
    (left right : Int) (leftRange : 0 ≤ left ∧ left < (2 : Int) ^ width)
    (rightRange : 0 ≤ right ∧ right < (2 : Int) ^ width) :
    semICmp op width left right =
      bitvecICmp op (BitVec.ofInt width left) (BitVec.ofInt width right) := by
  have leftNat : ((BitVec.ofInt width left).toNat : Int) = left :=
    bitvec_ofInt_toNat width left leftRange.1 leftRange.2
  have rightNat : ((BitVec.ofInt width right).toNat : Int) = right :=
    bitvec_ofInt_toNat width right rightRange.1 rightRange.2
  have leftSigned := bitvec_ofInt_toSigned width positive left leftRange.1 leftRange.2
  have rightSigned := bitvec_ofInt_toSigned width positive right rightRange.1 rightRange.2
  cases op <;> apply Bool.eq_iff_iff.mpr <;>
    simp only [semICmp, bitvecICmp, BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle,
      leftSigned, rightSigned, decide_eq_true_eq, beq_iff_eq, bne_iff_ne,
      BitVec.toNat_eq, BitVec.toNat_ne] <;> omega

/-- Actual expression evaluation reaches core BitVec predicates for every
integer comparison opcode and arbitrary well-sorted operand expressions. -/
theorem icmp_encoding_bitvec (op : ICmpOp) (width : Nat) (positive : 0 < width)
    (left right : TrustIrExpr)
    (leftTyped : SMTSorted width left (.bv width))
    (rightTyped : SMTSorted width right (.bv width)) (env : SMTEnv) :
    (encodeICmp op left right).evalAt env width =
      if bitvecICmp op (BitVec.ofInt width (left.evalAt env width))
        (BitVec.ofInt width (right.evalAt env width)) then 1 else 0 := by
  rw [icmp_encoding_correct_at, semICmp_bitvec op width positive]
  · exact SMTSorted.eval_value_valid width left (.bv width) leftTyped env
  · exact SMTSorted.eval_value_valid width right (.bv width) rightTyped env

/-- The comparison connection holds at the width of the actual emitted request. -/
theorem toSMTRequest_icmp_bitvec (op : ICmpOp) (width : Nat) (left right : TrustIrExpr)
    (leftTyped : SMTSorted width left (.bv width))
    (rightTyped : SMTSorted width right (.bv width))
    (request : SMTRequest) (built : (encodeICmp op left right).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    (encodeICmp op left right).evalAt env request.width =
      if bitvecICmp op (BitVec.ofInt request.width (left.evalAt env request.width))
        (BitVec.ofInt request.width (right.evalAt env request.width)) then 1 else 0 := by
  have metadata := toSMTRequest_metadata (encodeICmp op left right) width request built
  rw [metadata.1]
  exact icmp_encoding_bitvec op width metadata.2.1 left right leftTyped rightTyped env

end TrustIr.TrustIrExpr



#trustIrAxiomsExact TrustIr.TrustIrExpr.bitvec_ofInt_toNat == [propext]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bitvec_ofInt_toSigned == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.TrustIrExpr.semICmp_bitvec == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.TrustIrExpr.icmp_encoding_bitvec == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.TrustIrExpr.toSMTRequest_icmp_bitvec == [propext, Classical.choice, Quot.sound]

