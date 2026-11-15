-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYBitVecUnsignedDiv

namespace TrustIr.TrustIrExpr

private theorem word_of_unsigned {width : Nat} (word : BitVec width) :
    BitVec.ofInt width (word.toNat : Int) = word := by
  trustIrCompilerProof {
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt, ← Int.ofNat_emod, Nat.mod_eq_of_lt word.isLt]
    rfl
  } {
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt, ← Int.natCast_emod, Nat.mod_eq_of_lt word.isLt]
    rfl
  }

/-- Signed word interpretation is the sign-selected natural magnitude, even
for the minimum signed word whose negation has the same bit pattern. -/
theorem bitvec_signed_magnitude {width : Nat} (positive : 0 < width) (word : BitVec width) :
    word.toInt = if word.msb then -((-word).toNat : Int) else (word.toNat : Int) := by
  trustIrCompilerProof {
    have power : (2 : Nat) ^ width = 2 * (2 : Nat) ^ (width - 1) := by
      have successor : width = (width - 1) + 1 := by omega
      calc
        (2 : Nat) ^ width = 2 ^ ((width - 1) + 1) := congrArg (fun n => (2 : Nat) ^ n) successor
        _ = 2 * (2 : Nat) ^ (width - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    have bound := word.isLt
    cases sign : word.msb with
    | false =>
      have low : ¬ 2 ^ (width - 1) ≤ word.toNat := by
        exact of_decide_eq_false ((BitVec.msb_eq_decide word).symm.trans sign)
      have doubled : 2 * word.toNat < 2 ^ width := by omega
      simp only [BitVec.toInt, doubled, if_true, sign, Bool.false_eq_true, if_false]
    | true =>
      have high := BitVec.toNat_ge_of_msb_true sign
      have doubled : ¬ 2 * word.toNat < 2 ^ width := by omega
      have difference : 2 ^ width - word.toNat < 2 ^ width := by omega
      simp only [BitVec.toInt, doubled, if_false, sign, if_true, BitVec.toNat_neg,
        Nat.mod_eq_of_lt difference]
      rw [Int.ofNat_sub (Nat.le_of_lt bound)]
      omega
  } {
    cases sign : word.msb with
    | false => simpa only [sign, Bool.false_eq_true, if_false] using (BitVec.toInt_eq_toNat_of_msb sign)
    | true => simpa only [sign, if_true] using (BitVec.toInt_eq_neg_toNat_neg_of_msb_true sign)
  }

private theorem unsigned_div_word {width : Nat} (left right : BitVec width) :
    BitVec.ofInt width (trustIrIntTDiv (left.toNat : Int) (right.toNat : Int)) = BitVec.udiv left right := by
  trustIrCompilerProof {
    rw [Int.div_eq_ediv (Int.ofNat_nonneg _) (Int.ofNat_nonneg _), ← Int.ofNat_ediv]
    exact word_of_unsigned (BitVec.udiv left right)
  } {
    rw [Int.tdiv_eq_ediv_of_nonneg (Int.ofNat_nonneg _), ← Int.natCast_ediv]
    exact word_of_unsigned (BitVec.udiv left right)
  }

private theorem unsigned_mod_word {width : Nat} (left right : BitVec width) :
    BitVec.ofInt width (trustIrIntTMod (left.toNat : Int) (right.toNat : Int)) = BitVec.umod left right := by
  trustIrCompilerProof {
    rw [Int.mod_eq_emod (Int.ofNat_nonneg _) (Int.ofNat_nonneg _), ← Int.ofNat_emod]
    exact word_of_unsigned (BitVec.umod left right)
  } {
    rw [Int.tmod_eq_emod_of_nonneg (Int.ofNat_nonneg _), ← Int.natCast_emod]
    exact word_of_unsigned (BitVec.umod left right)
  }

private theorem neg_mod (left right : Int) : trustIrIntTMod (-left) right = -(trustIrIntTMod left right) := by
  trustIrCompilerProof {
    rw [Int.mod_def, Int.mod_def, Int.neg_div, Int.mul_neg]
    omega
  } {
    exact Int.neg_tmod left right
  }

private theorem word_neg_neg {width : Nat} (word : BitVec width) : -(-word) = word := by
  have equality := congrArg (BitVec.ofInt width) (Int.neg_neg (word.toNat : Int))
  rw [bitvec_ofInt_neg, bitvec_ofInt_neg, word_of_unsigned] at equality
  exact equality

/-- The pinned core's sign-selected division implements truncation toward zero,
including the modular minimum-word divided by minus-one result. -/
theorem bitvec_sdiv_ofInt {width : Nat} (positive : 0 < width) (left right : BitVec width) :
    BitVec.ofInt width (trustIrIntTDiv left.toInt right.toInt) = BitVec.sdiv left right := by
  trustIrCompilerProof {
    rw [bitvec_signed_magnitude positive left, bitvec_signed_magnitude positive right]
    cases leftSign : left.msb <;> cases rightSign : right.msb <;>
      simp only [Bool.false_eq_true, if_false, if_true, BitVec.sdiv, leftSign, rightSign,
        Int.neg_div_neg, Int.neg_div, Int.div_neg, bitvec_ofInt_neg, unsigned_div_word, word_neg_neg] <;> rfl
  } {
    rw [bitvec_signed_magnitude positive left, bitvec_signed_magnitude positive right]
    cases leftSign : left.msb <;> cases rightSign : right.msb <;>
      simp only [Bool.false_eq_true, if_false, if_true, BitVec.sdiv_eq, leftSign, rightSign,
        Int.neg_tdiv_neg, Int.neg_tdiv, Int.tdiv_neg, bitvec_ofInt_neg, unsigned_div_word, word_neg_neg] <;> rfl
  }

/-- The pinned core's signed remainder follows the dividend sign, including
zero divisor and the minimum-word divided by minus-one result. -/
theorem bitvec_srem_ofInt {width : Nat} (positive : 0 < width) (left right : BitVec width) :
    BitVec.ofInt width (trustIrIntTMod left.toInt right.toInt) = BitVec.srem left right := by
  trustIrCompilerProof {
    rw [bitvec_signed_magnitude positive left, bitvec_signed_magnitude positive right]
    cases leftSign : left.msb <;> cases rightSign : right.msb <;>
      simp only [Bool.false_eq_true, if_false, if_true, BitVec.srem, leftSign, rightSign,
        Int.mod_neg, neg_mod, bitvec_ofInt_neg, unsigned_mod_word] <;> rfl
  } {
    rw [bitvec_signed_magnitude positive left, bitvec_signed_magnitude positive right]
    cases leftSign : left.msb <;> cases rightSign : right.msb <;>
      simp only [Bool.false_eq_true, if_false, if_true, BitVec.srem_eq, leftSign, rightSign,
        Int.tmod_neg, neg_mod, bitvec_ofInt_neg, unsigned_mod_word] <;> rfl
  }

private theorem negative_magnitude_positive {width : Nat} (word : BitVec width)
    (sign : word.msb = true) : 0 < (-word).toNat := by
  have high := BitVec.toNat_ge_of_msb_true sign
  have halfPositive := Nat.two_pow_pos (width - 1)
  have _bound := word.isLt
  have difference : 2 ^ width - word.toNat < 2 ^ width := by omega
  rw [BitVec.toNat_neg, Nat.mod_eq_of_lt difference]
  omega

/-- The sign bit exactly records a negative signed interpretation. -/
theorem bitvec_toInt_negative_iff {width : Nat} (positive : 0 < width) (word : BitVec width) :
    word.toInt < 0 ↔ word.msb = true := by
  trustIrCompilerProof {
    rw [bitvec_signed_magnitude positive word]
    cases sign : word.msb with
    | false =>
      simp only [Bool.false_eq_true, if_false, iff_false]
      have nonnegative : (0 : Int) ≤ (word.toNat : Int) := Int.ofNat_nonneg _
      omega
    | true =>
      have magnitude : (0 : Int) < ((-word).toNat : Int) :=
        Int.ofNat_pos.mpr (negative_magnitude_positive word sign)
      simp only [if_true, iff_true]
      omega
  } {
    exact BitVec.toInt_neg_iff.trans BitVec.msb_eq_true_iff_two_mul_ge.symm
  }

private theorem word_toInt_zero_iff {width : Nat} (word : BitVec width) :
    word.toInt = 0 ↔ word = 0 := by
  trustIrCompilerProof {
    have zeroNat : (0 : BitVec width).toNat = 0 := by
      change (BitVec.ofNat width 0).toNat = 0
      rw [BitVec.toNat_ofNat, Nat.zero_mod]
    have zeroInt : (0 : BitVec width).toInt = 0 := by
      rw [BitVec.toInt, zeroNat]
      have low : 2 * 0 < 2 ^ width := by simpa only [Nat.mul_zero] using Nat.two_pow_pos width
      rw [if_pos low]
      rfl
    constructor
    · intro zero
      apply BitVec.eq_of_toInt_eq
      rw [zeroInt]
      exact zero
    · intro zero
      rw [zero]
      exact zeroInt
  } {
    constructor
    · intro zero
      apply BitVec.eq_of_toInt_eq
      exact zero.trans (show (0 : BitVec width).toInt = 0 from BitVec.toInt_zero).symm
    · intro zero
      rw [zero]
      exact BitVec.toInt_zero
  }

private theorem word_neg_zero_iff {width : Nat} (word : BitVec width) : -word = 0 ↔ word = 0 := by
  constructor
  · intro zero
    have back := congrArg (fun z : BitVec width => -z) zero
    change -(-word) = -(0 : BitVec width) at back
    have zeroNeg : -(0 : BitVec width) = 0 := BitVec.neg_zero width
    rw [word_neg_neg, zeroNeg] at back
    exact back
  · intro zero
    rw [zero]
    exact BitVec.neg_zero width

private theorem ofInt_one (width : Nat) : BitVec.ofInt width 1 = 1 := by
  trustIrCompilerProof {
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt]
    change (((1 : Nat) : Int) % ((2 ^ width : Nat) : Int)).toNat = 1 % 2 ^ width
    rw [← Int.ofNat_emod]
    rfl
  } {
    exact BitVec.ofInt_natCast width 1
  }

private theorem ofInt_neg_one (width : Nat) : BitVec.ofInt width (-1) = BitVec.allOnes width := by
  trustIrCompilerProof {
    rw [bitvec_ofInt_neg, ofInt_one]
    exact BitVec.negOne_eq_allOnes
  } {
    rw [bitvec_ofInt_neg, ofInt_one]
    exact BitVec.neg_one_eq_allOnes
  }

private theorem smtSDiv_eq_sdiv {width : Nat} (left right : BitVec width) (nonzero : right ≠ 0) :
    BitVec.smtSDiv left right = BitVec.sdiv left right := by
  trustIrCompilerProof {
    have negNonzero : BitVec.neg right ≠ (0 : BitVec width) := by
      intro zero
      exact nonzero ((word_neg_zero_iff right).mp zero)
    cases leftSign : left.msb <;> cases rightSign : right.msb <;>
      simp only [BitVec.smtSDiv, BitVec.sdiv, leftSign, rightSign, BitVec.smtUDiv,
        if_neg nonzero, if_neg negNonzero] <;> rfl
  } {
    have negNonzero : -right ≠ (0 : BitVec width) := by
      intro zero
      exact nonzero ((word_neg_zero_iff right).mp zero)
    cases leftSign : left.msb <;> cases rightSign : right.msb <;>
      simp only [BitVec.smtSDiv_eq, BitVec.sdiv_eq, leftSign, rightSign, BitVec.smtUDiv,
        if_neg nonzero, if_neg negNonzero] <;> rfl
  }

/-- Core SMT signed division agrees with the total signed integer definition,
including the sign-dependent divisor-zero answer. -/
theorem bitvec_smtSDiv_ofInt {width : Nat} (positive : 0 < width) (left right : BitVec width) :
    BitVec.ofInt width (if right.toInt == 0 then (if left.toInt < 0 then 1 else -1)
      else trustIrIntTDiv left.toInt right.toInt) = BitVec.smtSDiv left right := by
  trustIrCompilerProof {
    by_cases zero : right = 0
    · have intZero := (word_toInt_zero_iff right).mpr zero
      simp only [intZero, beq_self_eq_true, if_true]
      rw [zero]
      have zeroSign : (0 : BitVec width).msb = false := BitVec.msb_zero
      cases sign : left.msb with
      | false =>
        have nonnegative : ¬ left.toInt < 0 := by
          rw [bitvec_toInt_negative_iff positive]
          simp only [sign, Bool.false_eq_true, not_false_eq_true]
        rw [if_neg nonnegative, ofInt_neg_one]
        simp only [BitVec.smtSDiv, sign, zeroSign, BitVec.smtUDiv, if_pos rfl] <;> rfl
      | true =>
        have negative := (bitvec_toInt_negative_iff positive left).mpr sign
        rw [if_pos negative, ofInt_one]
        simp only [BitVec.smtSDiv, sign, zeroSign, BitVec.smtUDiv, if_pos rfl]
        change (1 : BitVec width) = -(BitVec.allOnes width)
        rw [← BitVec.negOne_eq_allOnes, word_neg_neg]
        rfl
    · have intNonzero : right.toInt ≠ 0 := by
        intro h
        exact zero ((word_toInt_zero_iff right).mp h)
      have boolean : (right.toInt == 0) = false := by simp [intNonzero]
      rw [boolean]
      simp only [Bool.false_eq_true, if_false]
      rw [bitvec_sdiv_ofInt positive, smtSDiv_eq_sdiv left right zero]
  } {
    by_cases zero : right = 0
    · have intZero := (word_toInt_zero_iff right).mpr zero
      simp only [intZero, beq_self_eq_true, if_true]
      rw [zero]
      have zeroSign : (0 : BitVec width).msb = false := BitVec.msb_zero
      cases sign : left.msb with
      | false =>
        have nonnegative : ¬ left.toInt < 0 := by
          rw [bitvec_toInt_negative_iff positive]
          simp only [sign, Bool.false_eq_true, not_false_eq_true]
        rw [if_neg nonnegative, ofInt_neg_one]
        simp only [BitVec.smtSDiv_eq, sign, zeroSign, BitVec.smtUDiv, if_pos rfl] <;> rfl
      | true =>
        have negative := (bitvec_toInt_negative_iff positive left).mpr sign
        rw [if_pos negative, ofInt_one]
        simp only [BitVec.smtSDiv_eq, sign, zeroSign, BitVec.smtUDiv, if_pos rfl]
        change (1 : BitVec width) = -(BitVec.allOnes width)
        rw [← BitVec.neg_one_eq_allOnes, word_neg_neg]
        rfl
    · have intNonzero : right.toInt ≠ 0 := by
        intro h
        exact zero ((word_toInt_zero_iff right).mp h)
      have boolean : (right.toInt == 0) = false := by simp [intNonzero]
      rw [boolean]
      simp only [Bool.false_eq_true, if_false]
      rw [bitvec_sdiv_ofInt positive, smtSDiv_eq_sdiv left right zero]
  }

private theorem word_of_signed {width : Nat} (positive : 0 < width) (word : BitVec width) :
    BitVec.ofInt width word.toInt = word := by
  rw [bitvec_signed_magnitude positive word]
  cases _sign : word.msb <;>
    simp only [Bool.false_eq_true, if_false, if_true, bitvec_ofInt_neg, word_of_unsigned,
      word_neg_neg]

private theorem ofInt_mod (width : Nat) (value : Int) :
    BitVec.ofInt width (value % (2 : Int) ^ width) = BitVec.ofInt width value := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  have power : ((2 ^ width : Nat) : Int) = (2 : Int) ^ width := Int.natCast_pow 2 width
  rw [power, Int.emod_emod]

/-- Actual total signed division reaches core smtSDiv at every positive width,
for arbitrary typed expressions and integer environments. -/
theorem bvSDiv_bitvec (width : Nat) (positive : 0 < width) (left right : TrustIrExpr)
    (leftTyped : SMTSorted width left (.bv width))
    (rightTyped : SMTSorted width right (.bv width)) (env : SMTEnv) :
    BitVec.ofInt width ((.bvSDiv left right : TrustIrExpr).evalAt env width) =
      BitVec.smtSDiv (BitVec.ofInt width (left.evalAt env width))
        (BitVec.ofInt width (right.evalAt env width)) := by
  have leftRange := SMTSorted.eval_value_valid width left (.bv width) leftTyped env
  have rightRange := SMTSorted.eval_value_valid width right (.bv width) rightTyped env
  rw [bvSDiv_evalAt_semantics, truncateUnsigned, ofInt_mod]
  rw [← bitvec_ofInt_toSigned width positive _ leftRange.1 leftRange.2,
    ← bitvec_ofInt_toSigned width positive _ rightRange.1 rightRange.2]
  exact bitvec_smtSDiv_ofInt positive _ _

/-- Actual total signed remainder reaches core srem, retaining divisor zero. -/
theorem bvSRem_bitvec (width : Nat) (positive : 0 < width) (left right : TrustIrExpr)
    (leftTyped : SMTSorted width left (.bv width))
    (rightTyped : SMTSorted width right (.bv width)) (env : SMTEnv) :
    BitVec.ofInt width ((.bvSRem left right : TrustIrExpr).evalAt env width) =
      BitVec.srem (BitVec.ofInt width (left.evalAt env width))
        (BitVec.ofInt width (right.evalAt env width)) := by
  trustIrCompilerProof {
    have leftRange := SMTSorted.eval_value_valid width left (.bv width) leftTyped env
    have rightRange := SMTSorted.eval_value_valid width right (.bv width) rightTyped env
    rw [bvSRem_evalAt_semantics, truncateUnsigned, ofInt_mod]
    rw [← bitvec_ofInt_toSigned width positive _ leftRange.1 leftRange.2,
      ← bitvec_ofInt_toSigned width positive _ rightRange.1 rightRange.2]
    by_cases zero : (BitVec.ofInt width (right.evalAt env width)).toInt = 0
    · have boolean : ((BitVec.ofInt width (right.evalAt env width)).toInt == 0) = true := by
        simpa only [beq_iff_eq] using zero
      rw [boolean]
      simp only [if_true]
      rw [← bitvec_srem_ofInt positive, zero, Int.mod_zero, word_of_signed positive]
    · have boolean : ((BitVec.ofInt width (right.evalAt env width)).toInt == 0) = false := by
        apply Bool.eq_false_iff.mpr
        intro equal
        exact zero (eq_of_beq equal)
      rw [boolean]
      simp only [Bool.false_eq_true, if_false]
      exact bitvec_srem_ofInt positive _ _
  } {
    have leftRange := SMTSorted.eval_value_valid width left (.bv width) leftTyped env
    have rightRange := SMTSorted.eval_value_valid width right (.bv width) rightTyped env
    rw [bvSRem_evalAt_semantics, truncateUnsigned, ofInt_mod]
    rw [← bitvec_ofInt_toSigned width positive _ leftRange.1 leftRange.2,
      ← bitvec_ofInt_toSigned width positive _ rightRange.1 rightRange.2]
    by_cases zero : (BitVec.ofInt width (right.evalAt env width)).toInt = 0
    · have boolean : ((BitVec.ofInt width (right.evalAt env width)).toInt == 0) = true := by
        simpa only [beq_iff_eq] using zero
      rw [boolean]
      simp only [if_true]
      rw [← bitvec_srem_ofInt positive, zero, Int.tmod_zero, word_of_signed positive]
    · have boolean : ((BitVec.ofInt width (right.evalAt env width)).toInt == 0) = false := by
        apply Bool.eq_false_iff.mpr
        intro equal
        exact zero (eq_of_beq equal)
      rw [boolean]
      simp only [Bool.false_eq_true, if_false]
      exact bitvec_srem_ofInt positive _ _
  }

/-- Actual successful bvSDiv requests retain the complete core integer result,
including zero divisors and signed overflow, at their own admitted width. -/
theorem toSMTRequest_bvSDiv_value (width : Nat) (left right : TrustIrExpr)
    (request : SMTRequest) (built : (.bvSDiv left right : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    Int.ofNat (BitVec.smtSDiv (BitVec.ofInt request.width (left.evalAt env request.width))
      (BitVec.ofInt request.width (right.evalAt env request.width))).toNat =
      (.bvSDiv left right : TrustIrExpr).evalAt env request.width := by
  have metadata := toSMTRequest_metadata (.bvSDiv left right) width request built
  rw [metadata.1]
  have typed := toSMTRequest_sorted (.bvSDiv left right) width request built
  generalize request.sort = sort at typed
  cases typed with
  | bvSDiv leftTyped rightTyped =>
    rw [← bvSDiv_bitvec width metadata.2.1 left right leftTyped rightTyped]
    exact (SMTSorted.bvSDiv leftTyped rightTyped).bitvec_ofInt_exact env

/-- Actual successful bvSRem requests retain the complete core integer result,
including zero divisors and signed overflow, at their own admitted width. -/
theorem toSMTRequest_bvSRem_value (width : Nat) (left right : TrustIrExpr)
    (request : SMTRequest) (built : (.bvSRem left right : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    Int.ofNat (BitVec.srem (BitVec.ofInt request.width (left.evalAt env request.width))
      (BitVec.ofInt request.width (right.evalAt env request.width))).toNat =
      (.bvSRem left right : TrustIrExpr).evalAt env request.width := by
  have metadata := toSMTRequest_metadata (.bvSRem left right) width request built
  rw [metadata.1]
  have typed := toSMTRequest_sorted (.bvSRem left right) width request built
  generalize request.sort = sort at typed
  cases typed with
  | bvSRem leftTyped rightTyped =>
    rw [← bvSRem_bitvec width metadata.2.1 left right leftTyped rightTyped]
    exact (SMTSorted.bvSRem leftTyped rightTyped).bitvec_ofInt_exact env

end TrustIr.TrustIrExpr

/-- info: 'TrustIr.TrustIrExpr.bitvec_signed_magnitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.bitvec_signed_magnitude

/-- info: 'TrustIr.TrustIrExpr.bitvec_sdiv_ofInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.bitvec_sdiv_ofInt

/-- info: 'TrustIr.TrustIrExpr.bitvec_srem_ofInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.bitvec_srem_ofInt

/-- info: 'TrustIr.TrustIrExpr.bitvec_toInt_negative_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.bitvec_toInt_negative_iff

/-- info: 'TrustIr.TrustIrExpr.bitvec_smtSDiv_ofInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.bitvec_smtSDiv_ofInt

/-- info: 'TrustIr.TrustIrExpr.bvSDiv_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.bvSDiv_bitvec

/-- info: 'TrustIr.TrustIrExpr.bvSRem_bitvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.bvSRem_bitvec

/-- info: 'TrustIr.TrustIrExpr.toSMTRequest_bvSDiv_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.toSMTRequest_bvSDiv_value

/-- info: 'TrustIr.TrustIrExpr.toSMTRequest_bvSRem_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.toSMTRequest_bvSRem_value

