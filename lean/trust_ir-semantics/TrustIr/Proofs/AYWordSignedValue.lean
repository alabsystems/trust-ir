-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYWordWires

namespace TrustIr.AYGateCNF
theorem word_ofInt_nat (width value : Nat) :
    BitVec.ofInt width (Int.ofNat value) = BitVec.ofNat width value := by
  trustIrCompilerProof {
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt]
    change ((value : Int) % ((2^width : Nat) : Int)).toNat = value % 2^width
    rw [← Int.ofNat_emod]
    rfl
  } {
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt]
    change ((value : Int) % ((2^width : Nat) : Int)).toNat = value % 2^width
    rw [← Int.natCast_emod]
    rfl
  }

theorem word_ofInt_negSucc (width value : Nat) (bound : value < 2^width) :
    BitVec.ofInt width (Int.negSucc value) = ~~~(BitVec.ofNat width value) := by
  trustIrCompilerProof {
    have difference : ((2^width : Nat) : Int) - ((value : Int) + 1) = ((2^width - 1 - value : Nat) : Int) := by omega
    have small : 2^width - 1 - value < 2^width := by omega
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofInt, Int.negSucc_eq, Int.neg_emod, difference,
      ← Int.ofNat_emod, Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt bound]
  } {
    exact BitVec.ofInt_negSucc_eq_not_ofNat
  }

theorem word_signExtend {source : Nat} (target : Nat) (word : BitVec source) (wide : source ≤ target) :
    word.signExtend target =
      if word.msb then ~~~((~~~word).zeroExtend target) else word.zeroExtend target := by
  trustIrCompilerProof {
    cases source with
    | zero =>
      have empty : word.toNat = 0 := by have bound := word.isLt; simp at bound; omega
      simp [BitVec.signExtend, BitVec.toInt, empty, BitVec.msb, BitVec.getMsb,
        word_ofInt_nat, BitVec.zeroExtend, BitVec.zeroExtend', BitVec.truncate]
      apply BitVec.eq_of_toNat_eq
      simp
    | succ source =>
      have valid := word.isLt
      by_cases sign : word.msb = true
      · have high := BitVec.toNat_ge_of_msb_true sign
        simp only [Nat.add_sub_cancel] at high
        have negative : ¬ 2 * word.toNat < 2^(source+1) := by omega
        have original : word.toInt = Int.negSucc (2^(source+1)-1-word.toNat) := by
          simp only [BitVec.toInt, if_neg negative, Int.negSucc_eq]
          omega
        have small : 2^(source+1)-1-word.toNat < 2^target := by
          have powers : 2^(source+1) ≤ 2^target := Nat.pow_le_pow_right (by decide) wide
          omega
        simp only [sign, Bool.true_eq, ite_true, BitVec.signExtend, original]
        rw [word_ofInt_negSucc _ _ small]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp
      · have low : word.toNat < 2^source := by simpa [BitVec.msb_eq_decide] using sign
        have positive : 2 * word.toNat < 2^(source+1) := by omega
        have original : word.toInt = Int.ofNat word.toNat := by simp [BitVec.toInt, positive]
        simp only [show word.msb = false by cases h : word.msb <;> simp_all,
          Bool.false_eq_true, ite_false, BitVec.signExtend, original]
        rw [word_ofInt_nat]
        apply BitVec.eq_of_toNat_eq
        simp
  } {
    cases sign : word.msb with
    | false => simpa only [sign, Bool.false_eq_true, ite_false] using
        (BitVec.signExtend_eq_setWidth_of_msb_false (v := target) sign)
    | true => simpa only [sign, ite_true] using
        (BitVec.signExtend_eq_not_setWidth_not_of_msb_true (v := target) sign)
  }

end TrustIr.AYGateCNF

#trustIrAxiomsExact TrustIr.AYGateCNF.word_ofInt_nat == [propext]

#trustIrAxiomsExact TrustIr.AYGateCNF.word_ofInt_negSucc == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.word_signExtend == [propext, Classical.choice, Quot.sound]
