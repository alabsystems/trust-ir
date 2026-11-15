-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYBitVecSignedDiv

namespace TrustIr.TrustIrExpr

private theorem ofInt_nat (width value : Nat) :
    BitVec.ofInt width (value : Int) = BitVec.ofNat width value := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt]
  change ((value : Int) % ((2 ^ width : Nat) : Int)).toNat = value % 2 ^ width
  trustIrCompilerProof { rw [← Int.ofNat_emod]; rfl } { rfl }

/-- Core left shift is the modular power-of-two product at every amount. -/
theorem bitvec_shiftLeft_ofInt {width : Nat} (word : BitVec width) (amount : Nat) :
    BitVec.ofInt width ((word.toNat : Int) * (2 : Int) ^ amount) = word <<< amount := by
  have power : ((2 ^ amount : Nat) : Int) = (2 : Int) ^ amount := Int.natCast_pow 2 amount
  rw [← power, ← Int.natCast_mul, ofInt_nat]
  change BitVec.ofNat width (word.toNat * 2 ^ amount) = BitVec.ofNat width (word.toNat <<< amount)
  rw [Nat.shiftLeft_eq]

/-- Core logical right shift retains the exact natural quotient as a word. -/
theorem bitvec_ushiftRight_ofInt {width : Nat} (word : BitVec width) (amount : Nat) :
    BitVec.ofInt width ((word.toNat : Int) / (2 : Int) ^ amount) = word >>> amount := by
  have power : ((2 ^ amount : Nat) : Int) = (2 : Int) ^ amount := Int.natCast_pow 2 amount
  trustIrCompilerProof
    { rw [← power, ← Int.ofNat_ediv, ofInt_nat] }
    { rw [← power, ← Int.natCast_ediv, ofInt_nat] }
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have bound := (word >>> amount).isLt
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at bound
  exact Nat.mod_eq_of_lt bound

/-- Core left shifts at or beyond the width are zero. -/
theorem bitvec_shiftLeft_large {width : Nat} (word : BitVec width) (amount : Nat)
    (large : width ≤ amount) : word <<< amount = 0 := by
  have factor : (2 : Nat) ^ amount = 2 ^ width * 2 ^ (amount - width) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  apply BitVec.eq_of_toNat_eq
  change (word <<< amount).toNat = (BitVec.ofNat width 0).toNat
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, factor, BitVec.toNat_ofNat, Nat.zero_mod]
  simp [Nat.mul_mod]

/-- Core logical right shifts at or beyond the width are zero. -/
theorem bitvec_ushiftRight_large {width : Nat} (word : BitVec width) (amount : Nat)
    (large : width ≤ amount) : word >>> amount = 0 := by
  have power : (2 : Nat) ^ width ≤ 2 ^ amount := by
    trustIrCompilerProof
      { exact Nat.pow_le_pow_of_le_right (by decide) large }
      { exact Nat.pow_le_pow_right (by decide) large }
  have bound : word.toNat < 2 ^ amount := Nat.lt_of_lt_of_le word.isLt power
  apply BitVec.eq_of_toNat_eq
  change (word >>> amount).toNat = (BitVec.ofNat width 0).toNat
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt bound,
    BitVec.toNat_ofNat, Nat.zero_mod]

/-- Integer arithmetic shift is floor division by the positive power of two. -/
theorem int_shiftRight_fdiv (value : Int) (amount : Nat) :
    value >>> amount = Int.fdiv value ((2 : Int) ^ amount) := by
  have power : (2 : Int) ^ amount = Int.ofNat (2 ^ amount) := (Int.natCast_pow 2 amount).symm
  rw [power]
  have positive := Nat.two_pow_pos amount
  cases naturalPower : (2 : Nat) ^ amount with
  | zero => rw [naturalPower] at positive; omega
  | succ k =>
    cases value with
    | ofNat n =>
      change Int.ofNat (n >>> amount) = Int.fdiv (Int.ofNat n) (Int.ofNat (k + 1))
      rw [Nat.shiftRight_eq_div_pow, naturalPower]
      exact Int.ofNat_fdiv n (k + 1)
    | negSucc n =>
      change Int.negSucc (n >>> amount) = Int.negSucc (n / (k + 1))
      rw [Nat.shiftRight_eq_div_pow, naturalPower]

private theorem signed_word_bound {width : Nat} (word : BitVec width) :
    -((2 ^ width : Nat) : Int) ≤ word.toInt ∧ word.toInt < ((2 ^ width : Nat) : Int) := by
  have bound := Int.ofNat_lt.mpr word.isLt
  have _nonnegative : (0 : Int) ≤ (word.toNat : Int) := Int.ofNat_nonneg _
  rw [BitVec.toInt]
  split <;> omega

/-- Oversized core arithmetic shifts are the exact signed-fill word. -/
theorem bitvec_sshiftRight_large {width : Nat} (word : BitVec width) (amount : Nat)
    (large : width ≤ amount) :
    BitVec.sshiftRight word amount =
      BitVec.ofInt width (if word.toInt < 0 then -1 else 0) := by
  have power : (2 : Nat) ^ width ≤ 2 ^ amount := by
    trustIrCompilerProof
      { exact Nat.pow_le_pow_of_le_right (by decide) large }
      { exact Nat.pow_le_pow_right (by decide) large }
  have bounds := signed_word_bound word
  rw [BitVec.sshiftRight]
  cases signed : word.toInt with
  | ofNat n =>
    rw [signed] at bounds
    change -((2 ^ width : Nat) : Int) ≤ (n : Int) ∧ (n : Int) < ((2 ^ width : Nat) : Int) at bounds
    have bound : n < 2 ^ amount := by omega
    have nonnegative : ¬ (Int.ofNat n < 0) := by
      change ¬ (n : Int) < 0
      have _h : (0 : Int) ≤ (n : Int) := Int.ofNat_nonneg n
      omega
    rw [if_neg nonnegative]
    change BitVec.ofInt width (Int.ofNat (n >>> amount)) = BitVec.ofInt width 0
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt bound]
    rfl
  | negSucc n =>
    rw [signed] at bounds
    change -((2 ^ width : Nat) : Int) ≤ -((n + 1 : Nat) : Int) ∧
      -((n + 1 : Nat) : Int) < ((2 ^ width : Nat) : Int) at bounds
    have bound : n < 2 ^ amount := by omega
    have negative : Int.negSucc n < 0 := by
      change -((n + 1 : Nat) : Int) < 0
      have _h : (0 : Int) < ((n + 1 : Nat) : Int) := by
        trustIrCompilerProof { exact Int.ofNat_pos.mpr (by omega) }
          { have positiveNat := Nat.zero_lt_succ n; omega }
      omega
    rw [if_pos negative]
    change BitVec.ofInt width (Int.negSucc (n >>> amount)) = BitVec.ofInt width (-1)
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt bound]
    rfl

private theorem ofInt_mod (width : Nat) (value : Int) :
    BitVec.ofInt width (value % (2 : Int) ^ width) = BitVec.ofInt width value := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  have power : ((2 ^ width : Nat) : Int) = (2 : Int) ^ width := Int.natCast_pow 2 width
  rw [power, Int.emod_emod]

private theorem ofInt_zero (width : Nat) : BitVec.ofInt width 0 = 0 := by
  change BitVec.ofInt width ((0 : Nat) : Int) = (0 : BitVec width)
  rw [ofInt_nat]
  rfl

/-- Actual guarded bvShl agrees with core word shifting for every typed operand. -/
theorem bvShl_bitvec (width : Nat) (left right : TrustIrExpr)
    (leftTyped : SMTSorted width left (.bv width))
    (rightTyped : SMTSorted width right (.bv width)) (env : SMTEnv) :
    BitVec.ofInt width ((.bvShl left right : TrustIrExpr).evalAt env width) =
      (BitVec.ofInt width (left.evalAt env width)) <<< (BitVec.ofInt width (right.evalAt env width)) := by
  have leftRange := SMTSorted.eval_value_valid width left (.bv width) leftTyped env
  have rightRange := SMTSorted.eval_value_valid width right (.bv width) rightTyped env
  have integer := bitvec_ofInt_toNat width _ rightRange.1 rightRange.2
  have natural := congrArg (fun z : Int => z.toNat) integer
  change (BitVec.ofInt width (right.evalAt env width)).toNat = (right.evalAt env width).toNat at natural
  change BitVec.ofInt width ((.bvShl left right : TrustIrExpr).evalAt env width) =
    (BitVec.ofInt width (left.evalAt env width)) <<< (BitVec.ofInt width (right.evalAt env width)).toNat
  rw [natural, bvShl_evalAt_semantics, truncateUnsigned, ofInt_mod]
  by_cases small : (right.evalAt env width).toNat < width
  · rw [if_pos small]
    have core := bitvec_shiftLeft_ofInt (BitVec.ofInt width (left.evalAt env width)) (right.evalAt env width).toNat
    have exactLeft : ((BitVec.ofInt width (left.evalAt env width)).toNat : Int) = left.evalAt env width :=
      bitvec_ofInt_toNat width _ leftRange.1 leftRange.2
    rw [exactLeft] at core
    exact core
  · rw [if_neg small, ofInt_zero, bitvec_shiftLeft_large _ _ (by omega)]

/-- Actual guarded bvLShr agrees with core word shifting for every typed operand. -/
theorem bvLShr_bitvec (width : Nat) (left right : TrustIrExpr)
    (leftTyped : SMTSorted width left (.bv width))
    (rightTyped : SMTSorted width right (.bv width)) (env : SMTEnv) :
    BitVec.ofInt width ((.bvLShr left right : TrustIrExpr).evalAt env width) =
      (BitVec.ofInt width (left.evalAt env width)) >>> (BitVec.ofInt width (right.evalAt env width)) := by
  have leftRange := SMTSorted.eval_value_valid width left (.bv width) leftTyped env
  have rightRange := SMTSorted.eval_value_valid width right (.bv width) rightTyped env
  have integer := bitvec_ofInt_toNat width _ rightRange.1 rightRange.2
  have natural := congrArg (fun z : Int => z.toNat) integer
  change (BitVec.ofInt width (right.evalAt env width)).toNat = (right.evalAt env width).toNat at natural
  change BitVec.ofInt width ((.bvLShr left right : TrustIrExpr).evalAt env width) =
    (BitVec.ofInt width (left.evalAt env width)) >>> (BitVec.ofInt width (right.evalAt env width)).toNat
  rw [natural, bvLShr_evalAt_semantics, truncateUnsigned, ofInt_mod]
  by_cases small : (right.evalAt env width).toNat < width
  · rw [if_pos small]
    have core := bitvec_ushiftRight_ofInt (BitVec.ofInt width (left.evalAt env width)) (right.evalAt env width).toNat
    have exactLeft : ((BitVec.ofInt width (left.evalAt env width)).toNat : Int) = left.evalAt env width :=
      bitvec_ofInt_toNat width _ leftRange.1 leftRange.2
    rw [exactLeft] at core
    exact core
  · rw [if_neg small, ofInt_zero, bitvec_ushiftRight_large _ _ (by omega)]

/-- Actual guarded arithmetic shifting agrees with core signed word shifting,
including oversized shifts of negative words. -/
theorem bvAShr_bitvec (width : Nat) (positive : 0 < width) (left right : TrustIrExpr)
    (leftTyped : SMTSorted width left (.bv width))
    (rightTyped : SMTSorted width right (.bv width)) (env : SMTEnv) :
    BitVec.ofInt width ((.bvAShr left right : TrustIrExpr).evalAt env width) =
      BitVec.sshiftRight (BitVec.ofInt width (left.evalAt env width))
        (BitVec.ofInt width (right.evalAt env width)).toNat := by
  have leftRange := SMTSorted.eval_value_valid width left (.bv width) leftTyped env
  have rightRange := SMTSorted.eval_value_valid width right (.bv width) rightTyped env
  have integer := bitvec_ofInt_toNat width _ rightRange.1 rightRange.2
  have natural := congrArg (fun z : Int => z.toNat) integer
  change (BitVec.ofInt width (right.evalAt env width)).toNat = (right.evalAt env width).toNat at natural
  rw [natural, bvAShr_evalAt_semantics, truncateUnsigned, ofInt_mod]
  rw [← bitvec_ofInt_toSigned width positive _ leftRange.1 leftRange.2]
  by_cases small : (right.evalAt env width).toNat < width
  · rw [if_pos small]
    change BitVec.ofInt width (Int.fdiv _ _) = BitVec.ofInt width (_ >>> _)
    rw [int_shiftRight_fdiv]
  · rw [if_neg small]
    exact (bitvec_sshiftRight_large _ _ (by omega)).symm

/-- Actual successful bvShl requests retain the complete core word result,
including oversized amounts, at the returned request width. -/
theorem toSMTRequest_bvShl_value (width : Nat) (left right : TrustIrExpr)
    (request : SMTRequest) (built : (.bvShl left right : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    Int.ofNat ((BitVec.ofInt request.width (left.evalAt env request.width)) <<< (BitVec.ofInt request.width (right.evalAt env request.width))).toNat =
      (.bvShl left right : TrustIrExpr).evalAt env request.width := by
  have metadata := toSMTRequest_metadata (.bvShl left right) width request built
  rw [metadata.1]
  have typed := toSMTRequest_sorted (.bvShl left right) width request built
  generalize request.sort = sort at typed
  cases typed with
  | bvShl leftTyped rightTyped =>
    rw [← bvShl_bitvec width left right leftTyped rightTyped env]
    exact (SMTSorted.bvShl leftTyped rightTyped).bitvec_ofInt_exact env

/-- Actual successful bvLShr requests retain the complete core word result,
including oversized amounts, at the returned request width. -/
theorem toSMTRequest_bvLShr_value (width : Nat) (left right : TrustIrExpr)
    (request : SMTRequest) (built : (.bvLShr left right : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    Int.ofNat ((BitVec.ofInt request.width (left.evalAt env request.width)) >>> (BitVec.ofInt request.width (right.evalAt env request.width))).toNat =
      (.bvLShr left right : TrustIrExpr).evalAt env request.width := by
  have metadata := toSMTRequest_metadata (.bvLShr left right) width request built
  rw [metadata.1]
  have typed := toSMTRequest_sorted (.bvLShr left right) width request built
  generalize request.sort = sort at typed
  cases typed with
  | bvLShr leftTyped rightTyped =>
    rw [← bvLShr_bitvec width left right leftTyped rightTyped env]
    exact (SMTSorted.bvLShr leftTyped rightTyped).bitvec_ofInt_exact env

/-- Actual successful bvAShr requests retain the complete core word result,
including oversized amounts, at the returned request width. -/
theorem toSMTRequest_bvAShr_value (width : Nat) (left right : TrustIrExpr)
    (request : SMTRequest) (built : (.bvAShr left right : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    Int.ofNat (BitVec.sshiftRight (BitVec.ofInt request.width (left.evalAt env request.width)) (BitVec.ofInt request.width (right.evalAt env request.width)).toNat).toNat =
      (.bvAShr left right : TrustIrExpr).evalAt env request.width := by
  have metadata := toSMTRequest_metadata (.bvAShr left right) width request built
  rw [metadata.1]
  have typed := toSMTRequest_sorted (.bvAShr left right) width request built
  generalize request.sort = sort at typed
  cases typed with
  | bvAShr leftTyped rightTyped =>
    rw [← bvAShr_bitvec width metadata.2.1 left right leftTyped rightTyped env]
    exact (SMTSorted.bvAShr leftTyped rightTyped).bitvec_ofInt_exact env

end TrustIr.TrustIrExpr

/-- info: 'TrustIr.TrustIrExpr.bitvec_shiftLeft_ofInt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.bitvec_shiftLeft_ofInt

/-- info: 'TrustIr.TrustIrExpr.bitvec_ushiftRight_ofInt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.bitvec_ushiftRight_ofInt

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bitvec_shiftLeft_large == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

/-- info: 'TrustIr.TrustIrExpr.bitvec_ushiftRight_large' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.bitvec_ushiftRight_large

#trustIrAxiomsPinned TrustIr.TrustIrExpr.int_shiftRight_fdiv == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bitvec_sshiftRight_large == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bvShl_bitvec == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bvLShr_bitvec == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bvAShr_bitvec == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_bvShl_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_bvLShr_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_bvAShr_value == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
