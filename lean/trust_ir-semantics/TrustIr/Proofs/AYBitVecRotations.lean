-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYBitVecShifts

namespace TrustIr.TrustIrExpr

private theorem or_comm (left right : Nat) : left ||| right = right ||| left := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_or, Bool.or_comm]

private theorem rotate_sum_eq_or (value width shift : Nat) (small : shift ≤ width)
    (bound : value < 2 ^ width) :
    (value * 2 ^ shift) % 2 ^ width + value / 2 ^ (width - shift) =
      ((value * 2 ^ shift) % 2 ^ width) ||| (value / 2 ^ (width - shift)) := by
  have factor : (2 : Nat) ^ width = 2 ^ (width - shift) * 2 ^ shift := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have bound' : value < 2 ^ (width - shift) * 2 ^ shift := by
    rw [← factor]
    exact bound
  have quotient : value / 2 ^ (width - shift) < 2 ^ shift :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by simpa only [Nat.mul_comm] using bound')
  rw [factor, Nat.mul_mod_mul_right]
  trustIrCompilerProof {
    simpa only [Nat.mul_comm] using
      Nat.mul_add_lt_is_or quotient (value % 2 ^ (width - shift))
  } {
    simpa only [Nat.mul_comm] using
      Nat.two_pow_add_eq_or_of_lt quotient (value % 2 ^ (width - shift))
  }

/-- Actual arithmetic left rotation is exactly core shift-and-OR rotation
at the reduced amount; the two pieces are proved to occupy disjoint bit ranges. -/
theorem rotlWidth_bitvec {width : Nat} (positive : 0 < width) (word : BitVec width) (amount : Nat) :
    rotlWidth word.toNat width amount = (BitVec.rotateLeft word (amount % width)).toNat := by
  trustIrCompilerProof {
  rw [BitVec.rotateLeft, BitVec.toNat_or, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  } {
    rw [BitVec.rotateLeft_def, Nat.mod_mod, BitVec.toNat_or, BitVec.toNat_shiftLeft,
      BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  }
  exact rotate_sum_eq_or word.toNat width (amount % width)
    (Nat.le_of_lt (Nat.mod_lt amount positive)) word.isLt

/-- Actual arithmetic right rotation is exactly core shift-and-OR rotation
at the reduced amount, retaining the complementary restart boundary. -/
theorem rotrWidth_bitvec {width : Nat} (positive : 0 < width) (word : BitVec width) (amount : Nat) :
    rotrWidth word.toNat width amount = (BitVec.rotateRight word (amount % width)).toNat := by
  trustIrCompilerProof {
  rw [BitVec.rotateRight, BitVec.toNat_or, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  } {
    rw [BitVec.rotateRight_def, Nat.mod_mod, BitVec.toNat_or, BitVec.toNat_shiftLeft,
      BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  }
  have small := Nat.mod_lt amount positive
  have complement : width - (width - amount % width) = amount % width := by omega
  have result := rotate_sum_eq_or word.toNat width (width - amount % width) (by omega) word.isLt
  rw [complement] at result
  simpa only [rotrWidth, Nat.add_comm, or_comm] using result

/-- Typed left-rotation expressions retain the complete core unsigned result. -/
theorem bvRotL_bitvec_value (width : Nat) (positive : 0 < width) (left right : TrustIrExpr)
    (leftTyped : SMTSorted width left (.bv width))
    (rightTyped : SMTSorted width right (.bv width)) (env : SMTEnv) :
    Int.ofNat (BitVec.rotateLeft (BitVec.ofInt width (left.evalAt env width))
      ((BitVec.ofInt width (right.evalAt env width)).toNat % width)).toNat =
      (.bvRotL left right : TrustIrExpr).evalAt env width := by
  have leftRange := SMTSorted.eval_value_valid width left (.bv width) leftTyped env
  have rightRange := SMTSorted.eval_value_valid width right (.bv width) rightTyped env
  have li := bitvec_ofInt_toNat width _ leftRange.1 leftRange.2
  have ri := bitvec_ofInt_toNat width _ rightRange.1 rightRange.2
  have ln := congrArg (fun z : Int => z.toNat) li
  have rn := congrArg (fun z : Int => z.toNat) ri
  change (BitVec.ofInt width (left.evalAt env width)).toNat = (left.evalAt env width).toNat at ln
  change (BitVec.ofInt width (right.evalAt env width)).toNat = (right.evalAt env width).toNat at rn
  change Int.ofNat (BitVec.rotateLeft _ (_ % width)).toNat = Int.ofNat (rotlWidth _ width _)
  rw [← rotlWidth_bitvec positive, ln, rn]

/-- Typed right-rotation expressions retain the complete core unsigned result. -/
theorem bvRotR_bitvec_value (width : Nat) (positive : 0 < width) (left right : TrustIrExpr)
    (leftTyped : SMTSorted width left (.bv width))
    (rightTyped : SMTSorted width right (.bv width)) (env : SMTEnv) :
    Int.ofNat (BitVec.rotateRight (BitVec.ofInt width (left.evalAt env width))
      ((BitVec.ofInt width (right.evalAt env width)).toNat % width)).toNat =
      (.bvRotR left right : TrustIrExpr).evalAt env width := by
  have leftRange := SMTSorted.eval_value_valid width left (.bv width) leftTyped env
  have rightRange := SMTSorted.eval_value_valid width right (.bv width) rightTyped env
  have li := bitvec_ofInt_toNat width _ leftRange.1 leftRange.2
  have ri := bitvec_ofInt_toNat width _ rightRange.1 rightRange.2
  have ln := congrArg (fun z : Int => z.toNat) li
  have rn := congrArg (fun z : Int => z.toNat) ri
  change (BitVec.ofInt width (left.evalAt env width)).toNat = (left.evalAt env width).toNat at ln
  change (BitVec.ofInt width (right.evalAt env width)).toNat = (right.evalAt env width).toNat at rn
  change Int.ofNat (BitVec.rotateRight _ (_ % width)).toNat = Int.ofNat (rotrWidth _ width _)
  rw [← rotrWidth_bitvec positive, ln, rn]

private theorem width_fits (width : Nat) : width < 2 ^ width := by
  induction width with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    have positive := Nat.two_pow_pos n
    omega

private theorem expansion_amounts {width : Nat} (positive : 0 < width) (amount : BitVec width) :
    (BitVec.umod amount (BitVec.ofNat width width)).toNat = amount.toNat % width ∧
    ((BitVec.ofNat width width) - (BitVec.umod amount (BitVec.ofNat width width))).toNat =
      width - amount.toNat % width := by
  have widthNat : (BitVec.ofNat width width).toNat = width := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (width_fits width)]
  have shiftNat : (BitVec.umod amount (BitVec.ofNat width width)).toNat = amount.toNat % width := by
    change amount.toNat % (BitVec.ofNat width width).toNat = _
    rw [widthNat]
  refine ⟨shiftNat, ?_⟩
  rw [BitVec.toNat_sub, widthNat, shiftNat]
  have small := Nat.mod_lt amount.toNat positive
  have _bound := width_fits width
  have algebra : width + (2 ^ width - amount.toNat % width) =
      (width - amount.toNat % width) + 2 ^ width := by omega
  trustIrCompilerProof { skip } {
    rw [Nat.add_comm (2 ^ width - amount.toNat % width) width]
  }
  rw [algebra, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- Core meaning of the exact remainder/subtract/shift/OR pattern emitted for
left rotation. In particular the width numeral and complementary amount fit. -/
theorem bitvec_rotateLeft_expansion {width : Nat} (positive : 0 < width)
    (word amount : BitVec width) :
    BitVec.rotateLeft word (amount.toNat % width) =
      let modulus := BitVec.ofNat width width
      let shift := BitVec.umod amount modulus
      (word <<< shift) ||| (word >>> (modulus - shift)) := by
  have amounts := expansion_amounts positive amount
  trustIrCompilerProof { skip } { rw [BitVec.rotateLeft_def, Nat.mod_mod] }
  change (word <<< (amount.toNat % width)) ||| (word >>> (width - amount.toNat % width)) =
    (word <<< (BitVec.umod amount (BitVec.ofNat width width)).toNat) |||
      (word >>> ((BitVec.ofNat width width) - (BitVec.umod amount (BitVec.ofNat width width))).toNat)
  rw [amounts.1, amounts.2]

/-- Core meaning of the exact emitted right-rotation operator pattern. -/
theorem bitvec_rotateRight_expansion {width : Nat} (positive : 0 < width)
    (word amount : BitVec width) :
    BitVec.rotateRight word (amount.toNat % width) =
      let modulus := BitVec.ofNat width width
      let shift := BitVec.umod amount modulus
      (word >>> shift) ||| (word <<< (modulus - shift)) := by
  have amounts := expansion_amounts positive amount
  trustIrCompilerProof { skip } { rw [BitVec.rotateRight_def, Nat.mod_mod] }
  change (word >>> (amount.toNat % width)) ||| (word <<< (width - amount.toNat % width)) =
    (word >>> (BitVec.umod amount (BitVec.ofNat width width)).toNat) |||
      (word <<< ((BitVec.ofNat width width) - (BitVec.umod amount (BitVec.ofNat width width))).toNat)
  rw [amounts.1, amounts.2]

/-- Actual successful bvRotL requests retain the exact core rotation result. -/
theorem toSMTRequest_bvRotL_value (width : Nat) (left right : TrustIrExpr)
    (request : SMTRequest) (built : (.bvRotL left right : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    Int.ofNat (BitVec.rotateLeft (BitVec.ofInt request.width (left.evalAt env request.width))
      ((BitVec.ofInt request.width (right.evalAt env request.width)).toNat % request.width)).toNat =
      (.bvRotL left right : TrustIrExpr).evalAt env request.width := by
  have metadata := toSMTRequest_metadata (.bvRotL left right) width request built
  rw [metadata.1]
  have typed := toSMTRequest_sorted (.bvRotL left right) width request built
  generalize request.sort = sort at typed
  cases typed with
  | bvRotL leftTyped rightTyped =>
    exact bvRotL_bitvec_value width metadata.2.1 left right leftTyped rightTyped env

/-- The actual bvRotL request's result agrees with the expanded core operator
pattern used by its renderer; no output or model-answer premise is supplied. -/
theorem toSMTRequest_bvRotL_expanded_value (width : Nat) (left right : TrustIrExpr)
    (request : SMTRequest) (built : (.bvRotL left right : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    let word := BitVec.ofInt request.width (left.evalAt env request.width)
    let amount := BitVec.ofInt request.width (right.evalAt env request.width)
    let modulus := BitVec.ofNat request.width request.width
    let shift := BitVec.umod amount modulus
    Int.ofNat ((word <<< shift) ||| (word >>> (modulus - shift))).toNat =
      (.bvRotL left right : TrustIrExpr).evalAt env request.width := by
  have metadata := toSMTRequest_metadata (.bvRotL left right) width request built
  have positive : 0 < request.width := by rw [metadata.1]; exact metadata.2.1
  have expansion := bitvec_rotateLeft_expansion positive
    (BitVec.ofInt request.width (left.evalAt env request.width))
    (BitVec.ofInt request.width (right.evalAt env request.width))
  change Int.ofNat _ = _
  rw [← expansion]
  exact toSMTRequest_bvRotL_value width left right request built env

/-- Actual successful bvRotR requests retain the exact core rotation result. -/
theorem toSMTRequest_bvRotR_value (width : Nat) (left right : TrustIrExpr)
    (request : SMTRequest) (built : (.bvRotR left right : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    Int.ofNat (BitVec.rotateRight (BitVec.ofInt request.width (left.evalAt env request.width))
      ((BitVec.ofInt request.width (right.evalAt env request.width)).toNat % request.width)).toNat =
      (.bvRotR left right : TrustIrExpr).evalAt env request.width := by
  have metadata := toSMTRequest_metadata (.bvRotR left right) width request built
  rw [metadata.1]
  have typed := toSMTRequest_sorted (.bvRotR left right) width request built
  generalize request.sort = sort at typed
  cases typed with
  | bvRotR leftTyped rightTyped =>
    exact bvRotR_bitvec_value width metadata.2.1 left right leftTyped rightTyped env

/-- The actual bvRotR request's result agrees with the expanded core operator
pattern used by its renderer; no output or model-answer premise is supplied. -/
theorem toSMTRequest_bvRotR_expanded_value (width : Nat) (left right : TrustIrExpr)
    (request : SMTRequest) (built : (.bvRotR left right : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    let word := BitVec.ofInt request.width (left.evalAt env request.width)
    let amount := BitVec.ofInt request.width (right.evalAt env request.width)
    let modulus := BitVec.ofNat request.width request.width
    let shift := BitVec.umod amount modulus
    Int.ofNat ((word >>> shift) ||| (word <<< (modulus - shift))).toNat =
      (.bvRotR left right : TrustIrExpr).evalAt env request.width := by
  have metadata := toSMTRequest_metadata (.bvRotR left right) width request built
  have positive : 0 < request.width := by rw [metadata.1]; exact metadata.2.1
  have expansion := bitvec_rotateRight_expansion positive
    (BitVec.ofInt request.width (left.evalAt env request.width))
    (BitVec.ofInt request.width (right.evalAt env request.width))
  change Int.ofNat _ = _
  rw [← expansion]
  exact toSMTRequest_bvRotR_value width left right request built env

end TrustIr.TrustIrExpr

#trustIrAxiomsPinned TrustIr.TrustIrExpr.rotlWidth_bitvec == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.rotrWidth_bitvec == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bvRotL_bitvec_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bvRotR_bitvec_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bitvec_rotateLeft_expansion == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bitvec_rotateRight_expansion == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_bvRotL_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_bvRotR_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_bvRotL_expanded_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_bvRotR_expanded_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
