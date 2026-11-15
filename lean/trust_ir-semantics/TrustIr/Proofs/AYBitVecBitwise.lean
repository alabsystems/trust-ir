-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYBitVecArithmetic
import TrustIr.BitVecBounds

namespace TrustIr.TrustIrExpr
trustIrBitVec430 local instance {n : Nat} : OrOp (BitVec n) := ⟨TrustIr.BitVecCompat.bitOr⟩
trustIrBitVec430 local instance {n : Nat} : XorOp (BitVec n) := ⟨TrustIr.BitVecCompat.bitXor⟩

private theorem canonical_toNat (width : Nat) (value : Int)
    (range : 0 ≤ value ∧ value < (2 : Int) ^ width) :
    (BitVec.ofInt width value).toNat = value.toNat := by
  have integer := bitvec_ofInt_toNat width value range.1 range.2
  have natural := congrArg (fun z : Int => z.toNat) integer
  exact natural

/-- Canonical integer and agrees with the core BitVec operation, as an
exact integer result rather than a potentially lossy modular conversion. -/
theorem bitvec_and_value (width : Nat) (left right : Int)
    (leftRange : 0 ≤ left ∧ left < (2 : Int) ^ width)
    (rightRange : 0 ≤ right ∧ right < (2 : Int) ^ width) :
    Int.ofNat ((BitVec.ofInt width left) &&& (BitVec.ofInt width right)).toNat =
      Int.land left right := by
  rw [BitVec.toNat_and, canonical_toNat width left leftRange,
    canonical_toNat width right rightRange]
  cases left with
  | negSucc n => have impossible := leftRange.1; simp only [Int.negSucc_not_nonneg] at impossible
  | ofNat a =>
    cases right with
    | negSucc n => have impossible := rightRange.1; simp only [Int.negSucc_not_nonneg] at impossible
    | ofNat b => rfl

/-- Canonical integer or agrees with the core BitVec operation, as an
exact integer result rather than a potentially lossy modular conversion. -/
theorem bitvec_or_value (width : Nat) (left right : Int)
    (leftRange : 0 ≤ left ∧ left < (2 : Int) ^ width)
    (rightRange : 0 ≤ right ∧ right < (2 : Int) ^ width) :
    Int.ofNat ((BitVec.ofInt width left) ||| (BitVec.ofInt width right)).toNat =
      Int.lor left right := by
  trustIrCompilerProof {
  rw [BitVec.toNat_or, canonical_toNat width left leftRange,
    canonical_toNat width right rightRange]
  } {
    change Int.ofNat (TrustIr.BitVecCompat.bitOr (BitVec.ofInt width left) (BitVec.ofInt width right)).toNat = Int.lor left right
    rw [TrustIr.BitVecCompat.toNat_bitOr, canonical_toNat width left leftRange,
      canonical_toNat width right rightRange]
  }
  cases left with
  | negSucc n => have impossible := leftRange.1; simp only [Int.negSucc_not_nonneg] at impossible
  | ofNat a =>
    cases right with
    | negSucc n => have impossible := rightRange.1; simp only [Int.negSucc_not_nonneg] at impossible
    | ofNat b => rfl

/-- Canonical integer xor agrees with the core BitVec operation, as an
exact integer result rather than a potentially lossy modular conversion. -/
theorem bitvec_xor_value (width : Nat) (left right : Int)
    (leftRange : 0 ≤ left ∧ left < (2 : Int) ^ width)
    (rightRange : 0 ≤ right ∧ right < (2 : Int) ^ width) :
    Int.ofNat ((BitVec.ofInt width left) ^^^ (BitVec.ofInt width right)).toNat =
      Int.xor left right := by
  trustIrCompilerProof {
  rw [BitVec.toNat_xor, canonical_toNat width left leftRange,
    canonical_toNat width right rightRange]
  } {
    change Int.ofNat (TrustIr.BitVecCompat.bitXor (BitVec.ofInt width left) (BitVec.ofInt width right)).toNat = Int.xor left right
    rw [TrustIr.BitVecCompat.toNat_bitXor, canonical_toNat width left leftRange,
      canonical_toNat width right rightRange]
  }
  cases left with
  | negSucc n => have impossible := leftRange.1; simp only [Int.negSucc_not_nonneg] at impossible
  | ofNat a =>
    cases right with
    | negSucc n => have impossible := rightRange.1; simp only [Int.negSucc_not_nonneg] at impossible
    | ofNat b => rfl

/-- The actual word mask yields exactly core BitVec complement. -/
theorem bitvec_not_value (width : Nat) (value : Int)
    (range : 0 ≤ value ∧ value < (2 : Int) ^ width) :
    Int.ofNat (~~~(BitVec.ofInt width value)).toNat = Int.xor value ((2 : Int) ^ width - 1) := by
  rw [BitVec.not_def, BitVec.toNat_xor, BitVec.toNat_allOnes,
    canonical_toNat width value range, Int.xor_comm]
  have power : ((2 ^ width : Nat) : Int) = (2 : Int) ^ width := Int.natCast_pow 2 width
  have mask : (2 : Int) ^ width - 1 = Int.ofNat (2 ^ width - 1) := by
    rw [← power]
    exact (Int.ofNat_sub (Nat.two_pow_pos width)).symm
  rw [mask]
  cases value with
  | negSucc n => have impossible := range.1; simp only [Int.negSucc_not_nonneg] at impossible
  | ofNat a => rfl

/-- Typing derives both operand carriers for exact and expression semantics. -/
theorem bvAnd_bitvec_value (width : Nat) (left right : TrustIrExpr)
    (leftTyped : SMTSorted width left (.bv width))
    (rightTyped : SMTSorted width right (.bv width)) (env : SMTEnv) :
    Int.ofNat ((BitVec.ofInt width (left.evalAt env width)) &&&
      (BitVec.ofInt width (right.evalAt env width))).toNat =
      (.bvAnd left right : TrustIrExpr).evalAt env width := by
  exact bitvec_and_value width _ _ (SMTSorted.eval_value_valid width left (.bv width) leftTyped env) (SMTSorted.eval_value_valid width right (.bv width) rightTyped env)

/-- The exact and result is preserved at the actual emitted request width. -/
theorem toSMTRequest_bvAnd_value (width : Nat) (left right : TrustIrExpr)
    (request : SMTRequest) (built : (.bvAnd left right : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    Int.ofNat ((BitVec.ofInt request.width (left.evalAt env request.width)) &&&
      (BitVec.ofInt request.width (right.evalAt env request.width))).toNat =
      (.bvAnd left right : TrustIrExpr).evalAt env request.width := by
  have metadata := toSMTRequest_metadata (.bvAnd left right) width request built
  rw [metadata.1]
  have typed := toSMTRequest_sorted (.bvAnd left right) width request built
  generalize request.sort = sort at typed
  cases typed with
  | bvAnd leftTyped rightTyped => exact bvAnd_bitvec_value width left right leftTyped rightTyped env

/-- Typing derives both operand carriers for exact or expression semantics. -/
theorem bvOr_bitvec_value (width : Nat) (left right : TrustIrExpr)
    (leftTyped : SMTSorted width left (.bv width))
    (rightTyped : SMTSorted width right (.bv width)) (env : SMTEnv) :
    Int.ofNat ((BitVec.ofInt width (left.evalAt env width)) |||
      (BitVec.ofInt width (right.evalAt env width))).toNat =
      (.bvOr left right : TrustIrExpr).evalAt env width := by
  exact bitvec_or_value width _ _ (SMTSorted.eval_value_valid width left (.bv width) leftTyped env) (SMTSorted.eval_value_valid width right (.bv width) rightTyped env)

/-- The exact or result is preserved at the actual emitted request width. -/
theorem toSMTRequest_bvOr_value (width : Nat) (left right : TrustIrExpr)
    (request : SMTRequest) (built : (.bvOr left right : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    Int.ofNat ((BitVec.ofInt request.width (left.evalAt env request.width)) |||
      (BitVec.ofInt request.width (right.evalAt env request.width))).toNat =
      (.bvOr left right : TrustIrExpr).evalAt env request.width := by
  have metadata := toSMTRequest_metadata (.bvOr left right) width request built
  rw [metadata.1]
  have typed := toSMTRequest_sorted (.bvOr left right) width request built
  generalize request.sort = sort at typed
  cases typed with
  | bvOr leftTyped rightTyped => exact bvOr_bitvec_value width left right leftTyped rightTyped env

/-- Typing derives both operand carriers for exact xor expression semantics. -/
theorem bvXor_bitvec_value (width : Nat) (left right : TrustIrExpr)
    (leftTyped : SMTSorted width left (.bv width))
    (rightTyped : SMTSorted width right (.bv width)) (env : SMTEnv) :
    Int.ofNat ((BitVec.ofInt width (left.evalAt env width)) ^^^
      (BitVec.ofInt width (right.evalAt env width))).toNat =
      (.bvXor left right : TrustIrExpr).evalAt env width := by
  exact bitvec_xor_value width _ _ (SMTSorted.eval_value_valid width left (.bv width) leftTyped env) (SMTSorted.eval_value_valid width right (.bv width) rightTyped env)

/-- The exact xor result is preserved at the actual emitted request width. -/
theorem toSMTRequest_bvXor_value (width : Nat) (left right : TrustIrExpr)
    (request : SMTRequest) (built : (.bvXor left right : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    Int.ofNat ((BitVec.ofInt request.width (left.evalAt env request.width)) ^^^
      (BitVec.ofInt request.width (right.evalAt env request.width))).toNat =
      (.bvXor left right : TrustIrExpr).evalAt env request.width := by
  have metadata := toSMTRequest_metadata (.bvXor left right) width request built
  rw [metadata.1]
  have typed := toSMTRequest_sorted (.bvXor left right) width request built
  generalize request.sort = sort at typed
  cases typed with
  | bvXor leftTyped rightTyped => exact bvXor_bitvec_value width left right leftTyped rightTyped env

/-- Typing derives the operand carrier for exact complement semantics. -/
theorem bvNot_bitvec_value (width : Nat) (arg : TrustIrExpr)
    (argTyped : SMTSorted width arg (.bv width)) (env : SMTEnv) :
    Int.ofNat (~~~(BitVec.ofInt width (arg.evalAt env width))).toNat =
      (.bvNot arg : TrustIrExpr).evalAt env width := by
  exact bitvec_not_value width _ (SMTSorted.eval_value_valid width arg (.bv width) argTyped env)

/-- Actual successful complement requests retain the exact core result. -/
theorem toSMTRequest_bvNot_value (width : Nat) (arg : TrustIrExpr)
    (request : SMTRequest) (built : (.bvNot arg : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    Int.ofNat (~~~(BitVec.ofInt request.width (arg.evalAt env request.width))).toNat =
      (.bvNot arg : TrustIrExpr).evalAt env request.width := by
  have metadata := toSMTRequest_metadata (.bvNot arg) width request built
  rw [metadata.1]
  have typed := toSMTRequest_sorted (.bvNot arg) width request built
  generalize request.sort = sort at typed
  cases typed with
  | bvNot argTyped => exact bvNot_bitvec_value width arg argTyped env

end TrustIr.TrustIrExpr

/-- info: 'TrustIr.TrustIrExpr.bitvec_and_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.bitvec_and_value

/-- info: 'TrustIr.TrustIrExpr.bitvec_or_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.bitvec_or_value

/-- info: 'TrustIr.TrustIrExpr.bitvec_xor_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.bitvec_xor_value

/-- info: 'TrustIr.TrustIrExpr.bitvec_not_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.bitvec_not_value

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bvAnd_bitvec_value == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bvOr_bitvec_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bvXor_bitvec_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bvNot_bitvec_value == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_bvAnd_value == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_bvOr_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_bvXor_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_bvNot_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

