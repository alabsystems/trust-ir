-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYBitVecProps

namespace TrustIr.TrustIrExpr

private theorem power_positive (width : Nat) : (0 : Int) < 2 ^ width := by
  have power : (2 : Int) ^ width = ((2 ^ width : Nat) : Int) := (Int.natCast_pow 2 width).symm
  rw [power]
  trustIrCompilerProof
    { exact Int.ofNat_pos.mpr (Nat.two_pow_pos width) }
    { exact Int.natCast_pos.mpr (Nat.two_pow_pos width) }

private theorem bitvec_unsigned (width : Nat) (value : Int) :
    ((BitVec.ofInt width value).toNat : Int) = value % (2 : Int) ^ width := by
  rw [BitVec.toNat_ofInt]
  have power : ((2 ^ width : Nat) : Int) = (2 : Int) ^ width := Int.natCast_pow 2 width
  rw [power]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by have h := power_positive width; omega))

/-- Negation commutes with the pinned core's integer-to-word conversion. -/
theorem bitvec_ofInt_neg (width : Nat) (value : Int) :
    BitVec.ofInt width (-value) = -(BitVec.ofInt width value) := by
  trustIrCompilerProof {
  apply BitVec.eq_of_toNat_eq
  apply Int.ofNat_inj.mp
  change ((BitVec.ofInt width (-value)).toNat : Int) = ((-(BitVec.ofInt width value)).toNat : Int)
  rw [bitvec_unsigned, BitVec.toNat_neg, Int.ofNat_emod,
    Int.ofNat_sub (Nat.le_of_lt (BitVec.ofInt width value).isLt)]
  have power : ((2 ^ width : Nat) : Int) = (2 : Int) ^ width := Int.natCast_pow 2 width
  rw [power, bitvec_unsigned]
  simp [Int.sub_emod, Int.neg_emod, Int.emod_emod]
  } { exact BitVec.ofInt_neg }

/-- Subtraction commutes with the pinned core's integer-to-word conversion. -/
theorem bitvec_ofInt_sub (width : Nat) (left right : Int) :
    BitVec.ofInt width (left - right) = BitVec.ofInt width left - BitVec.ofInt width right := by
  trustIrCompilerProof
    { rw [Int.sub_eq_add_neg, BitVec.ofInt_add, bitvec_ofInt_neg, BitVec.sub_toAdd] }
    { rw [Int.sub_eq_add_neg, BitVec.ofInt_add, bitvec_ofInt_neg, BitVec.sub_eq_add_neg] }

private theorem bitvec_trunc (width : Nat) (value : Int) :
    BitVec.ofInt width (((value % (2 : Int) ^ width) + (2 : Int) ^ width) % (2 : Int) ^ width) =
      BitVec.ofInt width value := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  have power : ((2 ^ width : Nat) : Int) = (2 : Int) ^ width := Int.natCast_pow 2 width
  rw [power]
  simp [Int.add_emod, Int.emod_emod]

/-- Actual wrapping addition agrees with core BitVec addition for arbitrary
operand expressions and integer environments, with no assumed input bounds. -/
theorem bvAdd_bitvec (width : Nat) (left right : TrustIrExpr) (env : SMTEnv) :
    BitVec.ofInt width ((.bvAdd left right : TrustIrExpr).evalAt env width) =
      BitVec.ofInt width (left.evalAt env width) + BitVec.ofInt width (right.evalAt env width) := by
  change BitVec.ofInt width (((_ % (2 : Int) ^ width) + (2 : Int) ^ width) % (2 : Int) ^ width) = _
  rw [bitvec_trunc, BitVec.ofInt_add]

/-- Actual wrapping subtraction agrees with core BitVec subtraction. -/
theorem bvSub_bitvec (width : Nat) (left right : TrustIrExpr) (env : SMTEnv) :
    BitVec.ofInt width ((.bvSub left right : TrustIrExpr).evalAt env width) =
      BitVec.ofInt width (left.evalAt env width) - BitVec.ofInt width (right.evalAt env width) := by
  change BitVec.ofInt width (((_ % (2 : Int) ^ width) + (2 : Int) ^ width) % (2 : Int) ^ width) = _
  rw [bitvec_trunc, bitvec_ofInt_sub]

/-- Actual wrapping multiplication agrees with core BitVec multiplication. -/
theorem bvMul_bitvec (width : Nat) (left right : TrustIrExpr) (env : SMTEnv) :
    BitVec.ofInt width ((.bvMul left right : TrustIrExpr).evalAt env width) =
      BitVec.ofInt width (left.evalAt env width) * BitVec.ofInt width (right.evalAt env width) := by
  change BitVec.ofInt width (((_ % (2 : Int) ^ width) + (2 : Int) ^ width) % (2 : Int) ^ width) = _
  rw [bitvec_trunc, BitVec.ofInt_mul]

/-- Actual wrapping negation agrees with core BitVec negation. -/
theorem bvNeg_bitvec (width : Nat) (arg : TrustIrExpr) (env : SMTEnv) :
    BitVec.ofInt width ((.bvNeg arg : TrustIrExpr).evalAt env width) =
      -(BitVec.ofInt width (arg.evalAt env width)) := by
  change BitVec.ofInt width (((_ % (2 : Int) ^ width) + (2 : Int) ^ width) % (2 : Int) ^ width) = _
  rw [bitvec_trunc, bitvec_ofInt_neg]

/-- Typing supplies the bound needed to recover the whole integer result
from core BitVec conversion, rather than merely equality modulo the width. -/
theorem SMTSorted.bitvec_ofInt_exact {width : Nat} {expr : TrustIrExpr}
    (typed : SMTSorted width expr (.bv width)) (env : SMTEnv) :
    Int.ofNat (BitVec.ofInt width (expr.evalAt env width)).toNat = expr.evalAt env width := by
  have range := SMTSorted.eval_value_valid width expr (.bv width) typed env
  exact bitvec_ofInt_toNat width _ range.1 range.2

/-- A successfully emitted bvAdd request has exactly the core operation's
unsigned result at its own width; no result bound is assumed. -/
theorem toSMTRequest_bvAdd_value (width : Nat) (left right : TrustIrExpr)
    (request : SMTRequest) (built : (.bvAdd left right : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    Int.ofNat ((BitVec.ofInt request.width (left.evalAt env request.width)) +
      (BitVec.ofInt request.width (right.evalAt env request.width))).toNat =
      (.bvAdd left right : TrustIrExpr).evalAt env request.width := by
  have metadata := toSMTRequest_metadata (.bvAdd left right) width request built
  rw [metadata.1]
  rw [← bvAdd_bitvec]
  have typed := toSMTRequest_sorted (.bvAdd left right) width request built
  generalize request.sort = sort at typed
  cases typed with
  | bvAdd leftTyped rightTyped =>
    exact (SMTSorted.bvAdd leftTyped rightTyped).bitvec_ofInt_exact env

/-- A successfully emitted bvSub request has exactly the core operation's
unsigned result at its own width; no result bound is assumed. -/
theorem toSMTRequest_bvSub_value (width : Nat) (left right : TrustIrExpr)
    (request : SMTRequest) (built : (.bvSub left right : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    Int.ofNat ((BitVec.ofInt request.width (left.evalAt env request.width)) -
      (BitVec.ofInt request.width (right.evalAt env request.width))).toNat =
      (.bvSub left right : TrustIrExpr).evalAt env request.width := by
  have metadata := toSMTRequest_metadata (.bvSub left right) width request built
  rw [metadata.1]
  rw [← bvSub_bitvec]
  have typed := toSMTRequest_sorted (.bvSub left right) width request built
  generalize request.sort = sort at typed
  cases typed with
  | bvSub leftTyped rightTyped =>
    exact (SMTSorted.bvSub leftTyped rightTyped).bitvec_ofInt_exact env

/-- A successfully emitted bvMul request has exactly the core operation's
unsigned result at its own width; no result bound is assumed. -/
theorem toSMTRequest_bvMul_value (width : Nat) (left right : TrustIrExpr)
    (request : SMTRequest) (built : (.bvMul left right : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    Int.ofNat ((BitVec.ofInt request.width (left.evalAt env request.width)) *
      (BitVec.ofInt request.width (right.evalAt env request.width))).toNat =
      (.bvMul left right : TrustIrExpr).evalAt env request.width := by
  have metadata := toSMTRequest_metadata (.bvMul left right) width request built
  rw [metadata.1]
  rw [← bvMul_bitvec]
  have typed := toSMTRequest_sorted (.bvMul left right) width request built
  generalize request.sort = sort at typed
  cases typed with
  | bvMul leftTyped rightTyped =>
    exact (SMTSorted.bvMul leftTyped rightTyped).bitvec_ofInt_exact env

/-- A successfully emitted negation request has exactly the core negation's
unsigned result at its own width. -/
theorem toSMTRequest_bvNeg_value (width : Nat) (arg : TrustIrExpr)
    (request : SMTRequest) (built : (.bvNeg arg : TrustIrExpr).toSMTRequest width = .ok request)
    (env : SMTEnv) :
    Int.ofNat (-(BitVec.ofInt request.width (arg.evalAt env request.width))).toNat =
      (.bvNeg arg : TrustIrExpr).evalAt env request.width := by
  have metadata := toSMTRequest_metadata (.bvNeg arg) width request built
  rw [metadata.1]
  rw [← bvNeg_bitvec]
  have typed := toSMTRequest_sorted (.bvNeg arg) width request built
  generalize request.sort = sort at typed
  cases typed with
  | bvNeg argTyped => exact (SMTSorted.bvNeg argTyped).bitvec_ofInt_exact env

end TrustIr.TrustIrExpr

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bitvec_ofInt_neg == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bitvec_ofInt_sub == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bvAdd_bitvec == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bvSub_bitvec == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bvMul_bitvec == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.bvNeg_bitvec == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTSorted.bitvec_ofInt_exact == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_bvAdd_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_bvSub_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_bvMul_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.toSMTRequest_bvNeg_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

