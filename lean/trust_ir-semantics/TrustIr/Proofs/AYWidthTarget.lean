-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYWordWidths

namespace TrustIr.AYGateCNF
open TrustIrExpr

theorem WordCode.resize_target {source : Nat} (extra : Nat) (input : Fin source → Nat) (next : Nat)
    (bound : ∀ i, input i < next) (env : Assignment) (term : SMTTerm (.bv source)) (target : SMTEnv)
    (value : wordValue input env = term.eval target) :
    (WordCode.resize (source+extra) input next).value env =
      (SMTTerm.unary (.bvZeroExtend source extra) term).eval target := by
  rw [WordCode.resize_value _ _ _ bound, value]
  rfl

theorem WordCode.signExtend_target {source : Nat} (extra : Nat) (input : Fin source → Nat) (next : Nat)
    (bound : ∀ i, input i < next) (env : Assignment) (term : SMTTerm (.bv source)) (target : SMTEnv)
    (value : wordValue input env = term.eval target) :
    (WordCode.signExtend (source+extra) input next).value env =
      (SMTTerm.unary (.bvSignExtend source extra) term).eval target := by
  rw [WordCode.signExtend_value _ _ _ (by omega) bound, value]
  rfl

theorem WordCode.extract_target {source : Nat} (hi lo : Nat) (ordered : lo ≤ hi) (bounded : hi < source)
    (input : Fin source → Nat) (next : Nat) (bound : ∀ i, input i < next) (env : Assignment)
    (term : SMTTerm (.bv source)) (target : SMTEnv) (value : wordValue input env = term.eval target) :
    (WordCode.extract (hi-lo+1) lo input next).value env =
      (SMTTerm.unary (.bvExtract source hi lo ordered bounded) term).eval target := by
  rw [WordCode.extract_value _ _ _ _ bound, value]
  rfl

theorem WordCode.resize_truncate_target {source : Nat} (hi : Nat) (bounded : hi < source)
    (input : Fin source → Nat) (next : Nat) (bound : ∀ i, input i < next) (env : Assignment)
    (term : SMTTerm (.bv source)) (target : SMTEnv) (value : wordValue input env = term.eval target) :
    (WordCode.resize (hi+1) input next).value env =
      (SMTTerm.unary (.bvExtract source hi 0 (by omega) bounded) term).eval target := by
  rw [WordCode.resize_value _ _ _ bound, value]
  apply BitVec.eq_of_toNat_eq
  simp [SMTTerm.eval, SMTUnary.eval, BitVec.extractLsb, BitVec.extractLsb']

theorem WordCode.concat_target {highWidth lowWidth : Nat} (high : Fin highWidth → Nat)
    (low : Fin lowWidth → Nat) (env : Assignment) (highTerm : SMTTerm (.bv highWidth))
    (lowTerm : SMTTerm (.bv lowWidth)) (target : SMTEnv)
    (highValue : wordValue high env = highTerm.eval target) (lowValue : wordValue low env = lowTerm.eval target) :
    (WordCode.concat high low).value env = (SMTTerm.concat highTerm lowTerm).eval target := by
  rw [WordCode.concat_value, highValue, lowValue]
  rfl

theorem WordCode.composeResize_target {source : Nat} (extra next : Nat) (child : WordCode source)
    (checked : child.check next = true) (env : Assignment) (term : SMTTerm (.bv source)) (target : SMTEnv)
    (value : child.value env = term.eval target) :
    (WordCode.composeWidth (WidthOp.resize : WidthOp source (source+extra)) next child).value env =
      (SMTTerm.unary (.bvZeroExtend source extra) term).eval target := by
  rw [WordCode.composeWidth_value _ _ _ checked, value]
  rfl

theorem WordCode.composeSignExtend_target {source : Nat} (extra next : Nat) (child : WordCode source)
    (checked : child.check next = true) (env : Assignment) (term : SMTTerm (.bv source)) (target : SMTEnv)
    (value : child.value env = term.eval target) :
    (WordCode.composeWidth (WidthOp.signExtend (by omega) : WidthOp source (source+extra)) next child).value env =
      (SMTTerm.unary (.bvSignExtend source extra) term).eval target := by
  rw [WordCode.composeWidth_value _ _ _ checked, value]
  rfl

theorem WordCode.composeExtract_target {source : Nat} (hi lo : Nat) (ordered : lo ≤ hi) (bounded : hi < source)
    (next : Nat) (child : WordCode source) (checked : child.check next = true) (env : Assignment)
    (term : SMTTerm (.bv source)) (target : SMTEnv) (value : child.value env = term.eval target) :
    (WordCode.composeWidth (WidthOp.extract lo : WidthOp source (hi-lo+1)) next child).value env =
      (SMTTerm.unary (.bvExtract source hi lo ordered bounded) term).eval target := by
  rw [WordCode.composeWidth_value _ _ _ checked, value]
  rfl

theorem WordCode.composeConcat_target {highWidth lowWidth : Nat} (next : Nat) (high : WordCode highWidth)
    (low : WordCode lowWidth) (highCheck : high.check next = true)
    (lowCheck : low.check (next+high.gates.length) = true) (env : Assignment)
    (highTerm : SMTTerm (.bv highWidth)) (lowTerm : SMTTerm (.bv lowWidth)) (target : SMTEnv)
    (highValue : high.value env = highTerm.eval target) (lowValue : low.value (run high.gates env) = lowTerm.eval target) :
    (WordCode.composeConcat next high low).value env = (SMTTerm.concat highTerm lowTerm).eval target := by
  rw [WordCode.composeConcat_value _ _ _ highCheck lowCheck, highValue, lowValue]
  rfl

end TrustIr.AYGateCNF

/-- info: 'TrustIr.AYGateCNF.WordCode.resize_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.resize_target

/-- info: 'TrustIr.AYGateCNF.WordCode.signExtend_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.signExtend_target

/-- info: 'TrustIr.AYGateCNF.WordCode.extract_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.extract_target

/-- info: 'TrustIr.AYGateCNF.WordCode.resize_truncate_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.resize_truncate_target

/-- info: 'TrustIr.AYGateCNF.WordCode.concat_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.concat_target

/-- info: 'TrustIr.AYGateCNF.WordCode.composeResize_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.composeResize_target

/-- info: 'TrustIr.AYGateCNF.WordCode.composeSignExtend_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.composeSignExtend_target

/-- info: 'TrustIr.AYGateCNF.WordCode.composeExtract_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.composeExtract_target

/-- info: 'TrustIr.AYGateCNF.WordCode.composeConcat_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.composeConcat_target
