-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYTargetCorrect

namespace TrustIr
open TrustIrExpr

private theorem constant_eval (width : Nat) (value : Int) (env : SMTEnv) :
    (TrustIrExpr.bvConst width value).evalAt env width = truncateUnsigned value width := by
  change ((value % (2 : Int) ^ width) + (2 : Int) ^ width) % (2 : Int) ^ width = _
  simp [truncateUnsigned, Int.add_emod]

/-- A refutation of the actual returned target proves source equivalence.
The width comes from successful request construction, not an oracle answer. -/
theorem target_expr_equiv (width : Nat) (left right : TrustIrExpr) (request : SMTRequest)
    (built : (expr_diff left right).toSMTRequest width = .ok request)
    (refuted : ∀ target : SMTEnv, request.assertion.eval target = false) :
    expr_equiv width left right := by
  have unsat := (toSMTRequest_unsat_iff_target _ width request built).mpr refuted
  have sameWidth := (toSMTRequest_metadata _ width request built).1
  rw [sameWidth] at unsat
  intro env
  have zero := unsat env
  by_cases same : left.evalAt env width = right.evalAt env width
  · exact same
  · simp [expr_diff, TrustIrExpr.evalAt, same] at zero

/-- Kernel-checked target refutation preserves the original decoder, including
undefinedness errors, result representation and the operation width. -/
theorem target_constant_fold_outcome (op : BinOp) (width : Nat) (lhs rhs result : Int)
    (leftNonnegative : 0 ≤ lhs) (leftBound : lhs < (2 : Int) ^ width)
    (rightNonnegative : 0 ≤ rhs) (rightBound : rhs < (2 : Int) ^ width)
    (boolOperands : op = .BAnd ∨ op = .BOr ∨ op = .BXor →
      (lhs = 0 ∨ lhs = 1) ∧ (rhs = 0 ∨ rhs = 1))
    (encoded : TrustIrExpr)
    (encoding : encodeBinOp op (.bvConst width lhs) (.bvConst width rhs) = some encoded)
    (request : SMTRequest)
    (built : (expr_diff encoded (.bvConst width result)).toSMTRequest width = .ok request)
    (refuted : ∀ target : SMTEnv, request.assertion.eval target = false) :
    semIntBinOp op width lhs rhs =
      decodeIntBinOpEncoding op width lhs rhs (truncateUnsigned result width) := by
  have equivalent := target_expr_equiv width encoded (.bvConst width result) request built refuted SMTEnv.default
  have outcome := int_binop_encoding_outcome op width lhs rhs leftNonnegative leftBound
    rightNonnegative rightBound boolOperands encoded encoding SMTEnv.default
  rw [equivalent] at outcome
  simpa only [constant_eval] using outcome

/-- Kernel-checked target refutation preserves the original decoder, including
undefinedness errors, result representation and the operation width. -/
theorem target_constant_fold_context_outcome (op : BinOp) (ty : Ty) (width : Nat)
    (integer : ty.isInteger = true) (ctx : EvalContext)
    (leftId rightId : ValueId) (state : MachineState) (lhs rhs result : Int)
    (leftLookup : state.lookupValue leftId = some (.int width lhs))
    (rightLookup : state.lookupValue rightId = some (.int width rhs))
    (leftNonnegative : 0 ≤ lhs) (leftBound : lhs < (2 : Int) ^ width)
    (rightNonnegative : 0 ≤ rhs) (rightBound : rhs < (2 : Int) ^ width)
    (boolOperands : op = .BAnd ∨ op = .BOr ∨ op = .BXor →
      (lhs = 0 ∨ lhs = 1) ∧ (rhs = 0 ∨ rhs = 1))
    (encoded : TrustIrExpr)
    (encoding : encodeBinOp op (.bvConst width lhs) (.bvConst width rhs) = some encoded)
    (request : SMTRequest)
    (built : (expr_diff encoded (.bvConst width result)).toSMTRequest width = .ok request)
    (refuted : ∀ target : SMTEnv, request.assertion.eval target = false) :
    Sem.run (stepInstWithContext ctx (.BinOp op ty leftId rightId)) state =
      bindEncodedValue state (do
        let folded ← decodeIntBinOpEncoding op width lhs rhs (truncateUnsigned result width)
        pure (.int width folded)) := by
  have equivalent := target_expr_equiv width encoded (.bvConst width result) request built refuted SMTEnv.default
  have outcome := int_binop_context_encoding_outcome op ty width integer ctx leftId rightId
    state lhs rhs leftLookup rightLookup leftNonnegative leftBound rightNonnegative rightBound
    boolOperands encoded encoding SMTEnv.default
  rw [equivalent] at outcome
  simpa only [constant_eval] using outcome

/-- Refutation of an actual target also reaches complete instruction equivalence
when both actual executions have the same faithful stateful decoder. -/
theorem target_inst_equiv (width : Nat) (left right : Inst)
    (leftExpr rightExpr : TrustIrExpr) (request : SMTRequest)
    (built : (expr_diff leftExpr rightExpr).toSMTRequest width = .ok request)
    (refuted : ∀ target : SMTEnv, request.assertion.eval target = false)
    (stateToEnv : MachineState → SMTEnv) (decode : InstructionDecoder)
    (leftFaithful : encoding_determines_behavior width left leftExpr stateToEnv decode)
    (rightFaithful : encoding_determines_behavior width right rightExpr stateToEnv decode) :
    ay_inst_equiv left right :=
  ay_equiv_implies_inst_equiv width left right leftExpr rightExpr stateToEnv decode
    (target_expr_equiv width leftExpr rightExpr request built refuted) leftFaithful rightFaithful

end TrustIr

#trustIrAxiomsExact TrustIr.target_expr_equiv == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.target_constant_fold_outcome == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.target_constant_fold_context_outcome == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.target_inst_equiv == [propext, Quot.sound, Classical.choice]
