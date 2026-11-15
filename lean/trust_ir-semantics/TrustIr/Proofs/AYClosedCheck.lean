-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYTargetInstruction

namespace TrustIr.TrustIrExpr

/-- Check a closed request by its actual native target assertion. Symbolic
requests are refused; no oracle answer or external payload is consulted. -/
def SMTRequest.checkClosedUnsat (request : SMTRequest) : Bool :=
  request.bindings.isEmpty && !(request.assertion.eval SMTEnv.default)

/-- Successful actual construction authenticates the declaration inventory.
A closed target refutation therefore holds in every source environment. -/
theorem toSMTRequest_checkClosedUnsat_sound (expr : TrustIrExpr) (width : Nat)
    (request : SMTRequest) (built : expr.toSMTRequest width = .ok request)
    (checked : request.checkClosedUnsat = true) : formula_unsat request.width expr := by
  have closed : request.bindings = [] := by
    cases names : request.bindings with
    | nil => rfl
    | cons head tail => simp [List.isEmpty, SMTRequest.checkClosedUnsat, names] at checked
  have rejected : request.assertion.eval SMTEnv.default = false := by
    simpa [List.isEmpty, SMTRequest.checkClosedUnsat, closed] using checked
  have zero : expr.evalAt SMTEnv.default request.width = 0 := by
    by_cases zero : expr.evalAt SMTEnv.default request.width = 0
    · exact zero
    · have accepted := (toSMTRequest_target_truth expr width request built
        SMTEnv.default SMTEnv.default (fun _ => rfl)).mpr zero
      rw [rejected] at accepted
      cases accepted
  intro env
  have same := toSMTRequest_eval_congr expr width request built env SMTEnv.default (by
    intro name member
    rw [closed] at member
    cases member)
  exact same.trans zero

/-- Exact admission for this checker: closed actual requests are accepted iff
unsatisfiable. This does not claim completeness for symbolic requests. -/
theorem toSMTRequest_checkClosedUnsat_iff (expr : TrustIrExpr) (width : Nat)
    (request : SMTRequest) (built : expr.toSMTRequest width = .ok request) :
    request.checkClosedUnsat = true ↔ request.bindings = [] ∧ formula_unsat request.width expr := by
  constructor
  · intro checked
    refine ⟨?_, toSMTRequest_checkClosedUnsat_sound expr width request built checked⟩
    cases names : request.bindings with
    | nil => rfl
    | cons head tail => simp [List.isEmpty, SMTRequest.checkClosedUnsat, names] at checked
  · rintro ⟨closed, unsat⟩
    have rejected := (toSMTRequest_unsat_iff_target expr width request built).mp unsat SMTEnv.default
    simp [List.isEmpty, SMTRequest.checkClosedUnsat, closed, rejected]

/-- Checked closed requests supply the universal premise of the target-to-IR
laws, with no AY soundness axiom. -/
theorem toSMTRequest_checkClosedUnsat_refutes (expr : TrustIrExpr) (width : Nat)
    (request : SMTRequest) (built : expr.toSMTRequest width = .ok request)
    (checked : request.checkClosedUnsat = true) :
    ∀ env : SMTEnv, request.assertion.eval env = false :=
  (toSMTRequest_unsat_iff_target expr width request built).mp
    (toSMTRequest_checkClosedUnsat_sound expr width request built checked)

/-- Construct and check the actual request; serialization errors refuse. -/
def checkClosedUnsat (expr : TrustIrExpr) (width : Nat) : Bool :=
  match expr.toSMTRequest width with
  | .error _ => false
  | .ok request => request.checkClosedUnsat

/-- Accepted checks retain successful request construction and its exact width. -/
theorem checkClosedUnsat_request (expr : TrustIrExpr) (width : Nat)
    (checked : expr.checkClosedUnsat width = true) :
    ∃ request : SMTRequest, expr.toSMTRequest width = .ok request ∧
      request.checkClosedUnsat = true := by
  cases built : expr.toSMTRequest width with
  | error message => simp [checkClosedUnsat, built] at checked
  | ok request => exact ⟨request, rfl, by simpa [checkClosedUnsat, built] using checked⟩

/-- The executable whole-request checker proves source unsatisfiability. -/
theorem checkClosedUnsat_sound (expr : TrustIrExpr) (width : Nat)
    (checked : expr.checkClosedUnsat width = true) : formula_unsat width expr := by
  obtain ⟨request, built, accepted⟩ := checkClosedUnsat_request expr width checked
  have sound := toSMTRequest_checkClosedUnsat_sound expr width request built accepted
  rw [(toSMTRequest_metadata expr width request built).1] at sound
  exact sound

end TrustIr.TrustIrExpr

namespace TrustIr
open TrustIrExpr

/-- A concrete closed-target check justifies source equivalence. -/
theorem checked_expr_equiv (width : Nat) (left right : TrustIrExpr) (request : SMTRequest)
    (built : (expr_diff left right).toSMTRequest width = .ok request)
    (checked : request.checkClosedUnsat = true) : expr_equiv width left right :=
  target_expr_equiv width left right request built
    (toSMTRequest_checkClosedUnsat_refutes _ width request built checked)

/-- A checked closed target preserves the complete original IR decoder outcome. -/
theorem checked_constant_fold_outcome (op : BinOp) (width : Nat) (lhs rhs result : Int)
    (leftNonnegative : 0 ≤ lhs) (leftBound : lhs < (2 : Int) ^ width)
    (rightNonnegative : 0 ≤ rhs) (rightBound : rhs < (2 : Int) ^ width)
    (boolOperands : op = .BAnd ∨ op = .BOr ∨ op = .BXor →
      (lhs = 0 ∨ lhs = 1) ∧ (rhs = 0 ∨ rhs = 1))
    (encoded : TrustIrExpr)
    (encoding : encodeBinOp op (.bvConst width lhs) (.bvConst width rhs) = some encoded)
    (request : SMTRequest)
    (built : (expr_diff encoded (.bvConst width result)).toSMTRequest width = .ok request)
    (checked : request.checkClosedUnsat = true) :
    semIntBinOp op width lhs rhs =
      decodeIntBinOpEncoding op width lhs rhs (truncateUnsigned result width) :=
  target_constant_fold_outcome op width lhs rhs result leftNonnegative leftBound rightNonnegative rightBound boolOperands encoded encoding request built
    (toSMTRequest_checkClosedUnsat_refutes _ width request built checked)

/-- A checked closed target preserves the complete original IR decoder outcome. -/
theorem checked_constant_fold_context_outcome (op : BinOp) (ty : Ty) (width : Nat)
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
    (checked : request.checkClosedUnsat = true) :
    Sem.run (stepInstWithContext ctx (.BinOp op ty leftId rightId)) state =
      bindEncodedValue state (do
        let folded ← decodeIntBinOpEncoding op width lhs rhs (truncateUnsigned result width)
        pure (.int width folded)) :=
  target_constant_fold_context_outcome op ty width integer ctx leftId rightId state lhs rhs result leftLookup rightLookup leftNonnegative leftBound rightNonnegative rightBound boolOperands encoded encoding request built
    (toSMTRequest_checkClosedUnsat_refutes _ width request built checked)

end TrustIr

#trustIrAxiomsExact TrustIr.TrustIrExpr.toSMTRequest_checkClosedUnsat_sound == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.TrustIrExpr.toSMTRequest_checkClosedUnsat_iff == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.TrustIrExpr.toSMTRequest_checkClosedUnsat_refutes == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.TrustIrExpr.checkClosedUnsat_request == [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.TrustIrExpr.checkClosedUnsat_sound == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.checked_expr_equiv == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.checked_constant_fold_outcome == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.checked_constant_fold_context_outcome == [propext, Quot.sound, Classical.choice]
