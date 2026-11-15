-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYSignedDivision
import TrustIr.Proofs.AYTypedRequest
import TrustIr.Proofs.AYTargetInstruction

namespace TrustIr
open TrustIrExpr AYGateCNF

def AYGateCNF.SignedDivisionOp.irOp : SignedDivisionOp → BinOp
  | .quotient => .SDiv
  | .remainder => .SRem

def AYGateCNF.SignedDivisionOp.emit {width : Nat} (op : SignedDivisionOp)
    (left right : SMTCheckedTerm (.bv width)) : SMTCheckedTerm (.bv width) :=
  left.binary (op.target width) right

theorem AYGateCNF.SignedDivisionOp.emit_eval {width : Nat} (op : SignedDivisionOp)
    (left right : SMTCheckedTerm (.bv width)) (env : SMTEnv) :
    (op.emit left right).term.eval env = op.eval (left.term.eval env) (right.term.eval env) := by
  cases op <;> rfl

def AYGateCNF.SignedDivisionOp.legacy (op : SignedDivisionOp) (width : Nat) (left right : Int) : TrustIrExpr :=
  match op with
  | .quotient => .bvSDiv (.bvConst width left) (.bvConst width right)
  | .remainder => .bvSRem (.bvConst width left) (.bvConst width right)

theorem AYGateCNF.SignedDivisionOp.legacy_encode (op : SignedDivisionOp) (width : Nat) (left right : Int) :
    encodeBinOp op.irOp (.bvConst width left) (.bvConst width right) = some (op.legacy width left right) := by
  cases op <;> rfl

theorem AYGateCNF.SignedDivisionOp.legacy_value {width : Nat} (op : SignedDivisionOp)
    (positive : 0 < width) (left right : BitVec width) :
    (op.legacy width (Int.ofNat left.toNat) (Int.ofNat right.toNat)).evalAt SMTEnv.default width =
      Int.ofNat (op.eval left right).toNat := by
  have translated : SMTTranslated width (op.legacy width (Int.ofNat left.toNat) (Int.ofNat right.toNat))
      (.binary (op.target width) (.bvConst width (Int.ofNat left.toNat)) (.bvConst width (Int.ofNat right.toNat))) := by
    cases op with
    | quotient => exact .bvSDiv (.bvConst _ positive) (.bvConst _ positive)
    | remainder => exact .bvSRem (.bvConst _ positive) (.bvConst _ positive)
  have actual := translated.eval_correct positive SMTEnv.default SMTEnv.default (fun _ => rfl)
  have leftWord : BitVec.ofInt width (Int.ofNat left.toNat) = left := SMTSort.toCore_fromCore (.bv width) left
  have rightWord : BitVec.ofInt width (Int.ofNat right.toNat) = right := SMTSort.toCore_fromCore (.bv width) right
  cases op <;> simp only [SignedDivisionOp.target, SignedDivisionOp.eval,
    SMTTerm.eval, SMTBinary.eval, SMTSort.fromCore] at actual ⊢
  all_goals rw [leftWord, rightWord] at actual
  all_goals exact actual.symm

/-- Retain the source definedness decoder even when the SMT result is total. -/
def AYGateCNF.SignedDivisionOp.decode {width : Nat} (op : SignedDivisionOp)
    (left right result : BitVec width) : Except SemError Value := do
  let value ← decodeIntBinOpEncoding op.irOp width (Int.ofNat left.toNat) (Int.ofNat right.toNat) (Int.ofNat result.toNat)
  pure (.int width value)

theorem AYGateCNF.SignedDivisionOp.step_outcome {width : Nat} (op : SignedDivisionOp)
    (positive : 0 < width) (ty : Ty) (model : ByteModel) (leftId rightId : ValueId) (state : MachineState)
    (left right : BitVec width)
    (leftLookup : state.lookupValue leftId = some (.int width (Int.ofNat left.toNat)))
    (rightLookup : state.lookupValue rightId = some (.int width (Int.ofNat right.toNat))) :
    Sem.run (stepInst (.BinOp op.irOp ty leftId rightId) model) state =
      bindEncodedValue state (op.decode left right (op.eval left right)) := by
  have leftRange := SMTSort.fromCore_valid (.bv width) left
  have rightRange := SMTSort.fromCore_valid (.bv width) right
  have outcome := int_binop_step_encoding_outcome op.irOp ty width leftId rightId state model
    (Int.ofNat left.toNat) (Int.ofNat right.toNat) leftLookup rightLookup leftRange.1 leftRange.2
    rightRange.1 rightRange.2 (by cases op <;> simp [SignedDivisionOp.irOp])
    (op.legacy width _ _) (op.legacy_encode _ _ _) SMTEnv.default
  rw [op.legacy_value positive] at outcome
  exact outcome

theorem AYGateCNF.SignedDivisionOp.context_outcome {width : Nat} (op : SignedDivisionOp)
    (positive : 0 < width) (ty : Ty) (integer : ty.isInteger = true) (ctx : EvalContext)
    (leftId rightId : ValueId) (state : MachineState) (left right : BitVec width)
    (leftLookup : state.lookupValue leftId = some (.int width (Int.ofNat left.toNat)))
    (rightLookup : state.lookupValue rightId = some (.int width (Int.ofNat right.toNat))) :
    Sem.run (stepInstWithContext ctx (.BinOp op.irOp ty leftId rightId)) state =
      bindEncodedValue state (op.decode left right (op.eval left right)) := by
  have leftRange := SMTSort.fromCore_valid (.bv width) left
  have rightRange := SMTSort.fromCore_valid (.bv width) right
  have outcome := int_binop_context_encoding_outcome op.irOp ty width integer ctx leftId rightId state
    (Int.ofNat left.toNat) (Int.ofNat right.toNat) leftLookup rightLookup leftRange.1 leftRange.2
    rightRange.1 rightRange.2 (by cases op <;> simp [SignedDivisionOp.irOp])
    (op.legacy width _ _) (op.legacy_encode _ _ _) SMTEnv.default
  rw [op.legacy_value positive] at outcome
  exact outcome

/-- This receipt is the checked circuit execution, not an assumed answer.
The conclusion preserves the entire original instruction outcome and state. -/
theorem AYGateCNF.SignedDivisionOp.gate_context_outcome {width : Nat} (op : SignedDivisionOp)
    (positive : 0 < width) (ty : Ty) (integer : ty.isInteger = true) (ctx : EvalContext)
    (leftId rightId : ValueId) (state : MachineState) (dividend divisor : Fin width → Nat)
    (next : Nat) (assignment : Assignment) (result : BitVec width)
    (executed : WordCode.checkedSignedDivision op dividend divisor next assignment = some result)
    (leftLookup : state.lookupValue leftId = some (.int width (Int.ofNat (wordValue dividend assignment).toNat)))
    (rightLookup : state.lookupValue rightId = some (.int width (Int.ofNat (wordValue divisor assignment).toNat))) :
    Sem.run (stepInstWithContext ctx (.BinOp op.irOp ty leftId rightId)) state =
      bindEncodedValue state (op.decode (wordValue dividend assignment) (wordValue divisor assignment) result) := by
  obtain ⟨leftBound, rightBound, actual⟩ := (WordCode.checkedSignedDivision_eq_some _ _ _ _ _ _).mp executed
  rw [WordCode.signedDivision_value _ _ _ _ leftBound rightBound] at actual
  rw [← actual]
  exact op.context_outcome positive ty integer ctx leftId rightId state _ _ leftLookup rightLookup

/-- A source-bound semantic subject, not a body-validation receipt. -/
structure SignedDivisionSubject (model : ByteModel) where
  op : SignedDivisionOp
  width : Nat
  ty : Ty
  positive : 0 < width
  integer : ty.isInteger = true
  typeWidth : getTyWidth ty model = .ok width

def SignedDivisionSubject.ofType (model : ByteModel) (op : SignedDivisionOp) (ty : Ty) :
    Except String (SignedDivisionSubject model) :=
  if integer : ty.isInteger = true then
    match actual : getTyWidth ty model with
    | .error _ => .error "integer type has no supported width"
    | .ok width =>
      if positive : 0 < width then .ok ⟨op,width,ty,positive,integer,actual⟩
      else .error "integer division width must be positive"
  else .error "signed division requires an integer type"

def SignedDivisionSubject.instruction {model : ByteModel} (subject : SignedDivisionSubject model)
    (left right : ValueId) : Inst := .BinOp subject.op.irOp subject.ty left right

theorem SignedDivisionSubject.ofType_identity (model : ByteModel) (op : SignedDivisionOp) (ty : Ty)
    (subject : SignedDivisionSubject model) (built : SignedDivisionSubject.ofType model op ty = .ok subject) :
    subject.op = op ∧ subject.ty = ty := by
  unfold SignedDivisionSubject.ofType at built
  split at built
  · split at built
    · cases built
    · split at built
      · cases built; exact ⟨rfl,rfl⟩
      · cases built
  · cases built

theorem AYGateCNF.SignedDivisionOp.decode_zero {width : Nat} (op : SignedDivisionOp)
    (left result : BitVec width) :
    op.decode left (BitVec.ofNat width 0) result =
      .error (.ub (if op = .quotient then "signed division by zero" else "signed remainder by zero")) := by
  trustIrCompilerProof {
    cases op <;> simp [SignedDivisionOp.decode, SignedDivisionOp.irOp, decodeIntBinOpEncoding,
      bind, Except.bind, pure, Except.pure]
  } {
    cases op <;> simp only [SignedDivisionOp.decode, BitVec.toNat_ofNat, Nat.zero_mod] <;> rfl
  }

def SignedDivisionSubject.toRequest {model : ByteModel} (subject : SignedDivisionSubject model)
    (left right : SMTCheckedTerm (.bv subject.width)) : Except String (SMTTypedRequest (.bv subject.width)) :=
  (subject.op.emit left right).toTypedRequest

/-- Overflow is source policy and cannot be discharged by any total SMT result. -/
theorem AYGateCNF.SignedDivisionOp.decode_overflow {width : Nat} (op : SignedDivisionOp)
    (left right result : BitVec width)
    (minimum : toSigned (Int.ofNat left.toNat) width = -((2 : Int)^(width-1)))
    (minusOne : toSigned (Int.ofNat right.toNat) width = -1)
    (nonzero : right.toNat ≠ 0) :
    op.decode left right result = .error (.ub (if op = .quotient then
      "signed division overflow (INT_MIN / -1)" else "signed remainder overflow (INT_MIN % -1)")) := by
  trustIrCompilerProof {
    change toSigned (left.toNat : Int) width = _ at minimum
    change toSigned (right.toNat : Int) width = -1 at minusOne
    have rhsNonzero : (right.toNat : Int) ≠ 0 := by
      intro zero
      have same := congrArg Int.toNat zero
      simp at same
      exact nonzero same
    cases op <;> simp [SignedDivisionOp.decode, SignedDivisionOp.irOp, decodeIntBinOpEncoding,
      rhsNonzero, minimum, minusOne, bind, Except.bind, pure, Except.pure]
  } {
    have rhsNonzero : (Int.ofNat right.toNat : Int) ≠ 0 := by
      intro h
      exact nonzero (Int.ofNat.inj h)
    have zeroTest : (Int.ofNat right.toNat == (0 : Int)) = false :=
      Bool.eq_false_iff.mpr (fun h => rhsNonzero (beq_iff_eq.mp h))
    have intSelf (value : Int) : (value == value) = true := beq_iff_eq.mpr rfl
    cases op <;> simp only [SignedDivisionOp.decode, SignedDivisionOp.irOp,
      decodeIntBinOpEncoding, zeroTest, Bool.false_eq_true, if_false,
      minimum, minusOne, intSelf, bind, Except.bind, pure, Except.pure] <;> rfl
  }

theorem SignedDivisionSubject.request_outcome (ctx : EvalContext) (subject : SignedDivisionSubject ctx.byteModel)
    (left right : SMTCheckedTerm (.bv subject.width)) (request : SMTTypedRequest (.bv subject.width))
    (built : subject.toRequest left right = .ok request) (env : SMTEnv) (leftId rightId : ValueId) (state : MachineState)
    (leftLookup : state.lookupValue leftId = some (.int subject.width (Int.ofNat (left.term.eval env).toNat)))
    (rightLookup : state.lookupValue rightId = some (.int subject.width (Int.ofNat (right.term.eval env).toNat))) :
    Sem.run (stepInstWithContext ctx (subject.instruction leftId rightId)) state =
      bindEncodedValue state (subject.op.decode (left.term.eval env) (right.term.eval env) (request.target.eval env)) := by
  have actual := ((subject.op.emit left right).toTypedRequest_admitted request built).1
  rw [actual, subject.op.emit_eval]
  exact subject.op.context_outcome subject.positive subject.ty subject.integer ctx leftId rightId state _ _ leftLookup rightLookup

theorem SignedDivisionSubject.original_request_outcome (ctx : EvalContext) (subject : SignedDivisionSubject ctx.byteModel)
    (original : Inst) (leftId rightId : ValueId) (same : original = subject.instruction leftId rightId)
    (left right : SMTCheckedTerm (.bv subject.width)) (request : SMTTypedRequest (.bv subject.width))
    (built : subject.toRequest left right = .ok request) (env : SMTEnv) (state : MachineState)
    (leftLookup : state.lookupValue leftId = some (.int subject.width (Int.ofNat (left.term.eval env).toNat)))
    (rightLookup : state.lookupValue rightId = some (.int subject.width (Int.ofNat (right.term.eval env).toNat))) :
    Sem.run (stepInstWithContext ctx original) state =
      bindEncodedValue state (subject.op.decode (left.term.eval env) (right.term.eval env) (request.target.eval env)) := by
  rw [same]
  exact subject.request_outcome ctx left right request built env leftId rightId state leftLookup rightLookup

theorem SignedDivisionSubject.gate_outcome (ctx : EvalContext) (subject : SignedDivisionSubject ctx.byteModel)
    (dividend divisor : Fin subject.width → Nat) (next : Nat) (assignment : Assignment)
    (result : BitVec subject.width)
    (executed : WordCode.checkedSignedDivision subject.op dividend divisor next assignment = some result)
    (leftId rightId : ValueId) (state : MachineState)
    (leftLookup : state.lookupValue leftId = some (.int subject.width (Int.ofNat (wordValue dividend assignment).toNat)))
    (rightLookup : state.lookupValue rightId = some (.int subject.width (Int.ofNat (wordValue divisor assignment).toNat))) :
    Sem.run (stepInstWithContext ctx (subject.instruction leftId rightId)) state =
      bindEncodedValue state (subject.op.decode (wordValue dividend assignment) (wordValue divisor assignment) result) :=
  subject.op.gate_context_outcome subject.positive subject.ty subject.integer ctx leftId rightId state
    dividend divisor next assignment result executed leftLookup rightLookup

end TrustIr

#trustIrAxiomsExact TrustIr.AYGateCNF.SignedDivisionOp.emit_eval == [propext, Quot.sound]

/-- info: 'TrustIr.AYGateCNF.SignedDivisionOp.legacy_encode' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.SignedDivisionOp.legacy_encode

#trustIrAxiomsExact TrustIr.AYGateCNF.SignedDivisionOp.legacy_value == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.SignedDivisionOp.step_outcome == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.SignedDivisionOp.context_outcome == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.SignedDivisionOp.gate_context_outcome == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SignedDivisionSubject.ofType_identity == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.AYGateCNF.SignedDivisionOp.decode_zero == [propext, Quot.sound] modern [propext]

#trustIrAxiomsExact TrustIr.AYGateCNF.SignedDivisionOp.decode_overflow == [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.SignedDivisionSubject.request_outcome == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.SignedDivisionSubject.original_request_outcome == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.SignedDivisionSubject.gate_outcome == [propext, Classical.choice, Quot.sound]
