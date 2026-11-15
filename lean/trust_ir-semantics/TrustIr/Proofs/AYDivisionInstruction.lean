-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYDivisionTarget
import TrustIr.Proofs.AYTypedRequest
import TrustIr.Proofs.AYTargetInstruction

namespace TrustIr
open TrustIrExpr AYGateCNF

def AYGateCNF.UnsignedDivisionOp.irOp : UnsignedDivisionOp → BinOp
  | .quotient => .UDiv
  | .remainder => .URem

def AYGateCNF.UnsignedDivisionOp.emit {width : Nat} (op : UnsignedDivisionOp)
    (left right : SMTCheckedTerm (.bv width)) : SMTCheckedTerm (.bv width) :=
  left.binary (op.target width) right

theorem AYGateCNF.UnsignedDivisionOp.emit_eval {width : Nat} (op : UnsignedDivisionOp)
    (left right : SMTCheckedTerm (.bv width)) (env : SMTEnv) :
    (op.emit left right).term.eval env = op.eval (left.term.eval env) (right.term.eval env) := by
  cases op <;> rfl

def AYGateCNF.UnsignedDivisionOp.legacy (op : UnsignedDivisionOp) (width : Nat) (left right : Int) : TrustIrExpr :=
  match op with
  | .quotient => .bvUDiv (.bvConst width left) (.bvConst width right)
  | .remainder => .bvURem (.bvConst width left) (.bvConst width right)

theorem AYGateCNF.UnsignedDivisionOp.legacy_encode (op : UnsignedDivisionOp) (width : Nat) (left right : Int) :
    encodeBinOp op.irOp (.bvConst width left) (.bvConst width right) = some (op.legacy width left right) := by
  cases op <;> rfl

theorem AYGateCNF.UnsignedDivisionOp.legacy_value {width : Nat} (op : UnsignedDivisionOp)
    (positive : 0 < width) (left right : BitVec width) :
    (op.legacy width (Int.ofNat left.toNat) (Int.ofNat right.toNat)).evalAt SMTEnv.default width =
      Int.ofNat (op.eval left right).toNat := by
  have translated : SMTTranslated width (op.legacy width (Int.ofNat left.toNat) (Int.ofNat right.toNat))
      (.binary (op.target width) (.bvConst width (Int.ofNat left.toNat)) (.bvConst width (Int.ofNat right.toNat))) := by
    cases op with
    | quotient => exact .bvUDiv (.bvConst _ positive) (.bvConst _ positive)
    | remainder => exact .bvURem (.bvConst _ positive) (.bvConst _ positive)
  have actual := translated.eval_correct positive SMTEnv.default SMTEnv.default (fun _ => rfl)
  have leftWord : BitVec.ofInt width (Int.ofNat left.toNat) = left := SMTSort.toCore_fromCore (.bv width) left
  have rightWord : BitVec.ofInt width (Int.ofNat right.toNat) = right := SMTSort.toCore_fromCore (.bv width) right
  cases op <;> simp only [UnsignedDivisionOp.target, UnsignedDivisionOp.eval,
    SMTTerm.eval, SMTBinary.eval, SMTSort.fromCore] at actual ⊢
  all_goals rw [leftWord, rightWord] at actual
  all_goals exact actual.symm

/-- Retain the source definedness decoder even when the SMT result is total. -/
def AYGateCNF.UnsignedDivisionOp.decode {width : Nat} (op : UnsignedDivisionOp)
    (left right result : BitVec width) : Except SemError Value := do
  let value ← decodeIntBinOpEncoding op.irOp width (Int.ofNat left.toNat) (Int.ofNat right.toNat) (Int.ofNat result.toNat)
  pure (.int width value)

theorem AYGateCNF.UnsignedDivisionOp.step_outcome {width : Nat} (op : UnsignedDivisionOp)
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
    rightRange.1 rightRange.2 (by cases op <;> simp [UnsignedDivisionOp.irOp])
    (op.legacy width _ _) (op.legacy_encode _ _ _) SMTEnv.default
  rw [op.legacy_value positive] at outcome
  exact outcome

theorem AYGateCNF.UnsignedDivisionOp.context_outcome {width : Nat} (op : UnsignedDivisionOp)
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
    rightRange.1 rightRange.2 (by cases op <;> simp [UnsignedDivisionOp.irOp])
    (op.legacy width _ _) (op.legacy_encode _ _ _) SMTEnv.default
  rw [op.legacy_value positive] at outcome
  exact outcome

/-- This receipt is the checked circuit execution, not an assumed answer.
The conclusion preserves the entire original instruction outcome and state. -/
theorem AYGateCNF.UnsignedDivisionOp.gate_context_outcome {width : Nat} (op : UnsignedDivisionOp)
    (positive : 0 < width) (ty : Ty) (integer : ty.isInteger = true) (ctx : EvalContext)
    (leftId rightId : ValueId) (state : MachineState) (dividend divisor : Fin width → Nat)
    (next : Nat) (assignment : Assignment) (result : BitVec width)
    (executed : WordCode.checkedUnsignedDivision op dividend divisor next assignment = some result)
    (leftLookup : state.lookupValue leftId = some (.int width (Int.ofNat (wordValue dividend assignment).toNat)))
    (rightLookup : state.lookupValue rightId = some (.int width (Int.ofNat (wordValue divisor assignment).toNat))) :
    Sem.run (stepInstWithContext ctx (.BinOp op.irOp ty leftId rightId)) state =
      bindEncodedValue state (op.decode (wordValue dividend assignment) (wordValue divisor assignment) result) := by
  obtain ⟨leftBound, rightBound, actual⟩ := (WordCode.checkedUnsignedDivision_eq_some _ _ _ _ _ _).mp executed
  rw [WordCode.unsignedDivision_value _ _ _ _ leftBound rightBound] at actual
  rw [← actual]
  exact op.context_outcome positive ty integer ctx leftId rightId state _ _ leftLookup rightLookup

/-- A source-bound semantic subject, not a body-validation receipt. -/
structure UnsignedDivisionSubject (model : ByteModel) where
  op : UnsignedDivisionOp
  width : Nat
  ty : Ty
  positive : 0 < width
  integer : ty.isInteger = true
  typeWidth : getTyWidth ty model = .ok width

def UnsignedDivisionSubject.ofType (model : ByteModel) (op : UnsignedDivisionOp) (ty : Ty) :
    Except String (UnsignedDivisionSubject model) :=
  if integer : ty.isInteger = true then
    match actual : getTyWidth ty model with
    | .error _ => .error "integer type has no supported width"
    | .ok width =>
      if positive : 0 < width then .ok ⟨op,width,ty,positive,integer,actual⟩
      else .error "integer division width must be positive"
  else .error "unsigned division requires an integer type"

def UnsignedDivisionSubject.instruction {model : ByteModel} (subject : UnsignedDivisionSubject model)
    (left right : ValueId) : Inst := .BinOp subject.op.irOp subject.ty left right

theorem UnsignedDivisionSubject.ofType_identity (model : ByteModel) (op : UnsignedDivisionOp) (ty : Ty)
    (subject : UnsignedDivisionSubject model) (built : UnsignedDivisionSubject.ofType model op ty = .ok subject) :
    subject.op = op ∧ subject.ty = ty := by
  unfold UnsignedDivisionSubject.ofType at built
  split at built
  · split at built
    · cases built
    · split at built
      · cases built; exact ⟨rfl,rfl⟩
      · cases built
  · cases built

theorem AYGateCNF.UnsignedDivisionOp.decode_zero {width : Nat} (op : UnsignedDivisionOp)
    (left result : BitVec width) :
    op.decode left (BitVec.ofNat width 0) result =
      .error (.ub (if op = .quotient then "unsigned division by zero" else "unsigned remainder by zero")) := by
  trustIrCompilerProof {
    cases op <;> simp [UnsignedDivisionOp.decode, UnsignedDivisionOp.irOp, decodeIntBinOpEncoding,
      bind, Except.bind, pure, Except.pure]
  } {
    cases op <;> simp only [UnsignedDivisionOp.decode, BitVec.toNat_ofNat, Nat.zero_mod] <;> rfl
  }

def UnsignedDivisionSubject.toRequest {model : ByteModel} (subject : UnsignedDivisionSubject model)
    (left right : SMTCheckedTerm (.bv subject.width)) : Except String (SMTTypedRequest (.bv subject.width)) :=
  (subject.op.emit left right).toTypedRequest

theorem UnsignedDivisionSubject.request_outcome (ctx : EvalContext) (subject : UnsignedDivisionSubject ctx.byteModel)
    (left right : SMTCheckedTerm (.bv subject.width)) (request : SMTTypedRequest (.bv subject.width))
    (built : subject.toRequest left right = .ok request) (env : SMTEnv) (leftId rightId : ValueId) (state : MachineState)
    (leftLookup : state.lookupValue leftId = some (.int subject.width (Int.ofNat (left.term.eval env).toNat)))
    (rightLookup : state.lookupValue rightId = some (.int subject.width (Int.ofNat (right.term.eval env).toNat))) :
    Sem.run (stepInstWithContext ctx (subject.instruction leftId rightId)) state =
      bindEncodedValue state (subject.op.decode (left.term.eval env) (right.term.eval env) (request.target.eval env)) := by
  have actual := ((subject.op.emit left right).toTypedRequest_admitted request built).1
  rw [actual, subject.op.emit_eval]
  exact subject.op.context_outcome subject.positive subject.ty subject.integer ctx leftId rightId state _ _ leftLookup rightLookup

theorem UnsignedDivisionSubject.original_request_outcome (ctx : EvalContext) (subject : UnsignedDivisionSubject ctx.byteModel)
    (original : Inst) (leftId rightId : ValueId) (same : original = subject.instruction leftId rightId)
    (left right : SMTCheckedTerm (.bv subject.width)) (request : SMTTypedRequest (.bv subject.width))
    (built : subject.toRequest left right = .ok request) (env : SMTEnv) (state : MachineState)
    (leftLookup : state.lookupValue leftId = some (.int subject.width (Int.ofNat (left.term.eval env).toNat)))
    (rightLookup : state.lookupValue rightId = some (.int subject.width (Int.ofNat (right.term.eval env).toNat))) :
    Sem.run (stepInstWithContext ctx original) state =
      bindEncodedValue state (subject.op.decode (left.term.eval env) (right.term.eval env) (request.target.eval env)) := by
  rw [same]
  exact subject.request_outcome ctx left right request built env leftId rightId state leftLookup rightLookup

theorem UnsignedDivisionSubject.gate_outcome (ctx : EvalContext) (subject : UnsignedDivisionSubject ctx.byteModel)
    (dividend divisor : Fin subject.width → Nat) (next : Nat) (assignment : Assignment)
    (result : BitVec subject.width)
    (executed : WordCode.checkedUnsignedDivision subject.op dividend divisor next assignment = some result)
    (leftId rightId : ValueId) (state : MachineState)
    (leftLookup : state.lookupValue leftId = some (.int subject.width (Int.ofNat (wordValue dividend assignment).toNat)))
    (rightLookup : state.lookupValue rightId = some (.int subject.width (Int.ofNat (wordValue divisor assignment).toNat))) :
    Sem.run (stepInstWithContext ctx (subject.instruction leftId rightId)) state =
      bindEncodedValue state (subject.op.decode (wordValue dividend assignment) (wordValue divisor assignment) result) :=
  subject.op.gate_context_outcome subject.positive subject.ty subject.integer ctx leftId rightId state
    dividend divisor next assignment result executed leftLookup rightLookup

end TrustIr

#trustIrAxiomsExact TrustIr.AYGateCNF.UnsignedDivisionOp.emit_eval == [propext, Quot.sound]

/-- info: 'TrustIr.AYGateCNF.UnsignedDivisionOp.legacy_encode' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.UnsignedDivisionOp.legacy_encode

#trustIrAxiomsExact TrustIr.AYGateCNF.UnsignedDivisionOp.legacy_value == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.UnsignedDivisionOp.step_outcome == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.UnsignedDivisionOp.context_outcome == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.UnsignedDivisionOp.gate_context_outcome == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.UnsignedDivisionSubject.ofType_identity == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.AYGateCNF.UnsignedDivisionOp.decode_zero == [propext, Quot.sound] modern [propext]

#trustIrAxiomsExact TrustIr.UnsignedDivisionSubject.request_outcome == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.UnsignedDivisionSubject.original_request_outcome == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsExact TrustIr.UnsignedDivisionSubject.gate_outcome == [propext, Classical.choice, Quot.sound]
