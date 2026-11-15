-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYDivisionInstruction
import TrustIr.Proofs.AYSignedDivisionInstruction
import TrustIr.Proofs.AYSourceInput
import TrustIr.Proofs.AYUnaryBody

namespace TrustIr.AYDivisionReplay
open TrustIrExpr AYGateCNF GenericCoro.Prefix

inductive Subject (model : ByteModel) where
  | unsigned (subject : UnsignedDivisionSubject model)
  | signed (subject : SignedDivisionSubject model)

def Subject.width {model} : Subject model → Nat
  | .unsigned s => s.width | .signed s => s.width
def Subject.ty {model} : Subject model → Ty
  | .unsigned s => s.ty | .signed s => s.ty
def Subject.op {model} : Subject model → BinOp
  | .unsigned s => s.op.irOp | .signed s => s.op.irOp
def Subject.toRequest {model} (subject : Subject model) :
    SMTCheckedTerm (.bv subject.width) → SMTCheckedTerm (.bv subject.width) → Except String (SMTTypedRequest (.bv subject.width)) :=
  match subject with | .unsigned s => s.toRequest | .signed s => s.toRequest
def Subject.decode {model} (subject : Subject model) :
    BitVec subject.width → BitVec subject.width → BitVec subject.width → Except SemError Value :=
  match subject with | .unsigned s => s.op.decode | .signed s => s.op.decode

structure Site (model : ByteModel) (original : Inst) where
  subject : Subject model
  left : ValueId
  right : ValueId
  origin : original = .BinOp subject.op subject.ty left right

private def Site.unsigned (model : ByteModel) (op : UnsignedDivisionOp) (ty : Ty) (left right : ValueId) :
    Except String (Site model (.BinOp op.irOp ty left right)) :=
  match built : UnsignedDivisionSubject.ofType model op ty with
  | .error reason => .error reason
  | .ok subject => .ok ⟨.unsigned subject,left,right,by
      have identity := UnsignedDivisionSubject.ofType_identity model op ty subject built
      simp only [Subject.op,Subject.ty]
      rw [identity.1,identity.2]⟩

private def Site.signed (model : ByteModel) (op : SignedDivisionOp) (ty : Ty) (left right : ValueId) :
    Except String (Site model (.BinOp op.irOp ty left right)) :=
  match built : SignedDivisionSubject.ofType model op ty with
  | .error reason => .error reason
  | .ok subject => .ok ⟨.signed subject,left,right,by
      have identity := SignedDivisionSubject.ofType_identity model op ty subject built
      simp only [Subject.op,Subject.ty]
      rw [identity.1,identity.2]⟩

def Site.build (model : ByteModel) : (original : Inst) → Except String (Site model original)
  | .BinOp .UDiv ty left right => Site.unsigned model .quotient ty left right
  | .BinOp .URem ty left right => Site.unsigned model .remainder ty left right
  | .BinOp .SDiv ty left right => Site.signed model .quotient ty left right
  | .BinOp .SRem ty left right => Site.signed model .remainder ty left right
  | _ => .error "division replay requires an original integer quotient or remainder"

/-- Execute the original definedness decoder before publishing any value. A
zero divisor or signed overflow cannot be licensed by a total SMT answer. -/
def publishDecoded (ctx : EvalContext) (original : Inst) (dests : List ValueId)
    (result : Except SemError Value) : Sem (ForInStep Unit) :=
  match result with
  | .error error => throw error
  | .ok value => publishComputedUnary ctx original dests value

theorem body_decoded (ctx : EvalContext) (op : BinOp) (ty : Ty) (left right : ValueId)
    (dests : List ValueId) (state : MachineState) (result : Except SemError Value)
    (computed : Sem.run (stepInstWithContext ctx (.BinOp op ty left right)) state = bindEncodedValue state result)
    (recurse : Recurse) (depth : Nat) (strategy : PanicStrategy) :
    Sem.run (evalBodyStep recurse ctx depth strategy (.BinOp op ty left right,dests)) state =
      Sem.run (publishDecoded ctx (.BinOp op ty left right) dests result) state := by
  cases result <;> simp only [evalBodyStep,Sem.run_bind,computed,publishDecoded,publishComputedUnary] <;> rfl

theorem body_request (ctx : EvalContext) (original : Inst) (site : Site ctx.byteModel original)
    (dests : List ValueId) (left right : SMTCheckedTerm (.bv site.subject.width))
    (request : SMTTypedRequest (.bv site.subject.width)) (built : site.subject.toRequest left right = .ok request)
    (env : SMTEnv) (state : MachineState)
    (leftLookup : state.lookupValue site.left = some (.int site.subject.width (Int.ofNat (left.term.eval env).toNat)))
    (rightLookup : state.lookupValue site.right = some (.int site.subject.width (Int.ofNat (right.term.eval env).toNat)))
    (recurse : Recurse) (depth : Nat) (strategy : PanicStrategy) :
    Sem.run (evalBodyStep recurse ctx depth strategy (original,dests)) state =
      Sem.run (publishDecoded ctx original dests (site.subject.decode (left.term.eval env) (right.term.eval env) (request.target.eval env))) state := by
  obtain ⟨subject,leftId,rightId,origin⟩ := site
  cases origin
  apply body_decoded
  cases subject with
  | unsigned subject => exact subject.request_outcome ctx left right request built env leftId rightId state leftLookup rightLookup
  | signed subject => exact subject.request_outcome ctx left right request built env leftId rightId state leftLookup rightLookup

theorem body_error (ctx : EvalContext) (original : Inst) (site : Site ctx.byteModel original)
    (dests : List ValueId) (state : MachineState) (error : SemError)
    (failed : Sem.run (stepInstWithContext ctx original) state = .error error)
    (recurse : Recurse) (depth : Nat) (strategy : PanicStrategy) :
    Sem.run (evalBodyStep recurse ctx depth strategy (original,dests)) state = .error error := by
  obtain ⟨subject,left,right,origin⟩ := site
  cases origin
  simp only [evalBodyStep,Sem.run_bind,failed]
  rfl

inductive Node (ctx : EvalContext) (row : Inst × List ValueId) (state : MachineState) where
  | request (site : Site ctx.byteModel row.1)
      (left right : SMTCheckedTerm (.bv site.subject.width)) (target : SMTTypedRequest (.bv site.subject.width))
      (built : site.subject.toRequest left right = .ok target) (env : SMTEnv)
      (leftLookup : state.lookupValue site.left = some (.int site.subject.width (Int.ofNat (left.term.eval env).toNat)))
      (rightLookup : state.lookupValue site.right = some (.int site.subject.width (Int.ofNat (right.term.eval env).toNat)))
  | sourceError (site : Site ctx.byteModel row.1) (error : SemError)
      (failed : Sem.run (stepInstWithContext ctx row.1) state = .error error)

def Node.outcome {ctx row state} : Node ctx row state → Except SemError (ForInStep Unit × MachineState)
  | .request site left right target _ env _ _ => Sem.run (publishDecoded ctx row.1 row.2
      (site.subject.decode (left.term.eval env) (right.term.eval env) (target.target.eval env))) state
  | .sourceError _ error _ => .error error

theorem Node.correct {ctx row state} (checked : Node ctx row state) (recurse : Recurse) (depth : Nat)
    (strategy : PanicStrategy) : Sem.run (evalBodyStep recurse ctx depth strategy row) state = checked.outcome := by
  cases checked with
  | request site left right target built env ll rl => exact body_request ctx row.1 site row.2 left right target built env state ll rl recurse depth strategy
  | sourceError site error failed => exact body_error ctx row.1 site row.2 state error failed recurse depth strategy

private def Node.sourceFailure {ctx row state} (site : Site ctx.byteModel row.1) (reason : String) :
    Except String (Node ctx row state) :=
  match actual : Sem.run (stepInstWithContext ctx row.1) state with
  | .error error => .ok (.sourceError site error actual)
  | .ok _ => .error reason

def Node.build (ctx : EvalContext) (row : Inst × List ValueId) (state : MachineState) :
    Except String (Node ctx row state) := do
  let site ← Site.build ctx.byteModel row.1
  match ll : state.lookupValue site.left, rl : state.lookupValue site.right with
  | some lhs,some rhs =>
    match SMTSourceInput.build (.bv site.subject.width) lhs, SMTSourceInput.build (.bv site.subject.width) rhs with
    | .ok left,.ok right =>
      match built : site.subject.toRequest left.arg right.arg with
      | .error reason => .error reason
      | .ok target => .ok (.request site left.arg right.arg target built SMTEnv.default
          (ll.trans (congrArg some left.same.symm)) (rl.trans (congrArg some right.same.symm)))
    | .error reason,_ => Node.sourceFailure site reason
    | _,.error reason => Node.sourceFailure site reason
  | _,_ => Node.sourceFailure site "division replay has no matching original operands"

end TrustIr.AYDivisionReplay
