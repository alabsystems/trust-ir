-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYZeroCountTarget
import TrustIr.Proofs.AYPermutationInstruction

namespace TrustIr
open TrustIrExpr

/-- An actual scalar CtLz/CtTz type, retaining the model-dependent source width.
Char denotes its integer carrier here, not a Unicode validity certificate. -/
structure ZeroCountSubject (model : ByteModel) where
  direction : ZeroCountDirection
  ty : Ty
  width : Nat
  integer : ty.isInteger = true
  typeWidth : getTyWidth ty model = .ok width
  positive : 0 < width

def ZeroCountSubject.ofType (model : ByteModel) (direction : ZeroCountDirection) (ty : Ty) : Except String (ZeroCountSubject model) :=
  if integer : ty.isInteger = true then
    match actual : getTyWidth ty model with
    | .error _ => .error "zero count type has no supported width"
    | .ok width =>
      if positive : 0 < width then .ok ⟨direction,ty,width,integer,actual,positive⟩
      else .error "zero count width must be positive"
  else .error "zero count requires an integer type"

theorem ZeroCountSubject.ofType_identity (model : ByteModel) (direction : ZeroCountDirection) (ty : Ty)
    (subject : ZeroCountSubject model) (built : ZeroCountSubject.ofType model direction ty = .ok subject) :
    subject.ty = ty ∧ subject.direction = direction := by
  unfold ZeroCountSubject.ofType at built
  split at built
  · split at built
    · cases built
    · split at built
      · cases built; exact ⟨rfl,rfl⟩
      · cases built
  · cases built

def ZeroCountSubject.instruction {model : ByteModel} (subject : ZeroCountSubject model)
    (operand : ValueId) : Inst := .UnOp subject.direction.irOp subject.ty operand

def ZeroCountSubject.toRequest {model : ByteModel} (subject : ZeroCountSubject model)
    (arg : SMTCheckedTerm (.bv subject.width)) : Except String (SMTTypedRequest (.bv subject.width)) := do
  let emitted ← arg.zeroCount subject.direction
  emitted.toTypedRequest

/-- The actual returned request retains the exact target and its numerical
meaning. There is no assumed output equality or solver answer. -/
theorem ZeroCountSubject.request_target {model : ByteModel} (subject : ZeroCountSubject model)
    (arg : SMTCheckedTerm (.bv subject.width)) (request : SMTTypedRequest (.bv subject.width))
    (built : subject.toRequest arg = .ok request) (env : SMTEnv) :
    request.target.WellFormed ∧
      (request.target.eval env).toNat = subject.direction.number (arg.term.eval env).toNat subject.width := by
  unfold ZeroCountSubject.toRequest at built
  cases emitted : arg.zeroCount subject.direction with
  | error reason => simp [emitted, bind, Except.bind] at built
  | ok result =>
    have requested : result.toTypedRequest = .ok request := by
      simpa [emitted, bind, Except.bind] using built
    exact (arg.zeroCount_request result subject.direction emitted request requested env).2

theorem ZeroCountSubject.request_bound {model : ByteModel} (subject : ZeroCountSubject model)
    (arg : SMTCheckedTerm (.bv subject.width)) (request : SMTTypedRequest (.bv subject.width))
    (built : subject.toRequest arg = .ok request) (env : SMTEnv) :
    (request.target.eval env).toNat ≤ subject.width := by
  rw [(subject.request_target arg request built env).2, ← zeroScan_complete]
  exact zeroScan_bound _ _ _ _

theorem ZeroCountSubject.request_semIntUnOp {model : ByteModel} (subject : ZeroCountSubject model)
    (arg : SMTCheckedTerm (.bv subject.width)) (request : SMTTypedRequest (.bv subject.width))
    (built : subject.toRequest arg = .ok request) (operand : Int) (env : SMTEnv)
    (source : arg.term.eval env = BitVec.ofInt subject.width operand) :
    semIntUnOp subject.direction.irOp subject.width operand = .ok (Int.ofNat (request.target.eval env).toNat) := by
  unfold ZeroCountSubject.toRequest at built
  cases emitted : arg.zeroCount subject.direction with
  | error reason => simp [emitted, bind, Except.bind] at built
  | ok result =>
    have requested : result.toTypedRequest = .ok request := by
      simpa [emitted, bind, Except.bind] using built
    rw [(result.toTypedRequest_admitted request requested).1]
    exact arg.zeroCount_semIntUnOp result subject.direction emitted operand env source

/-- The actual returned target preserves the total all-zero case. -/
theorem ZeroCountSubject.request_zero {model : ByteModel} (subject : ZeroCountSubject model)
    (arg : SMTCheckedTerm (.bv subject.width)) (request : SMTTypedRequest (.bv subject.width))
    (built : subject.toRequest arg = .ok request) (env : SMTEnv)
    (zero : (arg.term.eval env).toNat = 0) : (request.target.eval env).toNat = subject.width := by
  rw [(subject.request_target arg request built env).2, ← zeroScan_complete, zero]
  exact zeroScan_zero _ _ _

/-- Indexed by the original instruction so its opcode, type and operand
cannot be replaced while constructing a request. -/
structure ZeroCountSite (model : ByteModel) (original : Inst) where
  subject : ZeroCountSubject model
  operand : ValueId
  origin : original = subject.instruction operand

def ZeroCountSite.ofInst (model : ByteModel) (original : Inst) : Except String (ZeroCountSite model original) :=
  match original with
  | .UnOp .CtLz ty id =>
    match checked : ZeroCountSubject.ofType model .leading ty with
    | .error reason => .error reason
    | .ok subject => .ok ⟨subject,id,by
        have identity := ZeroCountSubject.ofType_identity model .leading ty subject checked
        simp [ZeroCountSubject.instruction, identity.1, identity.2, ZeroCountDirection.irOp]⟩
  | .UnOp .CtTz ty id =>
    match checked : ZeroCountSubject.ofType model .trailing ty with
    | .error reason => .error reason
    | .ok subject => .ok ⟨subject,id,by
        have identity := ZeroCountSubject.ofType_identity model .trailing ty subject checked
        simp [ZeroCountSubject.instruction, identity.1, identity.2, ZeroCountDirection.irOp]⟩
  | _ => .error "instruction is not a scalar integer leading/trailing zero count"

def ZeroCountSite.toRequest {model : ByteModel} {original : Inst}
    (site : ZeroCountSite model original) (arg : SMTCheckedTerm (.bv site.subject.width)) :
    Except String (SMTTypedRequest (.bv site.subject.width)) := site.subject.toRequest arg

/-- A returned target determines the complete ORIGINAL instruction outcome.
Only original operand lookup and input mapping are premises. -/
theorem ZeroCountSite.bare_request_outcome (model : ByteModel) (original : Inst)
    (site : ZeroCountSite model original) (arg : SMTCheckedTerm (.bv site.subject.width))
    (request : SMTTypedRequest (.bv site.subject.width)) (built : site.toRequest arg = .ok request)
    (state : MachineState) (operand : Int) (env : SMTEnv)
    (lookup : state.lookupValue site.operand = some (.int site.subject.width operand))
    (source : arg.term.eval env = BitVec.ofInt site.subject.width operand) :
    Sem.run (stepInst original model) state =
      bindEncodedValue state (.ok (.int site.subject.width (Int.ofNat (request.target.eval env).toNat))) := by
  have identity := congrArg (fun inst => Sem.run (stepInst inst model) state) site.origin
  apply identity.trans
  exact int_unop_step_result site.subject.direction.irOp site.subject.ty site.subject.width site.operand state model operand _ lookup
    (site.subject.request_semIntUnOp arg request built operand env source)

theorem ZeroCountSite.request_outcome (ctx : EvalContext) (original : Inst)
    (site : ZeroCountSite ctx.byteModel original) (arg : SMTCheckedTerm (.bv site.subject.width))
    (request : SMTTypedRequest (.bv site.subject.width)) (built : site.toRequest arg = .ok request)
    (state : MachineState) (operand : Int) (env : SMTEnv)
    (lookup : state.lookupValue site.operand = some (.int site.subject.width operand))
    (source : arg.term.eval env = BitVec.ofInt site.subject.width operand) :
    Sem.run (stepInstWithContext ctx original) state =
      bindEncodedValue state (.ok (.int site.subject.width (Int.ofNat (request.target.eval env).toNat))) := by
  have identity := congrArg (fun inst => Sem.run (stepInstWithContext ctx inst) state) site.origin
  apply identity.trans
  exact int_unop_step_result site.subject.direction.irOp site.subject.ty site.subject.width site.operand state ctx.byteModel operand _ lookup
    (site.subject.request_semIntUnOp arg request built operand env source)

/-- Exposes the fresh SSA binding and all untouched state fields, rather
than proving only equality of the scalar answer. -/
theorem ZeroCountSite.request_state (ctx : EvalContext) (original : Inst)
    (site : ZeroCountSite ctx.byteModel original) (arg : SMTCheckedTerm (.bv site.subject.width))
    (request : SMTTypedRequest (.bv site.subject.width)) (built : site.toRequest arg = .ok request)
    (state : MachineState) (operand : Int) (env : SMTEnv)
    (lookup : state.lookupValue site.operand = some (.int site.subject.width operand))
    (source : arg.term.eval env = BitVec.ofInt site.subject.width operand) :
    Sem.run (stepInstWithContext ctx original) state =
      .ok (.value (some ⟨state.nextValueId⟩),
        { state with
          locals := state.locals.set ⟨state.nextValueId⟩
            (.int site.subject.width (Int.ofNat (request.target.eval env).toNat)),
          nextValueId := state.nextValueId+1 }) :=
  site.request_outcome ctx original arg request built state operand env lookup source

theorem ZeroCountSite.missing_operand (ctx : EvalContext) (original : Inst)
    (site : ZeroCountSite ctx.byteModel original) (state : MachineState)
    (missing : state.lookupValue site.operand = none) :
    Sem.run (stepInstWithContext ctx original) state =
      .error (.typeError s!"undefined SSA value: {repr site.operand}") := by
  have identity := congrArg (fun inst => Sem.run (stepInstWithContext ctx inst) state) site.origin
  apply identity.trans
  exact int_unop_context_missing_operand ctx site.subject.direction.irOp site.subject.ty site.operand state missing

/-- An existing target does not override an original partial-value error. -/
theorem ZeroCountSite.guard_error (ctx : EvalContext) (original : Inst)
    (site : ZeroCountSite ctx.byteModel original) (state : MachineState) (value : Value) (error : SemError)
    (lookup : state.lookupValue site.operand = some value)
    (guard : Sem.run (Sem.rejectPartial value "UnOp") state = .error error) :
    Sem.run (stepInstWithContext ctx original) state = .error error := by
  have identity := congrArg (fun inst => Sem.run (stepInstWithContext ctx inst) state) site.origin
  apply identity.trans
  exact int_unop_context_guard_error ctx site.subject.direction.irOp site.subject.ty site.operand value state error lookup guard

end TrustIr
