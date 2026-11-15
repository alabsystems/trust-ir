-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYPopulationCount
import TrustIr.Proofs.AYPermutationInstruction

namespace TrustIr
open TrustIrExpr

/-- An actual scalar CtPop type, retaining the model-dependent source width.
Char denotes its integer carrier here, not a Unicode validity certificate. -/
structure PopulationSubject (model : ByteModel) where
  ty : Ty
  width : Nat
  integer : ty.isInteger = true
  typeWidth : getTyWidth ty model = .ok width
  positive : 0 < width

def PopulationSubject.ofType (model : ByteModel) (ty : Ty) : Except String (PopulationSubject model) :=
  if integer : ty.isInteger = true then
    match actual : getTyWidth ty model with
    | .error _ => .error "population count type has no supported width"
    | .ok width =>
      if positive : 0 < width then .ok ⟨ty,width,integer,actual,positive⟩
      else .error "population count width must be positive"
  else .error "population count requires an integer type"

theorem PopulationSubject.ofType_identity (model : ByteModel) (ty : Ty)
    (subject : PopulationSubject model) (built : PopulationSubject.ofType model ty = .ok subject) :
    subject.ty = ty := by
  unfold PopulationSubject.ofType at built
  split at built
  · split at built
    · cases built
    · split at built
      · cases built; rfl
      · cases built
  · cases built

def PopulationSubject.instruction {model : ByteModel} (subject : PopulationSubject model)
    (operand : ValueId) : Inst := .UnOp .CtPop subject.ty operand

def PopulationSubject.toRequest {model : ByteModel} (subject : PopulationSubject model)
    (arg : SMTCheckedTerm (.bv subject.width)) : Except String (SMTTypedRequest (.bv subject.width)) := do
  let emitted ← arg.popCount
  emitted.toTypedRequest

/-- The actual returned request retains the exact target and its numerical
meaning. There is no assumed output equality or solver answer. -/
theorem PopulationSubject.request_target {model : ByteModel} (subject : PopulationSubject model)
    (arg : SMTCheckedTerm (.bv subject.width)) (request : SMTTypedRequest (.bv subject.width))
    (built : subject.toRequest arg = .ok request) (env : SMTEnv) :
    request.target.WellFormed ∧
      (request.target.eval env).toNat = popCountWidth (arg.term.eval env).toNat subject.width := by
  unfold PopulationSubject.toRequest at built
  cases emitted : arg.popCount with
  | error reason => simp [emitted, bind, Except.bind] at built
  | ok result =>
    have requested : result.toTypedRequest = .ok request := by
      simpa [emitted, bind, Except.bind] using built
    exact (arg.popCount_request result emitted request requested env).2

theorem PopulationSubject.request_bound {model : ByteModel} (subject : PopulationSubject model)
    (arg : SMTCheckedTerm (.bv subject.width)) (request : SMTTypedRequest (.bv subject.width))
    (built : subject.toRequest arg = .ok request) (env : SMTEnv) :
    (request.target.eval env).toNat ≤ subject.width := by
  rw [(subject.request_target arg request built env).2, ← populationSlice_semantics]
  exact populationSlice_bound _ _ _

theorem PopulationSubject.request_semIntUnOp {model : ByteModel} (subject : PopulationSubject model)
    (arg : SMTCheckedTerm (.bv subject.width)) (request : SMTTypedRequest (.bv subject.width))
    (built : subject.toRequest arg = .ok request) (operand : Int) (env : SMTEnv)
    (source : arg.term.eval env = BitVec.ofInt subject.width operand) :
    semIntUnOp .CtPop subject.width operand = .ok (Int.ofNat (request.target.eval env).toNat) := by
  unfold PopulationSubject.toRequest at built
  cases emitted : arg.popCount with
  | error reason => simp [emitted, bind, Except.bind] at built
  | ok result =>
    have requested : result.toTypedRequest = .ok request := by
      simpa [emitted, bind, Except.bind] using built
    rw [(result.toTypedRequest_admitted request requested).1]
    exact arg.popCount_semIntUnOp result emitted operand env source

/-- Indexed by the original instruction so its opcode, type and operand
cannot be replaced while constructing a request. -/
structure PopulationSite (model : ByteModel) (original : Inst) where
  subject : PopulationSubject model
  operand : ValueId
  origin : original = subject.instruction operand

def PopulationSite.ofInst (model : ByteModel) (original : Inst) : Except String (PopulationSite model original) :=
  match original with
  | .UnOp .CtPop ty id =>
    match checked : PopulationSubject.ofType model ty with
    | .error reason => .error reason
    | .ok subject => .ok ⟨subject,id,by
        have identity := PopulationSubject.ofType_identity model ty subject checked
        simp [PopulationSubject.instruction, identity]⟩
  | _ => .error "instruction is not a scalar integer population count"

def PopulationSite.toRequest {model : ByteModel} {original : Inst}
    (site : PopulationSite model original) (arg : SMTCheckedTerm (.bv site.subject.width)) :
    Except String (SMTTypedRequest (.bv site.subject.width)) := site.subject.toRequest arg

/-- A returned target determines the complete ORIGINAL instruction outcome.
Only original operand lookup and input mapping are premises. -/
theorem PopulationSite.bare_request_outcome (model : ByteModel) (original : Inst)
    (site : PopulationSite model original) (arg : SMTCheckedTerm (.bv site.subject.width))
    (request : SMTTypedRequest (.bv site.subject.width)) (built : site.toRequest arg = .ok request)
    (state : MachineState) (operand : Int) (env : SMTEnv)
    (lookup : state.lookupValue site.operand = some (.int site.subject.width operand))
    (source : arg.term.eval env = BitVec.ofInt site.subject.width operand) :
    Sem.run (stepInst original model) state =
      bindEncodedValue state (.ok (.int site.subject.width (Int.ofNat (request.target.eval env).toNat))) := by
  have identity := congrArg (fun inst => Sem.run (stepInst inst model) state) site.origin
  apply identity.trans
  exact int_unop_step_result .CtPop site.subject.ty site.subject.width site.operand state model operand _ lookup
    (site.subject.request_semIntUnOp arg request built operand env source)

theorem PopulationSite.request_outcome (ctx : EvalContext) (original : Inst)
    (site : PopulationSite ctx.byteModel original) (arg : SMTCheckedTerm (.bv site.subject.width))
    (request : SMTTypedRequest (.bv site.subject.width)) (built : site.toRequest arg = .ok request)
    (state : MachineState) (operand : Int) (env : SMTEnv)
    (lookup : state.lookupValue site.operand = some (.int site.subject.width operand))
    (source : arg.term.eval env = BitVec.ofInt site.subject.width operand) :
    Sem.run (stepInstWithContext ctx original) state =
      bindEncodedValue state (.ok (.int site.subject.width (Int.ofNat (request.target.eval env).toNat))) := by
  have identity := congrArg (fun inst => Sem.run (stepInstWithContext ctx inst) state) site.origin
  apply identity.trans
  exact int_unop_step_result .CtPop site.subject.ty site.subject.width site.operand state ctx.byteModel operand _ lookup
    (site.subject.request_semIntUnOp arg request built operand env source)

/-- Exposes the fresh SSA binding and all untouched state fields, rather
than proving only equality of the scalar answer. -/
theorem PopulationSite.request_state (ctx : EvalContext) (original : Inst)
    (site : PopulationSite ctx.byteModel original) (arg : SMTCheckedTerm (.bv site.subject.width))
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

theorem PopulationSite.missing_operand (ctx : EvalContext) (original : Inst)
    (site : PopulationSite ctx.byteModel original) (state : MachineState)
    (missing : state.lookupValue site.operand = none) :
    Sem.run (stepInstWithContext ctx original) state =
      .error (.typeError s!"undefined SSA value: {repr site.operand}") := by
  have identity := congrArg (fun inst => Sem.run (stepInstWithContext ctx inst) state) site.origin
  apply identity.trans
  exact int_unop_context_missing_operand ctx .CtPop site.subject.ty site.operand state missing

/-- An existing target does not override an original partial-value error. -/
theorem PopulationSite.guard_error (ctx : EvalContext) (original : Inst)
    (site : PopulationSite ctx.byteModel original) (state : MachineState) (value : Value) (error : SemError)
    (lookup : state.lookupValue site.operand = some value)
    (guard : Sem.run (Sem.rejectPartial value "UnOp") state = .error error) :
    Sem.run (stepInstWithContext ctx original) state = .error error := by
  have identity := congrArg (fun inst => Sem.run (stepInstWithContext ctx inst) state) site.origin
  apply identity.trans
  exact int_unop_context_guard_error ctx .CtPop site.subject.ty site.operand value state error lookup guard

end TrustIr
