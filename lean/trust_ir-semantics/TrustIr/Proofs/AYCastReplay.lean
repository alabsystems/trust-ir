-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYCastTarget
import TrustIr.Proofs.AYUnaryBody

namespace TrustIr.AYCastReplay
open TrustIrExpr GenericCoro.Prefix

structure Carrier (model : ByteModel) (ty : Ty) where
  sort : SMTSort
  typed : sort.CastType model ty
  positive : ∀ width, sort = .bv width → 0 < width

def Carrier.build (model : ByteModel) (ty : Ty) : Except String (Carrier model ty) :=
  if boolean : ty.isBool = true then .ok ⟨.bool,(Ty.isBool_iff ty).mp boolean,by intro width impossible; cases impossible⟩
  else if integer : ty.isInteger = true then
    match width : getTyWidth ty model with
    | .error _ => .error "cast type has no supported width"
    | .ok bits =>
      if positive : 0 < bits then .ok ⟨.bv bits,⟨integer,width⟩,by intro w same; cases same; exact positive⟩
      else .error "cast width must be positive"
  else .error "cast replay requires an integer or Bool type"

def plan (op : CastOp) (input output : SMTSort) : Except String (IntegerCastTarget op input output) :=
  match op,input,output with
  | .Trunc,.bv source,.bv target =>
    if valid : 0 < target ∧ target < source then
      .ok (by
        have size : target-1+1 = target := by omega
        have narrow : target-1+1 < source := by omega
        simpa only [size] using IntegerCastTarget.trunc source (target-1) narrow)
    else .error "Trunc requires a positive strictly smaller destination"
  | .ZExt,.bv source,.bv target =>
    if valid : 0 < source ∧ source < target then
      .ok (by
        have size : source+(target-source) = target := by omega
        simpa only [size] using IntegerCastTarget.zext source (target-source) valid.1 (by omega))
    else .error "ZExt requires a positive strictly larger destination"
  | .SExt,.bv source,.bv target =>
    if valid : 0 < source ∧ source < target then
      .ok (by
        have size : source+(target-source) = target := by omega
        simpa only [size] using IntegerCastTarget.sext source (target-source) valid.1 (by omega))
    else .error "SExt requires a positive strictly larger destination"
  | .Trunc,.bv source,.bool =>
    if narrow : 1 < source then .ok (.truncBool source narrow)
    else .error "Bool truncation requires a source wider than one bit"
  | .ZExt,.bool,.bv target =>
    if widen : 1 < target then .ok (.zextBool target widen)
    else .error "Bool extension requires a destination wider than one bit"
  | .SExt,.bool,.bv target =>
    if widen : 1 < target then .ok (.sextBool target widen)
    else .error "Bool extension requires a destination wider than one bit"
  | _,_,_ => .error "unsupported cast replay operation or sorts"

structure Site (model : ByteModel) (original : Inst) where
  subject : IntegerCastSubject model
  operand : ValueId
  origin : original = subject.instruction operand

def Site.build (model : ByteModel) (original : Inst) : Except String (Site model original) :=
  match original with
  | .Cast op source target operand => do
    let input ← Carrier.build model source
    let output ← Carrier.build model target
    let selected ← plan op input.sort output.sort
    .ok ⟨⟨op,source,target,input.sort,output.sort,selected,input.typed,output.typed⟩,operand,rfl⟩
  | _ => .error "cast replay requires an original Cast instruction"

/-- Complete production publication, including original destination/type and
Char checks, follows from the actual typed request. -/
theorem body_request (ctx : EvalContext) (original : Inst) (site : Site ctx.byteModel original)
    (dests : List ValueId) (arg : SMTCheckedTerm site.subject.input)
    (request : SMTTypedRequest site.subject.output) (built : site.subject.toRequest arg = .ok request)
    (env : SMTEnv) (state : MachineState)
    (lookup : state.lookupValue site.operand = some (site.subject.input.irValue (arg.term.eval env)))
    (recurse : Recurse) (depth : Nat) (strategy : PanicStrategy) :
    Sem.run (evalBodyStep recurse ctx depth strategy (original,dests)) state =
      Sem.run (publishComputedUnary ctx original dests (site.subject.output.irValue (request.target.eval env))) state := by
  have computed := site.subject.original_request_outcome ctx original site.operand site.origin arg request built env state lookup
  obtain ⟨subject,operand,origin⟩ := site
  cases origin
  simp only [IntegerCastSubject.instruction] at computed
  simp only [IntegerCastSubject.instruction,evalBodyStep,Sem.run_bind,computed,publishComputedUnary]
  rfl

theorem body_error (ctx : EvalContext) (original : Inst) (site : Site ctx.byteModel original)
    (dests : List ValueId) (state : MachineState) (error : SemError)
    (failed : Sem.run (stepInstWithContext ctx original) state = .error error)
    (recurse : Recurse) (depth : Nat) (strategy : PanicStrategy) :
    Sem.run (evalBodyStep recurse ctx depth strategy (original,dests)) state = .error error := by
  obtain ⟨subject,operand,origin⟩ := site
  cases origin
  simp only [IntegerCastSubject.instruction] at failed
  simp only [IntegerCastSubject.instruction,evalBodyStep,Sem.run_bind,failed]
  rfl

inductive Node (ctx : EvalContext) (row : Inst × List ValueId) (state : MachineState) where
  | request (site : Site ctx.byteModel row.1)
      (arg : SMTCheckedTerm site.subject.input) (target : SMTTypedRequest site.subject.output)
      (built : site.subject.toRequest arg = .ok target) (env : SMTEnv)
      (lookup : state.lookupValue site.operand = some (site.subject.input.irValue (arg.term.eval env)))
  | sourceError (site : Site ctx.byteModel row.1) (error : SemError)
      (failed : Sem.run (stepInstWithContext ctx row.1) state = .error error)

def Node.outcome {ctx row state} : Node ctx row state → Except SemError (ForInStep Unit × MachineState)
  | .request site _ target _ env _ =>
    Sem.run (publishComputedUnary ctx row.1 row.2 (site.subject.output.irValue (target.target.eval env))) state
  | .sourceError _ error _ => .error error

theorem Node.correct {ctx row state} (checked : Node ctx row state) (recurse : Recurse) (depth : Nat)
    (strategy : PanicStrategy) : Sem.run (evalBodyStep recurse ctx depth strategy row) state = checked.outcome := by
  cases checked with
  | request site arg target built env lookup => exact body_request ctx row.1 site row.2 arg target built env state lookup recurse depth strategy
  | sourceError site error failed => exact body_error ctx row.1 site row.2 state error failed recurse depth strategy

def Node.build (ctx : EvalContext) (row : Inst × List ValueId) (state : MachineState) :
    Except String (Node ctx row state) := do
  let site ← Site.build ctx.byteModel row.1
  match actual : Sem.run (stepInstWithContext ctx row.1) state with
  | .error error => .ok (.sourceError site error actual)
  | .ok _ =>
    match lookup : state.lookupValue site.operand with
    | none => .error "cast replay has no original operand"
    | some value => do
      let input ← SMTSourceInput.build site.subject.input value
      match built : site.subject.toRequest input.arg with
      | .error reason => .error reason
      | .ok target => .ok (.request site input.arg target built SMTEnv.default (input.same.symm ▸ lookup))

end TrustIr.AYCastReplay
