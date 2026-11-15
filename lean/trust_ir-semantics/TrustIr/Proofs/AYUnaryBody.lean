-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYZeroCountGates
import TrustIr.Proofs.GenericCoroPrefixLayer

namespace TrustIr
open TrustIrExpr AYGateCNF GenericCoro.Prefix

/-- Publish a computed primitive value through the ORIGINAL production
result binder. Destination/type/Char checks and temporary retirement remain
actual executable operations, not success premises or a supplied final state. -/
def publishComputedUnary (ctx : EvalContext) (original : Inst) (dests : List ValueId)
    (value : Value) : Sem (ForInStep Unit) := do
  let id ← Sem.bindFresh value
  ctx.bindInstructionResults original (.value (some id)) dests
  pure (.yield ())

private theorem body_run_bind {α β : Type} (action : Sem α) (next : α → Sem β) (state : MachineState) :
    Sem.run (action >>= next) state = (do
      let (value,after) ← Sem.run action state
      Sem.run (next value) after) := rfl

/-- Transport a proven primitive outcome to the production body node, without
discarding its original destination checks or any ensuing error. -/
theorem unaryBody_of_step (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (op : UnOp) (ty : Ty) (operand : ValueId) (dests : List ValueId) (state : MachineState) (value : Value)
    (computed : Sem.run (stepInstWithContext ctx (.UnOp op ty operand)) state = bindEncodedValue state (.ok value)) :
    Sem.run (evalBodyStep recurse ctx depth strategy (.UnOp op ty operand,dests)) state =
      Sem.run (publishComputedUnary ctx (.UnOp op ty operand) dests value) state := by
  simp only [evalBodyStep, body_run_bind, computed, publishComputedUnary]
  rfl

private theorem unaryBody_of_origin (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (original : Inst) {op : UnOp} {ty : Ty} {operand : ValueId} (origin : original = .UnOp op ty operand)
    (dests : List ValueId) (state : MachineState) (value : Value)
    (computed : Sem.run (stepInstWithContext ctx original) state = bindEncodedValue state (.ok value)) :
    Sem.run (evalBodyStep recurse ctx depth strategy (original,dests)) state =
      Sem.run (publishComputedUnary ctx original dests value) state := by
  have identity := congrArg (fun inst => Sem.run (evalBodyStep recurse ctx depth strategy (inst,dests)) state =
    Sem.run (publishComputedUnary ctx inst dests value) state) origin
  apply Eq.mpr identity
  apply unaryBody_of_step
  exact (congrArg (fun inst => Sem.run (stepInstWithContext ctx inst) state) origin).symm.trans computed

/-- Primitive source failures remain terminal before result publication. -/
theorem unaryBody_error (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (op : UnOp) (ty : Ty) (operand : ValueId) (dests : List ValueId) (state : MachineState) (error : SemError)
    (failed : Sem.run (stepInstWithContext ctx (.UnOp op ty operand)) state = .error error) :
    Sem.run (evalBodyStep recurse ctx depth strategy (.UnOp op ty operand,dests)) state = .error error := by
  simp only [evalBodyStep, body_run_bind, failed]
  rfl

/-- The actual returned request reaches the production body binder, including its refusals. -/
theorem IntegerPermutationSite.body_request (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (original : Inst) (site : IntegerPermutationSite ctx.byteModel original)
    (dests : List ValueId) (arg : SMTCheckedTerm (.bv site.subject.width))
    (request : SMTTypedRequest (.bv site.subject.width)) (built : site.toRequest arg = .ok request)
    (state : MachineState) (operand : Int) (env : SMTEnv)
    (lookup : state.lookupValue site.operand = some (.int site.subject.width operand))
    (source : arg.term.eval env = BitVec.ofInt site.subject.width operand) :
    Sem.run (evalBodyStep recurse ctx depth strategy (original,dests)) state =
      Sem.run (publishComputedUnary ctx original dests (.int site.subject.width
        (Int.ofNat (request.target.eval env).toNat))) state :=
  unaryBody_of_origin recurse ctx depth strategy original site.origin dests state _
    (site.request_outcome ctx original arg request built state operand env lookup source)

/-- Actual checked gates also preserve the complete production body outcome. -/
theorem IntegerPermutationSite.body_gate (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (original : Inst) (site : IntegerPermutationSite ctx.byteModel original)
    (dests : List ValueId) (base next : Nat) (env : Assignment) (state : MachineState)
    (operand : Int) (result : BitVec site.subject.width)
    (lookup : state.lookupValue site.operand = some (.int site.subject.width operand))
    (executed : site.subject.checkedCode base next (BitVec.ofInt site.subject.width operand) env = some result) :
    Sem.run (evalBodyStep recurse ctx depth strategy (original,dests)) state =
      Sem.run (publishComputedUnary ctx original dests (.int site.subject.width (Int.ofNat result.toNat))) state :=
  unaryBody_of_origin recurse ctx depth strategy original site.origin dests state _
    (site.gate_outcome ctx original base next env state operand result lookup executed)

/-- The actual returned request reaches the production body binder, including its refusals. -/
theorem PopulationSite.body_request (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (original : Inst) (site : PopulationSite ctx.byteModel original)
    (dests : List ValueId) (arg : SMTCheckedTerm (.bv site.subject.width))
    (request : SMTTypedRequest (.bv site.subject.width)) (built : site.toRequest arg = .ok request)
    (state : MachineState) (operand : Int) (env : SMTEnv)
    (lookup : state.lookupValue site.operand = some (.int site.subject.width operand))
    (source : arg.term.eval env = BitVec.ofInt site.subject.width operand) :
    Sem.run (evalBodyStep recurse ctx depth strategy (original,dests)) state =
      Sem.run (publishComputedUnary ctx original dests (.int site.subject.width
        (Int.ofNat (request.target.eval env).toNat))) state :=
  unaryBody_of_origin recurse ctx depth strategy original site.origin dests state _
    (site.request_outcome ctx original arg request built state operand env lookup source)

/-- Actual checked gates also preserve the complete production body outcome. -/
theorem PopulationSite.body_gate (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (original : Inst) (site : PopulationSite ctx.byteModel original)
    (dests : List ValueId) (base next : Nat) (env : Assignment) (state : MachineState)
    (operand : Int) (result : BitVec site.subject.width)
    (lookup : state.lookupValue site.operand = some (.int site.subject.width operand))
    (executed : site.subject.checkedCode base next (BitVec.ofInt site.subject.width operand) env = some result) :
    Sem.run (evalBodyStep recurse ctx depth strategy (original,dests)) state =
      Sem.run (publishComputedUnary ctx original dests (.int site.subject.width (Int.ofNat result.toNat))) state :=
  unaryBody_of_origin recurse ctx depth strategy original site.origin dests state _
    (site.gate_outcome ctx original base next env state operand result lookup executed)

/-- The actual returned request reaches the production body binder, including its refusals. -/
theorem ZeroCountSite.body_request (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (original : Inst) (site : ZeroCountSite ctx.byteModel original)
    (dests : List ValueId) (arg : SMTCheckedTerm (.bv site.subject.width))
    (request : SMTTypedRequest (.bv site.subject.width)) (built : site.toRequest arg = .ok request)
    (state : MachineState) (operand : Int) (env : SMTEnv)
    (lookup : state.lookupValue site.operand = some (.int site.subject.width operand))
    (source : arg.term.eval env = BitVec.ofInt site.subject.width operand) :
    Sem.run (evalBodyStep recurse ctx depth strategy (original,dests)) state =
      Sem.run (publishComputedUnary ctx original dests (.int site.subject.width
        (Int.ofNat (request.target.eval env).toNat))) state :=
  unaryBody_of_origin recurse ctx depth strategy original site.origin dests state _
    (site.request_outcome ctx original arg request built state operand env lookup source)

/-- Actual checked gates also preserve the complete production body outcome. -/
theorem ZeroCountSite.body_gate (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (original : Inst) (site : ZeroCountSite ctx.byteModel original)
    (dests : List ValueId) (base next : Nat) (env : Assignment) (state : MachineState)
    (operand : Int) (result : BitVec site.subject.width)
    (lookup : state.lookupValue site.operand = some (.int site.subject.width operand))
    (executed : site.subject.checkedCode base next (BitVec.ofInt site.subject.width operand) env = some result) :
    Sem.run (evalBodyStep recurse ctx depth strategy (original,dests)) state =
      Sem.run (publishComputedUnary ctx original dests (.int site.subject.width (Int.ofNat result.toNat))) state :=
  unaryBody_of_origin recurse ctx depth strategy original site.origin dests state _
    (site.gate_outcome ctx original base next env state operand result lookup executed)

end TrustIr
