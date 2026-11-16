-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYUnaryBody
import TrustIr.Proofs.AYCastReplay
import TrustIr.Proofs.AYDivisionReplay
import TrustIr.Proofs.GenericCoroPrefixLoop

namespace TrustIr.AYUnaryReplay
open TrustIrExpr GenericCoro.Prefix

abbrev Row := Inst × List ValueId

inductive Site (model : ByteModel) (original : Inst) where
  | permutation (site : IntegerPermutationSite model original)
  | population (site : PopulationSite model original)
  | zeros (site : ZeroCountSite model original)

def Site.width {model original} : Site model original → Nat
  | .permutation s => s.subject.width
  | .population s => s.subject.width
  | .zeros s => s.subject.width
def Site.operand {model original} : Site model original → ValueId
  | .permutation s => s.operand
  | .population s => s.operand
  | .zeros s => s.operand
theorem Site.positive {model original} (site : Site model original) : 0 < site.width := by
  cases site with
  | permutation s => exact s.subject.positive
  | population s => exact s.subject.positive
  | zeros s => exact s.subject.positive

def Site.ofInst (model : ByteModel) (original : Inst) : Except String (Site model original) :=
  match original with
  | .UnOp .BitReverse ty id => .permutation <$> IntegerPermutationSite.ofInst model (.UnOp .BitReverse ty id)
  | .UnOp .BSwap ty id => .permutation <$> IntegerPermutationSite.ofInst model (.UnOp .BSwap ty id)
  | .UnOp .CtPop ty id => .population <$> PopulationSite.ofInst model (.UnOp .CtPop ty id)
  | .UnOp .CtLz ty id => .zeros <$> ZeroCountSite.ofInst model (.UnOp .CtLz ty id)
  | .UnOp .CtTz ty id => .zeros <$> ZeroCountSite.ofInst model (.UnOp .CtTz ty id)
  | _ => .error "body replay requires a supported scalar bit/count instruction"

def Site.toRequest {model original} (site : Site model original) :
    SMTCheckedTerm (.bv site.width) → Except String (SMTTypedRequest (.bv site.width)) :=
  match site with
  | .permutation s => s.toRequest
  | .population s => s.toRequest
  | .zeros s => s.toRequest

theorem Site.body_request {original : Inst} (ctx : EvalContext) (site : Site ctx.byteModel original)
    (arg : SMTCheckedTerm (.bv site.width)) (request : SMTTypedRequest (.bv site.width))
    (built : site.toRequest arg = .ok request) (state : MachineState) (operand : Int) (env : SMTEnv)
    (lookup : state.lookupValue site.operand = some (.int site.width operand))
    (source : arg.term.eval env = BitVec.ofInt site.width operand)
    (recurse : Recurse) (depth : Nat) (strategy : PanicStrategy) (dests : List ValueId) :
    Sem.run (evalBodyStep recurse ctx depth strategy (original,dests)) state =
      Sem.run (publishComputedUnary ctx original dests (.int site.width (Int.ofNat (request.target.eval env).toNat))) state := by
  cases site with
  | permutation s => exact s.body_request recurse ctx depth strategy original dests arg request built state operand env lookup source
  | population s => exact s.body_request recurse ctx depth strategy original dests arg request built state operand env lookup source
  | zeros s => exact s.body_request recurse ctx depth strategy original dests arg request built state operand env lookup source

theorem Site.body_error {original : Inst} (ctx : EvalContext) (site : Site ctx.byteModel original)
    (state : MachineState) (error : SemError) (failed : Sem.run (stepInstWithContext ctx original) state = .error error)
    (recurse : Recurse) (depth : Nat) (strategy : PanicStrategy) (dests : List ValueId) :
    Sem.run (evalBodyStep recurse ctx depth strategy (original,dests)) state = .error error := by
  cases site with
  | permutation s =>
    have origin := s.origin
    have moved := congrArg (fun inst => Sem.run (stepInstWithContext ctx inst) state) origin
    have actual := unaryBody_error recurse ctx depth strategy s.subject.op.irOp s.subject.ty s.operand dests state error (moved.symm.trans failed)
    exact (congrArg (fun inst => Sem.run (evalBodyStep recurse ctx depth strategy (inst,dests)) state) origin).trans actual
  | population s =>
    have moved := congrArg (fun inst => Sem.run (stepInstWithContext ctx inst) state) s.origin
    have actual := unaryBody_error recurse ctx depth strategy .CtPop s.subject.ty s.operand dests state error (moved.symm.trans failed)
    exact (congrArg (fun inst => Sem.run (evalBodyStep recurse ctx depth strategy (inst,dests)) state) s.origin).trans actual
  | zeros s =>
    have moved := congrArg (fun inst => Sem.run (stepInstWithContext ctx inst) state) s.origin
    have actual := unaryBody_error recurse ctx depth strategy s.subject.direction.irOp s.subject.ty s.operand dests state error (moved.symm.trans failed)
    exact (congrArg (fun inst => Sem.run (evalBodyStep recurse ctx depth strategy (inst,dests)) state) s.origin).trans actual

/-- Actual source-bound requests or actual primitive errors, never a caller's
desired answer or final state. Both original instruction and entry state index
the receipt. -/
inductive Node (ctx : EvalContext) (row : Row) (state : MachineState) where
  | division (checked : AYDivisionReplay.Node ctx row state)
  | cast (checked : AYCastReplay.Node ctx row state)
  | request (site : Site ctx.byteModel row.fst)
      (arg : SMTCheckedTerm (.bv site.width)) (target : SMTTypedRequest (.bv site.width))
      (built : site.toRequest arg = .ok target) (operand : Int) (env : SMTEnv)
      (lookup : state.lookupValue site.operand = some (.int site.width operand))
      (source : arg.term.eval env = BitVec.ofInt site.width operand)
  | sourceError (site : Site ctx.byteModel row.fst) (error : SemError)
      (failed : Sem.run (stepInstWithContext ctx row.fst) state = .error error)

def Node.run {ctx row state} : Node ctx row state → Except SemError (ForInStep Unit × MachineState)
  | .division checked => checked.outcome
  | .cast checked => checked.outcome
  | .request site _ target _ _ env _ _ =>
    Sem.run (publishComputedUnary ctx row.fst row.snd (.int site.width (Int.ofNat (target.target.eval env).toNat))) state
  | .sourceError _ error _ => .error error

theorem Node.correct {ctx row state} (node : Node ctx row state) (recurse : Recurse) (depth : Nat)
    (strategy : PanicStrategy) : Sem.run (evalBodyStep recurse ctx depth strategy row) state = node.run := by
  cases node with
  | division checked => exact checked.correct recurse depth strategy
  | cast checked => exact checked.correct recurse depth strategy
  | request site arg target built operand env lookup source => exact site.body_request ctx arg target built state operand env lookup source recurse depth strategy row.snd
  | sourceError site error failed => exact site.body_error ctx state error failed recurse depth strategy row.snd

def Node.sourceFailure {ctx row state} (site : Site ctx.byteModel row.fst) : Except String (Node ctx row state) :=
  match actual : Sem.run (stepInstWithContext ctx row.fst) state with
  | .error error => .ok (.sourceError site error actual)
  | .ok _ => .error "body replay source has no matching integer carrier"

private def Node.buildUnary (ctx : EvalContext) (row : Row) (state : MachineState) : Except String (Node ctx row state) := do
  let site ← Site.ofInst ctx.byteModel row.fst
  match found : state.lookupValue site.operand with
  | some (.int width operand) =>
    if same : width = site.width then
      let arg : SMTCheckedTerm (.bv site.width) := ⟨.bvConst site.width operand,[],site.positive,rfl,[],rfl⟩
      match built : site.toRequest arg with
      | .error reason => .error reason
      | .ok target => .ok (.request site arg target built operand SMTEnv.default
          (by simpa [same] using found) rfl)
    else Node.sourceFailure site
  | _ => Node.sourceFailure site

/-- Dispatch source-bound division and casts to their checked factories;
remaining reached instructions retain the existing unary admission policy. -/
def Node.build (ctx : EvalContext) (row : Row) (state : MachineState) : Except String (Node ctx row state) :=
  match row.1 with
  | .BinOp .UDiv _ _ _ | .BinOp .URem _ _ _ | .BinOp .SDiv _ _ _ | .BinOp .SRem _ _ _ =>
      Node.division <$> AYDivisionReplay.Node.build ctx row state
  | .Cast _ _ _ _ => Node.cast <$> AYCastReplay.Node.build ctx row state
  | _ => Node.buildUnary ctx row state

/-- A complete executed path through the ORIGINAL row list. Each successor
state is produced by the real publisher; a terminal error retains the entire
unexecuted suffix. These are point-execution receipts, not a codegen license. -/
inductive Trace (ctx : EvalContext) : List Row → MachineState → Type where
  | nil (state : MachineState) : Trace ctx [] state
  | failed {row rest state} (node : Node ctx row state) (error : SemError)
      (actual : node.run = .error error) : Trace ctx (row::rest) state
  | next {row rest state} (node : Node ctx row state) (after : MachineState)
      (actual : node.run = .ok (.yield (),after)) (tail : Trace ctx rest after) : Trace ctx (row::rest) state

def Trace.outcome {ctx rows state} : Trace ctx rows state → Except SemError (Unit × MachineState)
  | .nil state => .ok ((),state)
  | .failed _ error _ => .error error
  | .next _ _ _ tail => tail.outcome

def Trace.visited {ctx rows state} : Trace ctx rows state → Nat
  | .nil _ => 0
  | .failed _ _ _ => 1
  | .next _ _ _ tail => 1+tail.visited

def Trace.build (ctx : EvalContext) : (rows : List Row) → (state : MachineState) → Except String (Trace ctx rows state)
  | [],state => .ok (.nil state)
  | row::rest,state => do
    let node ← Node.build ctx row state
    match actual : node.run with
    | .error error => .ok (.failed node error actual)
    | .ok (.done (),_) => .error "body replay encountered an unexpected early exit"
    | .ok (.yield (),after) =>
      let tail ← Trace.build ctx rest after
      .ok (.next node after actual tail)

theorem Trace.correct {ctx rows state} (trace : Trace ctx rows state) (recurse : Recurse) (depth : Nat)
    (strategy : PanicStrategy) : Sem.run (evalBody recurse ctx depth strategy rows) state = trace.outcome := by
  induction trace with
  | nil state => rfl
  | failed node error actual =>
    rw [evalBody_cons, Sem.run_bind, node.correct recurse depth strategy, actual]
    rfl
  | next node after actual tail ih =>
    rw [evalBody_cons, Sem.run_bind, node.correct recurse depth strategy, actual]
    exact ih

theorem Trace.built_correct (ctx : EvalContext) (rows : List Row) (state : MachineState)
    (trace : Trace ctx rows state) (_built : Trace.build ctx rows state = .ok trace)
    (recurse : Recurse) (depth : Nat) (strategy : PanicStrategy) :
    Sem.run (evalBody recurse ctx depth strategy rows) state = trace.outcome := trace.correct recurse depth strategy

/-- The exact body result composes with arbitrary production continuation;
an error never evaluates that continuation. -/
theorem Trace.continuation_correct {α : Type} {ctx rows state} (trace : Trace ctx rows state)
    (recurse : Recurse) (depth : Nat) (strategy : PanicStrategy) (next : Sem α) :
    Sem.run (do evalBody recurse ctx depth strategy rows; next) state = (do
      let (_,after) ← trace.outcome
      Sem.run next after) := by
  rw [Sem.run_bind, trace.correct recurse depth strategy]
  cases trace.outcome <;> rfl

theorem Trace.visited_le {ctx rows state} (trace : Trace ctx rows state) : trace.visited ≤ rows.length := by
  induction trace with
  | nil _ => exact Nat.le_refl _
  | failed _ _ _ => simp [Trace.visited]
  | next _ _ _ _ ih => simp only [Trace.visited, List.length_cons]; omega

end TrustIr.AYUnaryReplay
