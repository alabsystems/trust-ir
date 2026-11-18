-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import SemRUnsignedDivision
import TrustIr.Proofs.GenericCoroPrefixLayer

/-! A scalar transition relation between the two existing executors.

The statement names the original node, operand lookups, destination and source
declaration check. It does not assume either execution succeeds or assume a
translation theorem. This component concerns U64 division and register state;
it grants no whole-function, memory, source/ABI or compiler proof authority.
-/

namespace SemR.CanonicalScalarStep

def divisionNode (left right destination : Nat) : SemR.Node :=
  { inst := .binop .udiv (.int .u64) left right, results := [destination] }

def sourceAfter (before : SemR.Core) (destination quotient : Nat) : SemR.Core :=
  { before with
    pc := before.pc + 1,
    env := (destination, .int .u64 quotient) :: before.env }

/-- The actual private temporary is retired unless it is the destination.
This definition records a state update, not an instruction evaluator. -/
def targetAfter (before : TrustIr.MachineState) (destination quotient : Nat) :
    TrustIr.MachineState :=
  let fresh := (before.bindValue (.int 64 (quotient : Int))).2
  let published := { fresh with
    locals := fresh.locals.set ⟨destination⟩ (.int 64 (quotient : Int)),
    nextValueId := max fresh.nextValueId (destination + 1) }
  if before.nextValueId = destination then published
  else { published with locals := fun id =>
    if id == ⟨before.nextValueId⟩ then none else published.locals id }

open TrustIr in
@[simp] private theorem run_get (state : MachineState) :
    Sem.run Sem.getState state = .ok (state, state) := rfl

open TrustIr in
@[simp] private theorem run_set (state after : MachineState) :
    Sem.run (Sem.setState after) state = .ok ((), after) := rfl

open TrustIr in
@[simp] private theorem run_throw {α : Type} (state : MachineState) (error : SemError) :
    Sem.run (throw error : Sem α) state = .error error := rfl

open TrustIr in
@[simp] private theorem run_lookup (state : MachineState) (id : ValueId) :
    Sem.run (Sem.lookupValue id) state =
      match state.lookupValue id with
      | some value => .ok (value, state)
      | none => .error (.typeError s!"undefined SSA value: {repr id}") := by
  cases found : state.lookupValue id <;>
    simp [Sem.lookupValue, Sem.run_bind, Except.bind, found, Sem.run_pure,
      Sem.throwTypeError] <;> rfl

open TrustIr in
@[simp] private theorem run_fresh (state : MachineState) (value : Value) :
    Sem.run (Sem.bindFresh value) state = .ok (state.bindValue value) := rfl

open TrustIr in
@[simp] private theorem except_pure {α : Type} (value : α) :
    (pure value : Except SemError α) = .ok value := rfl

open TrustIr in
@[simp] private theorem run_map {α β : Type} (f : α → β) (action : Sem α)
    (state : MachineState) :
    Sem.run (f <$> action) state =
      (Sem.run action state).map (fun (value, after) => (f value, after)) := rfl

open TrustIr in
theorem target_step_raw (recurse : GenericCoro.Prefix.Recurse) (ctx : EvalContext)
    (depth : Nat) (strategy : PanicStrategy) (before : MachineState)
    (left right destination dividend divisor : Nat)
    (leftLookup : before.lookupValue ⟨left⟩ = some (.int 64 (dividend : Int)))
    (rightLookup : before.lookupValue ⟨right⟩ = some (.int 64 (divisor : Int)))
    (declarations : ctx.instructionResultTypes (.BinOp .UDiv .U64 ⟨left⟩ ⟨right⟩)
      [⟨destination⟩] 1 = .ok [.U64])
    (leftRange : dividend < 2 ^ 64) (rightRange : divisor < 2 ^ 64) :
    Sem.run (GenericCoro.Prefix.evalBodyStep recurse ctx depth strategy
      (.BinOp .UDiv .U64 ⟨left⟩ ⟨right⟩, [⟨destination⟩])) before =
      if divisor = 0 then .error (.ub "unsigned division by zero")
      else .ok (.yield (), targetAfter before destination (dividend / divisor)) := by
  have leftFound : before.locals ⟨left⟩ = some (.int 64 (dividend : Int)) := leftLookup
  have rightFound : before.locals ⟨right⟩ = some (.int 64 (divisor : Int)) := rightLookup
  by_cases zero : divisor = 0
  · subst divisor
    simp [GenericCoro.Prefix.evalBodyStep, stepInstWithContext, stepInst, semBinOp,
      BinOp.isMinMax, semBinOpDeterministic, Sem.run_bind, leftLookup, rightLookup,
      semBinOpValues, semIntBinOp, Sem.rejectPartial, Sem.run_pure, Sem.run, StateT.run, StateT.bind,
      StateT.pure, StateT.map, StateT.get, StateT.lift, bind, pure, Functor.map, Except.bind,
      Except.pure, Except.map, throw, throwThe, MonadExceptOf.throw, Sem.lookupValue,
      Sem.getState, MachineState.lookupValue, ValueMap.get, leftFound, rightFound]
  · have computed := (CanonicalUnsignedDivision.value 64 dividend divisor
      leftRange rightRange zero).2
    by_cases same : before.nextValueId = destination <;>
      simp [GenericCoro.Prefix.evalBodyStep, stepInstWithContext, stepInst, semBinOp,
      BinOp.isMinMax, semBinOpDeterministic, Sem.run_bind, leftLookup, rightLookup,
      semBinOpValues, computed, same, Sem.rejectPartial, Sem.run_pure,
      EvalContext.bindInstructionResults, EvalContext.checkInstructionResults,
      declarations, checkSSACharValues, checkSSACharValue, bindInstrResultDests,
      bindResultDests, MachineState.bindValue, MachineState.lookupValue,
      ValueMap.get, ValueMap.set, targetAfter, zero, bind, Except.bind, Except.map, leftFound, rightFound,
      Sem.run, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.get, StateT.set,
      StateT.lift, pure, Functor.map, Except.pure, throw, throwThe, MonadExceptOf.throw,
      Sem.lookupValue, Sem.getState, Sem.setState, Sem.bindFresh]

theorem source_step (m : SemR.Module) (before : SemR.Core)
    (left right destination dividend divisor : Nat)
    (atNode : SemR.nth? before.block.body before.pc =
      some (divisionNode left right destination))
    (leftLookup : SemR.lookupEnv before.env left = some (.int .u64 dividend))
    (rightLookup : SemR.lookupEnv before.env right = some (.int .u64 divisor))
    (leftRange : dividend < 2 ^ 64) (rightRange : divisor < 2 ^ 64) :
    SemR.stepCore m before =
      if divisor = 0 then .done (.ub "unsigned division by zero")
      else .cont (sourceAfter before destination (dividend / divisor)) := by
  by_cases zero : divisor = 0 <;>
    simp [SemR.stepCore, atNode, SemR.execNode, divisionNode, SemR.binopStep,
    SemR.getV, leftLookup, rightLookup, SemR.evalBinop, SemR.expectTy,
    SemR.Val.ty, SemR.Ty.beq, SemR.IntTy.code, SemR.IntTy.bits, SemR.modulus,
    leftRange, rightRange, SemR.isBoolTy, SemR.expectInt, SemR.rejectPoison,
    SemR.intBin, SemR.liftOp, SemR.bindResults, SemR.next, SemR.ofR,
    sourceAfter, bind, pure, SemR.R.bind, zero]

/-- The scalar register view uses actual U64 residues and Bool values only.
Other SemR values have no scalar image. This is not a heap or full-value
embedding and cannot establish a whole-program simulation. -/
def scalarImage : SemR.Val → Option TrustIr.Value
  | .int .u64 raw => some (.int 64 (raw : Int))
  | .bool value => some (.bool value)
  | _ => none

def RegistersAgree (source : SemR.Core) (target : TrustIr.MachineState) : Prop :=
  ∀ id, (SemR.lookupEnv source.env id).bind scalarImage = target.lookupValue ⟨id⟩

theorem source_after_lookup (before : SemR.Core) (destination quotient id : Nat) :
    SemR.lookupEnv (sourceAfter before destination quotient).env id =
      if destination = id then some (.int .u64 quotient)
      else SemR.lookupEnv before.env id := by
  simp [sourceAfter, SemR.lookupEnv]

open TrustIr in
/-- A live register may not be silently overwritten by the canonical fresh
temporary. Its absence is independently owed before this step. -/
theorem target_after_lookup (before : MachineState) (destination quotient id : Nat)
    (fresh : before.lookupValue ⟨before.nextValueId⟩ = none) :
    (targetAfter before destination quotient).lookupValue ⟨id⟩ =
      if destination = id then some (.int 64 (quotient : Int))
      else before.lookupValue ⟨id⟩ := by
  have absent : before.locals ⟨before.nextValueId⟩ = none := fresh
  by_cases same : before.nextValueId = destination <;>
    by_cases atDestination : id = destination <;>
      by_cases atTemporary : id = before.nextValueId <;>
        simp_all [targetAfter, MachineState.bindValue, MachineState.lookupValue,
          ValueMap.get, ValueMap.set] <;> omega

theorem registers_preserved (source : SemR.Core) (target : TrustIr.MachineState)
    (destination quotient : Nat) (related : RegistersAgree source target)
    (fresh : target.lookupValue ⟨target.nextValueId⟩ = none) :
    RegistersAgree (sourceAfter source destination quotient)
      (targetAfter target destination quotient) := by
  intro id
  rw [source_after_lookup, target_after_lookup target destination quotient id fresh]
  by_cases same : destination = id
  · simp [same, scalarImage]
  · simpa only [same, if_false] using related id

open TrustIr in
/-- Full success and an arbitrary continuation over BOTH post-states. The
actual steppers, destination publication and zero-divisor refusal are fixed;
the continuation can therefore be the next instruction's state relation. -/
theorem division_step_wp_iff (m : SemR.Module) (source : SemR.Core)
    (recurse : GenericCoro.Prefix.Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (target : MachineState)
    (left right destination dividend divisor : Nat)
    (atNode : SemR.nth? source.block.body source.pc =
      some (divisionNode left right destination))
    (leftLookup : SemR.lookupEnv source.env left = some (.int .u64 dividend))
    (rightLookup : SemR.lookupEnv source.env right = some (.int .u64 divisor))
    (related : RegistersAgree source target)
    (declarations : ctx.instructionResultTypes (.BinOp .UDiv .U64 ⟨left⟩ ⟨right⟩)
      [⟨destination⟩] 1 = .ok [.U64])
    (leftRange : dividend < 2 ^ 64) (rightRange : divisor < 2 ^ 64)
    (post : SemR.Core → MachineState → Prop) :
    (∃ sourceNext targetNext,
      SemR.stepCore m source = .cont sourceNext ∧
      Sem.run (GenericCoro.Prefix.evalBodyStep recurse ctx depth strategy
        (.BinOp .UDiv .U64 ⟨left⟩ ⟨right⟩, [⟨destination⟩])) target =
          .ok (.yield (), targetNext) ∧ post sourceNext targetNext) ↔
      divisor ≠ 0 ∧ post (sourceAfter source destination (dividend / divisor))
        (targetAfter target destination (dividend / divisor)) := by
  have targetLeft : target.lookupValue ⟨left⟩ = some (.int 64 (dividend : Int)) := by
    rw [← related left, leftLookup]; rfl
  have targetRight : target.lookupValue ⟨right⟩ = some (.int 64 (divisor : Int)) := by
    rw [← related right, rightLookup]; rfl
  rw [source_step m source left right destination dividend divisor atNode
    leftLookup rightLookup leftRange rightRange,
    target_step_raw recurse ctx depth strategy target left right destination
      dividend divisor targetLeft targetRight declarations leftRange rightRange]
  by_cases zero : divisor = 0 <;> simp [zero]

open TrustIr in
/-- The composed one-step simulation for the scalar register view. Freshness
is an input invariant still to be discharged for reachable whole-body states. -/
theorem division_step_registers_iff (m : SemR.Module) (source : SemR.Core)
    (recurse : GenericCoro.Prefix.Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (target : MachineState)
    (left right destination dividend divisor : Nat)
    (atNode : SemR.nth? source.block.body source.pc =
      some (divisionNode left right destination))
    (leftLookup : SemR.lookupEnv source.env left = some (.int .u64 dividend))
    (rightLookup : SemR.lookupEnv source.env right = some (.int .u64 divisor))
    (related : RegistersAgree source target)
    (declarations : ctx.instructionResultTypes (.BinOp .UDiv .U64 ⟨left⟩ ⟨right⟩)
      [⟨destination⟩] 1 = .ok [.U64])
    (leftRange : dividend < 2 ^ 64) (rightRange : divisor < 2 ^ 64)
    (fresh : target.lookupValue ⟨target.nextValueId⟩ = none) :
    (∃ sourceNext targetNext,
      SemR.stepCore m source = .cont sourceNext ∧
      Sem.run (GenericCoro.Prefix.evalBodyStep recurse ctx depth strategy
        (.BinOp .UDiv .U64 ⟨left⟩ ⟨right⟩, [⟨destination⟩])) target =
          .ok (.yield (), targetNext) ∧ RegistersAgree sourceNext targetNext) ↔
      divisor ≠ 0 := by
  have nextRelated := registers_preserved source target destination
    (dividend / divisor) related fresh
  simpa only [nextRelated, and_true] using
    (division_step_wp_iff m source recurse ctx depth strategy target left right
      destination dividend divisor atNode leftLookup rightLookup related
      declarations leftRange rightRange RegistersAgree)

end SemR.CanonicalScalarStep
