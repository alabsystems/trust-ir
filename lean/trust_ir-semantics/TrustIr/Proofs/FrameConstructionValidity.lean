-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameAggregateValidity
import TrustIr.Proofs.FrameUnaryValidity

namespace TrustIr.FrameLifetime

private theorem run_bind {α β : Type} (action : Sem α) (next : α → Sem β) (state : MachineState) :
    Sem.run (action >>= next) state =
      (Sem.run action state >>= fun pair => Sem.run (next pair.1) pair.2) := rfl

private theorem split_bind_success {α β : Type} (action : Sem α) (next : α → Sem β)
    (s final : MachineState) (result : β)
    (run : Sem.run (action >>= next) s = .ok (result, final)) :
    ∃ value middle, Sem.run action s = .ok (value, middle) ∧
      Sem.run (next value) middle = .ok (result, final) := by
  rw [run_bind] at run
  cases step : Sem.run action s with
  | error error => simp [step, bind, Except.bind] at run
  | ok pair => exact ⟨pair.1, pair.2, rfl, by simpa [step] using run⟩

private theorem lookup_success (s final : MachineState) (id : ValueId) (value : Value)
    (run : Sem.run (Sem.lookupValue id) s = .ok (value, final)) :
    s.lookupValue id = some value ∧ final = s := by
  cases lookup : s.lookupValue id with
  | none =>
    simp [Sem.lookupValue, Sem.run, Sem.getState, Sem.throwTypeError, lookup,
      StateT.run, StateT.bind, StateT.get, StateT.pure, StateT.lift, bind, pure,
      Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at run
  | some held =>
    simp [Sem.lookupValue, Sem.run, Sem.getState, lookup, StateT.run,
      StateT.bind, StateT.get, StateT.pure, bind, pure, Except.bind, Except.pure] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

private theorem zip_second_member {α β : Type} (left : List α) (right : List β)
    (a : α) (b : β) (member : (a,b) ∈ left.zip right) : b ∈ right := by
  induction left generalizing right with
  | nil => cases member
  | cons first rest ih =>
    cases right with
    | nil => cases member
    | cons second right =>
      cases member with
      | head => exact .head _
      | tail _ member => exact .tail _ (ih right member)

theorem record_lanes_minted (bound : Nat) (names : List String) (lanes : List Value)
    (valid : MintedArgs bound lanes) : MintedValue bound (.record (names.zip lanes)) := by
  intro lineage occurs
  cases occurs with
  | record member child => exact valid _ (zip_second_member names lanes _ _ member) lineage child

theorem enum_lanes_minted (bound width : Nat) (tag : Int) (lanes : List Value)
    (valid : MintedArgs bound lanes) : MintedValue bound (.aggregate (Value.intAt width tag :: lanes)) := by
  apply (mintedValue_iff_shape bound _).2
  intro value member
  cases member with
  | head => exact mintedValue_int bound _ _
  | tail _ member => exact valid value member

private theorem pure_minted (bound : Nat) (value result : Value) (valid : MintedValue bound value)
    (run : Except.ok value = Except.ok (ε := SemError) result) : MintedValue bound result := by
  cases run
  exact valid

/-- Actual table-aware enum and record construction retains all incoming
identities. The synthesized discriminant contains no frame identity. -/
theorem contextual_aggregate_value_minted (bound : Nat) (ctx : EvalContext) (ty : Ty)
    (variant : Option Nat) (lanes : List Value) (result : Value) (valid : MintedArgs bound lanes)
    (run : makeAggregateValueWithContext ctx ty variant lanes = .ok result) : MintedValue bound result := by
  unfold makeAggregateValueWithContext at run
  simp only [bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at run
  repeat' first
    | exact pure_minted bound _ result (enum_lanes_minted bound _ _ lanes valid) run
    | exact pure_minted bound _ result (record_lanes_minted bound _ lanes valid) run
    | contradiction
    | split at run

/-- Original array declaration, arity and register checks remain in execution. -/
theorem contextual_array_value_minted (bound : Nat) (ctx : EvalContext) (element : TyId)
    (count : Nat) (variant : Option Nat) (ids : List ValueId) (lanes : List Value) (result : Value)
    (valid : MintedArgs bound lanes)
    (run : makeArrayValueWithContext ctx element count variant ids lanes = .ok result) : MintedValue bound result := by
  unfold makeArrayValueWithContext at run
  simp only [bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at run
  repeat' first
    | exact pure_minted bound _ result (array_from_lanes_minted bound lanes valid) run
    | contradiction
    | split at run

/-- Checked typed closure construction preserves the original capture values. -/
theorem contextual_closure_value_minted (bound : Nat) (ctx : EvalContext)
    (cid : ClosureTyId) (fn : FuncId) (captures : List Value) (result : Value)
    (valid : MintedArgs bound captures)
    (run : makeClosureValue ctx cid fn captures = .ok result) : MintedValue bound result := by
  have capturesValid : MintedValue bound (.typedClosure cid fn captures) :=
    (mintedValue_iff_shape bound _).2 valid
  unfold makeClosureValue at run
  simp only [bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at run
  repeat' first
    | exact pure_minted bound _ result capturesValid run
    | contradiction
    | split at run

private theorem throw_success {α : Type} (s final : MachineState) (value : α) (error : SemError)
    (run : Sem.run (throw error : Sem α) s = .ok (value, final)) : False := by
  cases run

private theorem mapped_fresh_success (s final : MachineState) (value : Value) (result : InstrResult)
    (valid : WellMintedState s) (incoming : MintedValue s.nextFrameLineage value)
    (run : Sem.run (Sem.bindFresh value >>= fun id => pure (InstrResult.value (some id))) s = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  obtain ⟨id, middle, bound, tail⟩ := split_bind_success _ _ s final result run
  change Except.ok (.value (some id), middle) = Except.ok (result, final) at tail
  cases tail
  exact ⟨id, rfl, valid.fresh_success s final value id incoming bound⟩

private theorem checked_lanes_step_success (lookup : Sem (List Value))
    (compute : List Value → Except SemError Value) (s final : MachineState) (result : InstrResult)
    (valid : WellMintedState s)
    (read : ∀ lanes middle, Sem.run lookup s = .ok (lanes, middle) →
      middle = s ∧ MintedArgs s.nextFrameLineage lanes)
    (preserve : ∀ lanes value, MintedArgs s.nextFrameLineage lanes → compute lanes = .ok value →
      MintedValue s.nextFrameLineage value)
    (run : Sem.run (do
      let lanes ← lookup
      let value ← match compute lanes with
        | .ok value => pure value
        | .error error => throw error
      pure (InstrResult.value (some (← Sem.bindFresh value)))) s = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  obtain ⟨lanes, middle, looked, tail⟩ := split_bind_success _ _ s final result run
  obtain ⟨same, incoming⟩ := read lanes middle looked
  subst middle
  cases computed : compute lanes with
  | error error =>
    simp [computed, Sem.run, StateT.run, StateT.bind, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at tail
  | ok value =>
    apply mapped_fresh_success s final value result valid (preserve lanes value incoming computed)
    simpa only [computed] using tail

/-- Contextual MakeAggregate consumes the original declaration-aware path;
ordinary tuple/struct construction retains the original bare primitive. -/
theorem WellMintedState.make_aggregate_step_success (ctx : EvalContext) (ty : Ty)
    (variant : Option Nat) (fields : List ValueId) (s final : MachineState) (result : InstrResult)
    (valid : WellMintedState s)
    (run : Sem.run (stepInstWithContext ctx (.MakeAggregate ty variant fields)) s = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  cases ty with
  | Array element count =>
    exact checked_lanes_step_success (lookupLanes fields) (makeArrayValueWithContext ctx element count variant fields)
      s final result valid (fun lanes middle executed => lookup_lanes_success fields s middle lanes valid executed)
      (fun lanes value incoming executed => contextual_array_value_minted _ ctx element count variant fields lanes value incoming executed) run
  | Enum eid =>
    exact checked_lanes_step_success (lookupLanes fields) (makeAggregateValueWithContext ctx (.Enum eid) variant)
      s final result valid (fun lanes middle executed => lookup_lanes_success fields s middle lanes valid executed)
      (fun lanes value incoming executed => contextual_aggregate_value_minted _ ctx (.Enum eid) variant lanes value incoming executed) run
  | Record rid =>
    exact checked_lanes_step_success (lookupLanes fields) (makeAggregateValueWithContext ctx (.Record rid) variant)
      s final result valid (fun lanes middle executed => lookup_lanes_success fields s middle lanes valid executed)
      (fun lanes value incoming executed => contextual_aggregate_value_minted _ ctx (.Record rid) variant lanes value incoming executed) run
  | _ =>
    obtain ⟨id, middle, executed, tail⟩ := split_bind_success _ _ s final result run
    change Except.ok (.value (some id), middle) = Except.ok (result, final) at tail
    cases tail
    exact ⟨id, rfl, valid.make_aggregate_success s final _ variant fields id executed⟩

theorem WellMintedState.make_closure_step_success (ctx : EvalContext) (cid : ClosureTyId)
    (fn : FuncId) (captures : List ValueId) (s final : MachineState) (result : InstrResult)
    (valid : WellMintedState s)
    (run : Sem.run (stepInstWithContext ctx (.MakeClosure cid fn captures)) s = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final :=
  checked_lanes_step_success (captures.mapM Sem.lookupValue) (makeClosureValue ctx cid fn) s final result valid
    (fun values middle executed => lookup_args_success captures s middle values valid executed)
    (fun values value incoming executed => contextual_closure_value_minted _ ctx cid fn values value incoming executed) run

private theorem reject_success_state (value : Value) (s final : MachineState)
    (run : Sem.run (Sem.rejectPartial value "ArraySplat") s = .ok ((), final)) : final = s := by
  cases value <;>
    simp [Sem.rejectPartial, Sem.run, Sem.throwUB, StateT.run, StateT.pure,
      StateT.lift, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      bind, Except.bind] at run <;> exact run.symm

private theorem bare_splat_step_success (ty : Ty) (operand : ValueId)
    (ctx : EvalContext) (s final : MachineState) (result : InstrResult) (valid : WellMintedState s)
    (run : Sem.run (stepInst (.ArraySplat ty operand) ctx.byteModel) s = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  obtain ⟨id, middle, executed, tail⟩ := split_bind_success _ _ s final result run
  change Except.ok (.value (some id), middle) = Except.ok (result, final) at tail
  cases tail
  exact ⟨id, rfl, valid.array_splat_success s final ty operand id executed⟩

/-- ArraySplat retains the original element declaration, SSA table, exact type
identity check and poison guard before the original compact replication. -/
theorem WellMintedState.array_splat_step_success (ctx : EvalContext) (ty : Ty)
    (operand : ValueId) (s final : MachineState) (result : InstrResult) (valid : WellMintedState s)
    (run : Sem.run (stepInstWithContext ctx (.ArraySplat ty operand)) s = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  obtain ⟨value, middle, looked, tail⟩ := split_bind_success (Sem.lookupValue operand) _ s final result run
  obtain ⟨_, same⟩ := lookup_success s middle operand value looked
  subst middle
  obtain ⟨unit, middle, guarded, tail⟩ := split_bind_success _ _ s final result tail
  cases unit
  have same := reject_success_state value s middle guarded
  subst middle
  simp only [Sem.throwTypeError, Sem.throwUnsupported, pure_bind] at tail
  repeat' first
    | exact bare_splat_step_success _ operand ctx s final result valid tail
    | exact False.elim (throw_success s final result _ tail)
    | split at tail <;> try simp only [pure_bind] at tail

end TrustIr.FrameLifetime
