-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameConstructionValidity

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

private theorem get_member {α : Type} {values : List α} {index : Nat} {value : α}
    (found : trustIrListGet? values index = some value) : value ∈ values := by
  induction values generalizing index with
  | nil => cases found
  | cons first rest ih =>
    cases index with
    | zero => simp at found; subst value; exact .head _
    | succ index => exact .tail _ (ih found)

private theorem set_all {α : Type} (P : α → Prop) (values : List α) (index : Nat) (value : α)
    (original : ∀ child ∈ values, P child) (inserted : P value) :
    ∀ child ∈ values.set index value, P child := by
  induction values generalizing index with
  | nil => intro child member; cases member
  | cons first rest ih =>
    cases index with
    | zero =>
      intro child member
      cases member with
      | head => exact inserted
      | tail _ member => exact original child (.tail first member)
    | succ index =>
      intro child member
      cases member with
      | head => exact original first (.head rest)
      | tail _ member => exact ih index (fun child member => original child (.tail first member)) child member

private theorem pure_minted (bound : Nat) (value result : Value) (valid : MintedValue bound value)
    (run : Except.ok value = Except.ok (ε := SemError) result) : MintedValue bound result := by
  cases run
  exact valid

/-- Checked closure projection selects an original recursively valid capture. -/
theorem closure_extract_minted (bound : Nat) (ctx : EvalContext) (ty : Ty)
    (cid : ClosureTyId) (fn : FuncId) (captures : List Value) (field : Nat) (result : Value)
    (valid : MintedArgs bound captures)
    (run : closureExtract ctx ty cid fn captures field = .ok result) : MintedValue bound result := by
  unfold closureExtract at run
  simp only [bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at run
  repeat' first
    | (apply pure_minted bound _ result ?_ run)
      exact valid _ (get_member (by assumption))
    | contradiction
    | split at run

/-- Checked closure update keeps nominal/code identity and all other captures. -/
theorem closure_insert_minted (bound : Nat) (ctx : EvalContext) (ty : Ty)
    (cid : ClosureTyId) (fn : FuncId) (captures : List Value) (field : Nat) (inserted result : Value)
    (valid : MintedArgs bound captures) (incoming : MintedValue bound inserted)
    (run : closureInsert ctx ty cid fn captures field inserted = .ok result) : MintedValue bound result := by
  have updated : MintedValue bound (.typedClosure cid fn (captures.set field inserted)) :=
    (mintedValue_iff_shape bound _).2 (set_all (MintedValue bound) captures field inserted valid incoming)
  unfold closureInsert at run
  simp only [bind, pure, Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at run
  repeat' first
    | exact pure_minted bound _ result updated run
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

private theorem pure_step_success (id : ValueId) (s final : MachineState) (result : InstrResult)
    (valid : WellMintedState s)
    (run : Sem.run (pure (InstrResult.value (some id))) s = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  change Except.ok (.value (some id), s) = Except.ok (result, final) at run
  cases run
  exact ⟨id, rfl, valid⟩

private theorem bare_extract_step_success (ctx : EvalContext) (ty : Ty) (operand : ValueId) (field : Nat)
    (s final : MachineState) (result : InstrResult) (valid : WellMintedState s)
    (run : Sem.run (stepInst (.ExtractField ty operand field) ctx.byteModel) s = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  obtain ⟨id, middle, computed, tail⟩ := split_bind_success (semExtractField ty operand field) _ s final result run
  change Except.ok (.value (some id), middle) = Except.ok (result, final) at tail
  cases tail
  exact ⟨id, rfl, valid.extract_field_success s final ty operand id field computed⟩

private theorem bare_insert_step_success (ctx : EvalContext) (ty : Ty) (operand rhs : ValueId) (field : Nat)
    (s final : MachineState) (result : InstrResult) (valid : WellMintedState s)
    (run : Sem.run (stepInst (.InsertField ty operand field rhs) ctx.byteModel) s = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  obtain ⟨id, middle, computed, tail⟩ := split_bind_success (semInsertField ty operand field rhs) _ s final result run
  change Except.ok (.value (some id), middle) = Except.ok (result, final) at tail
  cases tail
  exact ⟨id, rfl, valid.insert_field_success s final ty operand rhs id field computed⟩

/-- Actual contextual projection preserves identity through typed closure or
ordinary aggregate paths, with original declaration and lane checks retained. -/
theorem WellMintedState.extract_field_step_success (ctx : EvalContext) (ty : Ty)
    (operand : ValueId) (field : Nat) (s final : MachineState) (result : InstrResult)
    (valid : WellMintedState s)
    (run : Sem.run (stepInstWithContext ctx (.ExtractField ty operand field)) s = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  obtain ⟨held, middle, looked, tail⟩ := split_bind_success (Sem.lookupValue operand) _ s final result run
  obtain ⟨lookup, same⟩ := lookup_success s middle operand held looked
  subst middle
  have original := valid.values operand held lookup
  cases held with
  | typedClosure cid fn captures =>
    cases computed : closureExtract ctx ty cid fn captures field with
    | error error =>
      simp [computed, Sem.run, StateT.run, StateT.bind, StateT.lift,
        throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at tail
    | ok value =>
      apply mapped_fresh_success s final value result valid
        (closure_extract_minted _ ctx ty _ _ _ field value ((mintedValue_iff_shape _ _).1 original) computed)
      simpa only [computed] using tail
  | _ =>
    simp only [pure_bind] at tail
    obtain ⟨ordinary, after, executed, tail⟩ := split_bind_success (stepInst (.ExtractField ty operand field) ctx.byteModel) _ s final result tail
    obtain ⟨id, shape, preserved⟩ := bare_extract_step_success ctx ty operand field s after ordinary valid executed
    subst ordinary
    obtain ⟨value, middle, looked, tail⟩ := split_bind_success (Sem.lookupValue id) _ after final result tail
    obtain ⟨_, same⟩ := lookup_success after middle id value looked
    subst middle
    simp only [Sem.throwUB, pure_bind] at tail
    repeat' first
      | exact pure_step_success _ after final result preserved tail
      | exact False.elim (throw_success after final result _ tail)
      | split at tail <;> try simp only [pure_bind] at tail

private theorem reject_success_state (value : Value) (s final : MachineState)
    (run : Sem.run (Sem.rejectPartial value "InsertField") s = .ok ((), final)) : final = s := by
  cases value <;>
    simp [Sem.rejectPartial, Sem.run, Sem.throwUB, StateT.run, StateT.pure,
      StateT.lift, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      bind, Except.bind] at run <;> exact run.symm

set_option maxHeartbeats 1000000 in
/-- Actual contextual insertion retains all original SSA/declaration, enum-tag
and replacement-lane guards, and the typed closure update path. -/
theorem WellMintedState.insert_field_step_success (ctx : EvalContext) (ty : Ty)
    (operand rhs : ValueId) (field : Nat) (s final : MachineState) (result : InstrResult)
    (valid : WellMintedState s)
    (run : Sem.run (stepInstWithContext ctx (.InsertField ty operand field rhs)) s = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  obtain ⟨held, middle, looked, tail⟩ := split_bind_success (Sem.lookupValue operand) _ s final result run
  obtain ⟨lookup, same⟩ := lookup_success s middle operand held looked
  subst middle
  obtain ⟨inserted, middle, looked, tail⟩ := split_bind_success (Sem.lookupValue rhs) _ s final result tail
  obtain ⟨lookupRhs, same⟩ := lookup_success s middle rhs inserted looked
  subst middle
  have original := valid.values operand held lookup
  have incoming := valid.values rhs inserted lookupRhs
  cases held with
  | typedClosure cid fn captures =>
    cases computed : closureInsert ctx ty cid fn captures field inserted with
    | error error =>
      simp [computed, Sem.run, StateT.run, StateT.bind, StateT.lift,
        throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at tail
    | ok value =>
      apply mapped_fresh_success s final value result valid
        (closure_insert_minted _ ctx ty _ _ _ field inserted value ((mintedValue_iff_shape _ _).1 original) incoming computed)
      simpa only [computed] using tail
  | _ =>
    simp only [pure_bind] at tail
    cases tableEq : ctx.localTypes with
    | none =>
      simp only [tableEq, Sem.throwUB, Sem.throwTypeError, pure_bind] at tail
      repeat' first
        | exact bare_insert_step_success ctx _ operand rhs field s final result valid tail
        | exact False.elim (throw_success s final result _ tail)
        | split at tail <;> try simp only [pure_bind] at tail
    | some table =>
      simp only [tableEq] at tail
      obtain ⟨unit, middle, guarded, tail⟩ := split_bind_success (Sem.rejectPartial _ "InsertField") _ s final result tail
      cases unit
      have same := reject_success_state _ s middle guarded
      subst middle
      obtain ⟨unit, middle, guarded, tail⟩ := split_bind_success (Sem.rejectPartial inserted "InsertField") _ s final result tail
      cases unit
      have same := reject_success_state inserted s middle guarded
      subst middle
      simp only [Sem.throwUB, Sem.throwTypeError, pure_bind] at tail
      repeat' first
        | exact bare_insert_step_success ctx _ operand rhs _ s final result valid tail
        | exact False.elim (throw_success s final result _ tail)
        | split at tail <;> try simp only [pure_bind] at tail

end TrustIr.FrameLifetime
