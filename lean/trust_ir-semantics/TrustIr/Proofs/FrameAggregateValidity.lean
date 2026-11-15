-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameResultValidity
import TrustIr.Proofs.FrameAliasValidity
import TrustIr.Semantics.Aggregate

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

theorem field_get_minted (bound : Nat) (aggregate value : Value) (index : Nat)
    (valid : MintedValue bound aggregate) (found : getField aggregate index = some value) :
    MintedValue bound value := by
  cases aggregate <;> simp only [getField] at found <;> try contradiction
  case aggregate values =>
    exact fun lineage occurs => valid lineage (.aggregate (get_member found) occurs)
  case record fields =>
    cases lookup : trustIrListGet? fields index with
    | none => simp [lookup] at found
    | some pair =>
      simp [lookup] at found
      subst value
      exact fun lineage occurs => valid lineage (.record (get_member lookup) occurs)

theorem field_set_minted (bound : Nat) (aggregate inserted output : Value) (index : Nat)
    (valid : MintedValue bound aggregate) (incoming : MintedValue bound inserted)
    (run : setField aggregate index inserted = some output) : MintedValue bound output := by
  cases aggregate <;> simp only [setField] at run <;> try contradiction
  case aggregate fields =>
    split at run
    · cases run
      exact (mintedValue_iff_shape bound _).2
        (set_all (MintedValue bound) fields index inserted ((mintedValue_iff_shape bound _).1 valid) incoming)
    · contradiction
  case record fields =>
    split at run
    · rename_i name _previous _found
      cases run
      exact (mintedValue_iff_shape bound _).2 (fun key value member =>
        set_all (fun pair : String × Value => MintedValue bound pair.2) fields index (name, inserted)
          (fun pair member => (mintedValue_iff_shape bound _).1 valid pair.1 pair.2 member)
          incoming (key,value) member)
    · contradiction

theorem element_get_minted (bound : Nat) (aggregate value : Value) (index : Nat)
    (valid : MintedValue bound aggregate) (found : getElement aggregate index = some value) :
    MintedValue bound value := by
  cases aggregate <;> simp only [getElement] at found <;> try contradiction
  case aggregate values => exact fun lineage occurs => valid lineage (.aggregate (get_member found) occurs)
  case sequence values => exact fun lineage occurs => valid lineage (.sequence (get_member found) occurs)
  case array values => exact fun lineage occurs => valid lineage (.array found occurs)

theorem element_set_minted (bound : Nat) (aggregate inserted output : Value) (index : Nat)
    (valid : MintedValue bound aggregate) (incoming : MintedValue bound inserted)
    (run : setElement aggregate index inserted = some output) : MintedValue bound output := by
  cases aggregate <;> simp only [setElement] at run <;> try contradiction
  case aggregate fields =>
    split at run
    · cases run
      exact (mintedValue_iff_shape bound _).2
        (set_all (MintedValue bound) fields index inserted ((mintedValue_iff_shape bound _).1 valid) incoming)
    · contradiction
  case sequence fields =>
    split at run
    · cases run
      exact (mintedValue_iff_shape bound _).2
        (set_all (MintedValue bound) fields index inserted ((mintedValue_iff_shape bound _).1 valid) incoming)
    · contradiction
  case array values =>
    cases changed : values.tree.set? index inserted with
    | none => simp [CompactArray.Packed.set?, changed] at run
    | some tree =>
      simp [CompactArray.Packed.set?, changed] at run
      cases run
      apply (mintedValue_iff_shape bound _).2
      intro other value found
      change tree.get? other = some value at found
      by_cases same : other = index
      · subst other
        rw [CompactArray.Tree.get_set_hit _ _ _ _ changed] at found
        cases found
        exact incoming
      · rw [CompactArray.Tree.get_set_other _ _ _ _ _ changed same] at found
        exact (mintedValue_iff_shape bound _).1 valid other value found

theorem array_from_lanes_minted (bound : Nat) (lanes : List Value) (valid : MintedArgs bound lanes) :
    MintedValue bound (.array (CompactArray.Packed.ofArray lanes.toArray)) := by
  apply (mintedValue_iff_shape bound _).2
  intro index value found
  rw [CompactArray.Packed.get_ofList] at found
  exact valid value (get_member found)

theorem array_uniform_minted (bound count : Nat) (value : Value) (valid : MintedValue bound value) :
    MintedValue bound (.array (CompactArray.Packed.uniform count value)) := by
  apply (mintedValue_iff_shape bound _).2
  intro index child found
  by_cases inside : index < count
  · simp [CompactArray.Packed.get?, CompactArray.Packed.uniform, CompactArray.Tree.get?, inside] at found
    subst child
    exact valid
  · simp [CompactArray.Packed.get?, CompactArray.Packed.uniform, CompactArray.Tree.get?, inside] at found

private theorem except_success {α β : Type} (action : Except SemError α)
    (next : α → Except SemError β) (result : β)
    (run : (action >>= next) = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases step : action with
  | error error => simp [step, bind, Except.bind] at run
  | ok value => exact ⟨value, rfl, by simpa [step] using run⟩

theorem vector_element_get_minted (bound : Nat) (ty : Ty) (aggregate value : Value) (index : Nat)
    (valid : MintedValue bound aggregate) (run : getVectorElement ty aggregate index = .ok value) :
    MintedValue bound value := by
  cases aggregate <;> simp only [getVectorElement] at run <;> try contradiction
  case vector lanes =>
    split at run
    · cases run
    · cases lookup : trustIrListGet? lanes index with
      | none => simp [lookup, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at run
      | some lane =>
        simp only [lookup] at run
        obtain ⟨unit, _, tail⟩ := except_success (checkVectorLaneType ty true lane) _ value run
        cases unit
        change Except.ok lane = Except.ok value at tail
        cases tail
        exact fun lineage occurs => valid lineage (.vector (get_member lookup) occurs)

theorem vector_element_set_minted (bound : Nat) (ty : Ty) (aggregate inserted output : Value) (index : Nat)
    (valid : MintedValue bound aggregate) (incoming : MintedValue bound inserted)
    (run : setVectorElement ty aggregate index inserted = .ok output) : MintedValue bound output := by
  cases aggregate <;> simp only [setVectorElement] at run <;> try contradiction
  case vector lanes =>
    cases ty <;> simp only at run <;> try (simp [throw, throwThe, MonadExceptOf.throw] at run)
    case Vector count elem =>
      obtain ⟨unit, _, tail1⟩ := except_success (checkVectorShape count elem lanes) _ output run
      cases unit
      obtain ⟨unit, _, tail2⟩ := except_success (checkVectorLaneType elem false inserted) _ output tail1
      cases unit
      cases lookup : trustIrListGet? lanes index with
      | none => simp [lookup, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at tail2
      | some previous =>
        simp only [lookup] at tail2
        obtain ⟨unit, _, tail4⟩ := except_success (checkVectorLaneType elem true previous) _ output tail2
        cases unit
        change Except.ok (.vector _) = Except.ok output at tail4
        cases tail4
        exact (mintedValue_iff_shape bound _).2
          (set_all (MintedValue bound) _ index inserted ((mintedValue_iff_shape bound _).1 valid) incoming)

private theorem reject_success_state (value : Value) (label : String) (s final : MachineState)
    (run : Sem.run (Sem.rejectPartial value label) s = .ok ((), final)) : final = s := by
  cases value <;>
    simp [Sem.rejectPartial, Sem.run, Sem.throwUB, StateT.run, StateT.pure,
      StateT.lift, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      bind, Except.bind] at run <;> exact run.symm

private theorem throw_success {α : Type} (s final : MachineState) (value : α) (error : SemError)
    (run : Sem.run (throw error : Sem α) s = .ok (value, final)) : False := by
  cases run

/-- Ordered construction lanes retain state and recursively valid values;
root poison checks remain part of the successful execution premise. -/
theorem lookup_lanes_success (ids : List ValueId) (s final : MachineState) (args : List Value)
    (valid : WellMintedState s)
    (run : Sem.run (lookupLanes ids) s = .ok (args, final)) :
    final = s ∧ MintedArgs s.nextFrameLineage args := by
  induction ids generalizing s final args with
  | nil =>
    change Except.ok ([], s) = Except.ok (args, final) at run
    cases run
    exact ⟨rfl, fun _ member => nomatch member⟩
  | cons id rest ih =>
    obtain ⟨head, middle, first, tail⟩ := split_bind_success _ _ s final args run
    obtain ⟨lookup, same⟩ := lookup_success s middle id head first
    subst middle
    obtain ⟨unit, middle, guarded, tail⟩ := split_bind_success _ _ s final args tail
    cases unit
    have same := reject_success_state head "MakeAggregate" s middle guarded
    subst middle
    obtain ⟨values, after, remaining, finished⟩ := split_bind_success _ _ s final args tail
    obtain ⟨same, minted⟩ := ih s after values valid remaining
    subst after
    change Except.ok (head :: values, s) = Except.ok (args, final) at finished
    cases finished
    exact ⟨rfl, fun value member => by
      cases member with
      | head => exact valid.values id head lookup
      | tail _ member => exact minted value member⟩

theorem WellMintedState.make_aggregate_success (s final : MachineState) (ty : Ty)
    (variant : Option Nat) (fields : List ValueId) (id : ValueId) (valid : WellMintedState s)
    (run : Sem.run (semMakeAggregate ty variant fields) s = .ok (id, final)) : WellMintedState final := by
  obtain ⟨lanes, middle, looked, tail⟩ := split_bind_success _ _ s final id run
  obtain ⟨same, incoming⟩ := lookup_lanes_success fields s middle lanes valid looked
  subst middle
  have built : MintedValue s.nextFrameLineage (.aggregate lanes) := (mintedValue_iff_shape _ _).2 incoming
  simp only [Sem.throwTypeError, Sem.throwUB, Sem.throwUnsupported, buildAggregate] at tail
  repeat' first
    | with_reducible exact valid.fresh_success s final _ id built tail
    | with_reducible exact valid.fresh_success s final _ id (array_from_lanes_minted _ lanes incoming) tail
    | with_reducible exact False.elim (throw_success s final id _ tail)
    | split at tail

theorem WellMintedState.array_splat_success (s final : MachineState) (ty : Ty)
    (operand id : ValueId) (valid : WellMintedState s)
    (run : Sem.run (semArraySplat ty operand) s = .ok (id, final)) : WellMintedState final := by
  obtain ⟨value, middle, looked, tail⟩ := split_bind_success _ _ s final id run
  obtain ⟨lookup, same⟩ := lookup_success s middle operand value looked
  subst middle
  obtain ⟨unit, middle, guarded, tail⟩ := split_bind_success _ _ s final id tail
  cases unit
  have same := reject_success_state value "ArraySplat" s middle guarded
  subst middle
  split at tail
  · exact valid.fresh_success s final _ id (array_uniform_minted _ _ value (valid.values operand value lookup)) tail
  · exact False.elim (throw_success s final id _ tail)

theorem WellMintedState.extract_field_success (s final : MachineState) (ty : Ty)
    (operand id : ValueId) (field : Nat) (valid : WellMintedState s)
    (run : Sem.run (semExtractField ty operand field) s = .ok (id, final)) : WellMintedState final := by
  obtain ⟨value, middle, looked, tail⟩ := split_bind_success _ _ s final id run
  obtain ⟨lookup, same⟩ := lookup_success s middle operand value looked
  subst middle
  obtain ⟨unit, middle, guarded, tail⟩ := split_bind_success _ _ s final id tail
  cases unit
  have same := reject_success_state value "ExtractField" s middle guarded
  subst middle
  cases found : getField value field with
  | none =>
    simp only [found, Sem.throwTypeError, Sem.throwUB] at tail
    repeat' first
      | with_reducible exact False.elim (throw_success s final id _ tail)
      | split at tail
  | some child =>
    simp only [found] at tail
    split at tail
    · exact False.elim (throw_success s final id _ tail)
    · exact valid.fresh_success s final child id
        (field_get_minted _ value child field (valid.values operand value lookup) found) tail

theorem WellMintedState.insert_field_success (s final : MachineState) (ty : Ty)
    (operand rhs id : ValueId) (field : Nat) (valid : WellMintedState s)
    (run : Sem.run (semInsertField ty operand field rhs) s = .ok (id, final)) : WellMintedState final := by
  obtain ⟨value, middle, looked, tail⟩ := split_bind_success _ _ s final id run
  obtain ⟨lookup, same⟩ := lookup_success s middle operand value looked
  subst middle
  obtain ⟨inserted, middle, looked, tail⟩ := split_bind_success _ _ s final id tail
  obtain ⟨lookupRhs, same⟩ := lookup_success s middle rhs inserted looked
  subst middle
  obtain ⟨unit, middle, guarded, tail⟩ := split_bind_success _ _ s final id tail
  cases unit
  have same := reject_success_state value "InsertField" s middle guarded
  subst middle
  obtain ⟨unit, middle, guarded, tail⟩ := split_bind_success _ _ s final id tail
  cases unit
  have same := reject_success_state inserted "InsertField" s middle guarded
  subst middle
  have original := valid.values operand value lookup
  have incoming := valid.values rhs inserted lookupRhs
  simp only [Sem.throwTypeError, Sem.throwUB, Sem.throwUnsupported, buildAggregate] at tail
  repeat' first
    | with_reducible exact valid.fresh_success s final _ id (field_set_minted _ value inserted _ field original incoming (by assumption)) tail
    | with_reducible exact False.elim (throw_success s final id _ tail)
    | split at tail

/-- Contextual integer/index validation is a read-only computation. -/
theorem element_index_success_state (ctx : EvalContext) (operand : ValueId) (value : Value)
    (s final : MachineState) (index : Nat)
    (run : Sem.run (ctx.elementIndex operand value) s = .ok (index, final)) : final = s := by
  unfold EvalContext.elementIndex at run
  dsimp only at run
  split at run
  · change Except.ok (_, s) = Except.ok (index, final) at run
    cases run
    rfl
  · exact False.elim (throw_success s final index _ run)

theorem WellMintedState.extract_element_success (indexOf : Value → Sem Nat)
    (readonly : ∀ value s final index, Sem.run (indexOf value) s = .ok (index, final) → final = s)
    (s final : MachineState) (ty : Ty) (operand indexId id : ValueId) (valid : WellMintedState s)
    (run : Sem.run (semExtractElementUsing indexOf ty operand indexId) s = .ok (id, final)) :
    WellMintedState final := by
  obtain ⟨value, middle, looked, tail⟩ := split_bind_success _ _ s final id run
  obtain ⟨lookup, same⟩ := lookup_success s middle operand value looked
  subst middle
  obtain ⟨indexValue, middle, looked, tail⟩ := split_bind_success _ _ s final id tail
  obtain ⟨_, same⟩ := lookup_success s middle indexId indexValue looked
  subst middle
  obtain ⟨index, middle, computed, tail⟩ := split_bind_success _ _ s final id tail
  have same := readonly indexValue s middle index computed
  subst middle
  have original := valid.values operand value lookup
  simp only [Sem.throwUB, Sem.throwTypeError] at tail
  repeat' first
    | with_reducible exact valid.fresh_success s final _ id (element_get_minted _ value _ index original (by assumption)) tail
    | (with_reducible refine valid.fresh_success s final _ id ?_ tail)
      exact vector_element_get_minted _ ty _ _ index original (by assumption)
    | with_reducible exact False.elim (throw_success s final id _ tail)
    | split at tail

theorem WellMintedState.insert_element_success (indexOf : Value → Sem Nat)
    (readonly : ∀ value s final index, Sem.run (indexOf value) s = .ok (index, final) → final = s)
    (s final : MachineState) (ty : Ty) (operand indexId rhs id : ValueId) (valid : WellMintedState s)
    (run : Sem.run (semInsertElementUsing indexOf ty operand indexId rhs) s = .ok (id, final)) :
    WellMintedState final := by
  obtain ⟨value, middle, looked, tail⟩ := split_bind_success _ _ s final id run
  obtain ⟨lookup, same⟩ := lookup_success s middle operand value looked
  subst middle
  obtain ⟨indexValue, middle, looked, tail⟩ := split_bind_success _ _ s final id tail
  obtain ⟨_, same⟩ := lookup_success s middle indexId indexValue looked
  subst middle
  obtain ⟨inserted, middle, looked, tail⟩ := split_bind_success _ _ s final id tail
  obtain ⟨lookupRhs, same⟩ := lookup_success s middle rhs inserted looked
  subst middle
  obtain ⟨index, middle, computed, tail⟩ := split_bind_success _ _ s final id tail
  have same := readonly indexValue s middle index computed
  subst middle
  have original := valid.values operand value lookup
  have incoming := valid.values rhs inserted lookupRhs
  split at tail
  · repeat' first
      | (with_reducible refine valid.fresh_success s final _ id ?_ tail)
        exact vector_element_set_minted _ ty _ inserted _ index original incoming (by assumption)
      | with_reducible exact False.elim (throw_success s final id _ tail)
      | split at tail
  · obtain ⟨unit, middle, guarded, tail⟩ := split_bind_success _ _ s final id tail
    cases unit
    have same := reject_success_state inserted "InsertElement" s middle guarded
    subst middle
    simp only [Sem.throwUB, Sem.throwTypeError] at tail
    repeat' first
      | with_reducible exact valid.fresh_success s final _ id (element_set_minted _ value inserted _ index original incoming (by assumption)) tail
      | with_reducible exact False.elim (throw_success s final id _ tail)
      | split at tail

end TrustIr.FrameLifetime
