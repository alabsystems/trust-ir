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

private theorem append_member {α : Type} (left right : List α) (value : α)
    (member : value ∈ left ++ right) : value ∈ left ∨ value ∈ right := by
  induction left with
  | nil => exact .inr member
  | cons first rest ih =>
    cases member with
    | head => exact .inl (.head rest)
    | tail _ member =>
      cases ih member with
      | inl member => exact .inl (.tail first member)
      | inr member => exact .inr member

/-- Value-level union selects only original elements. This is a helper law,
not a claim that a SetUnion instruction exists in the current Step grammar. -/
theorem set_union_minted (bound : Nat) (left right output : Value)
    (leftValid : MintedValue bound left) (rightValid : MintedValue bound right)
    (run : setUnion left right = some output) : MintedValue bound output := by
  unfold setUnion at run
  split at run
  · cases run
    apply (mintedValue_iff_shape bound _).2
    intro value member
    cases append_member _ _ _ member with
    | inl member => exact (mintedValue_iff_shape bound _).1 leftValid value member
    | inr member => exact (mintedValue_iff_shape bound _).1 rightValid value (List.mem_filter.mp member).1
  · contradiction

theorem set_intersection_minted (bound : Nat) (left right output : Value)
    (leftValid : MintedValue bound left)
    (run : setIntersection left right = some output) : MintedValue bound output := by
  unfold setIntersection at run
  split at run
  · cases run
    exact (mintedValue_iff_shape bound _).2 (fun value member =>
      (mintedValue_iff_shape bound _).1 leftValid value (List.mem_filter.mp member).1)
  · contradiction

theorem sequence_concat_minted (bound : Nat) (left right output : Value)
    (leftValid : MintedValue bound left) (rightValid : MintedValue bound right)
    (run : seqConcat left right = some output) : MintedValue bound output := by
  unfold seqConcat at run
  split at run
  · cases run
    apply (mintedValue_iff_shape bound _).2
    intro value member
    cases append_member _ _ _ member with
    | inl member => exact (mintedValue_iff_shape bound _).1 leftValid value member
    | inr member => exact (mintedValue_iff_shape bound _).1 rightValid value member
  · contradiction

theorem sequence_add_lanes_minted (bound : Nat) (k : Nat) (input output : List Value)
    (run : seqMapAddKList k input = .ok output) : MintedArgs bound output := by
  induction input generalizing output with
  | nil =>
    cases run
    exact fun _ member => nomatch member
  | cons first rest ih =>
    cases first <;> simp only [seqMapAddKList] at run <;> try contradiction
    case int =>
      cases computed : seqMapAddKList k rest with
      | error error => simp [computed] at run
      | ok values =>
        simp only [computed] at run
        cases run
        intro value member
        cases member with
        | head => exact mintedValue_int bound _ _
        | tail _ member => exact ih values computed value member

theorem sequence_not_lanes_minted (bound : Nat) (input output : List Value)
    (run : seqMapNotList input = .ok output) : MintedArgs bound output := by
  induction input generalizing output with
  | nil =>
    cases run
    exact fun _ member => nomatch member
  | cons first rest ih =>
    cases first <;> simp only [seqMapNotList] at run <;> try contradiction
    case bool =>
      cases computed : seqMapNotList rest with
      | error error => simp [computed] at run
      | ok values =>
        simp only [computed] at run
        cases run
        intro value member
        cases member with
        | head => exact mintedValue_bool bound _
        | tail _ member => exact ih values computed value member

private theorem throw_success {α : Type} (s final : MachineState) (value : α) (error : SemError)
    (run : Sem.run (throw error : Sem α) s = .ok (value, final)) : False := by
  cases run

/-- Fixed integer sequence mapping preserves state identity validity and only
publishes a sequence of frame-free scalar results. -/
theorem WellMintedState.sequence_add_success (s final : MachineState) (ty : Ty)
    (operand id : ValueId) (k : Nat) (valid : WellMintedState s)
    (run : Sem.run (semSeqMapAddK ty operand k) s = .ok (id, final)) : WellMintedState final := by
  obtain ⟨value, middle, looked, tail⟩ := split_bind_success _ _ s final id run
  obtain ⟨_, same⟩ := lookup_success s middle operand value looked
  subst middle
  simp only [Sem.throwTypeError] at tail
  repeat' first
    | (with_reducible refine valid.fresh_success s final _ id ?_ tail)
      apply (mintedValue_iff_shape _ _).2
      exact sequence_add_lanes_minted _ k _ _ (by assumption)
    | with_reducible exact False.elim (throw_success s final id _ tail)
    | split at tail

theorem WellMintedState.sequence_not_success (s final : MachineState) (ty : Ty)
    (operand id : ValueId) (valid : WellMintedState s)
    (run : Sem.run (semSeqMapNot ty operand) s = .ok (id, final)) : WellMintedState final := by
  obtain ⟨value, middle, looked, tail⟩ := split_bind_success _ _ s final id run
  obtain ⟨_, same⟩ := lookup_success s middle operand value looked
  subst middle
  simp only [Sem.throwTypeError] at tail
  repeat' first
    | (with_reducible refine valid.fresh_success s final _ id ?_ tail)
      apply (mintedValue_iff_shape _ _).2
      exact sequence_not_lanes_minted _ _ _ (by assumption)
    | with_reducible exact False.elim (throw_success s final id _ tail)
    | split at tail

/-- Callback SeqMap preparation transports original sequence elements and leaves
state exactly unchanged. This does not execute or qualify the element callback. -/
theorem sequence_map_request_success (ctx : EvalContext) (ty : Ty) (operand : ValueId) (fn : FuncId)
    (s final : MachineState) (result : InstrResult) (valid : WellMintedState s)
    (run : Sem.run (stepInstWithContext ctx (.SeqMap ty operand fn)) s = .ok (result, final)) :
    ∃ elements, result = .terminator (.SeqMapReq fn elements) ∧ final = s ∧
      MintedArgs s.nextFrameLineage elements := by
  obtain ⟨value, middle, looked, tail⟩ := split_bind_success (Sem.lookupValue operand) _ s final result run
  obtain ⟨lookup, same⟩ := lookup_success s middle operand value looked
  subst middle
  cases value <;> simp only at tail
  case sequence elements =>
    change Except.ok (.terminator (.SeqMapReq fn elements), s) = Except.ok (result, final) at tail
    cases tail
    exact ⟨elements, rfl, rfl, (mintedValue_iff_shape _ _).1 (valid.values operand (.sequence elements) lookup)⟩
  all_goals exact False.elim (throw_success s final result _ tail)

end TrustIr.FrameLifetime
