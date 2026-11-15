-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameUnaryValidity
import TrustIr.Semantics.Compare

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

private theorem except_success {α β : Type} (action : Except SemError α)
    (next : α → Except SemError β) (result : β)
    (run : (action >>= next) = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases step : action with
  | error error => simp [step, bind, Except.bind] at run
  | ok value => exact ⟨value, rfl, by simpa [step] using run⟩

/-- Scalar arithmetic results contain no frame identity at any depth. -/
private theorem except_map_minted {α : Type} (bound : Nat) (action : Except SemError α)
    (encode : α → Value) (result : Value) (known : ∀ value, MintedValue bound (encode value))
    (run : (do let value ← action; pure (encode value)) = .ok result) : MintedValue bound result := by
  cases computed : action with
  | error error => simp [computed, bind, Except.bind] at run
  | ok value =>
    simp [computed, bind, pure, Except.bind, Except.pure] at run
    cases run
    exact known value

private theorem bool_pair_minted {α β : Type} (bound : Nat)
    (left : Except SemError α) (right : Except SemError β) (encode : α → β → Bool)
    (result : Value)
    (run : (do let a ← left; let b ← right; pure (Value.bool (encode a b))) = .ok result) :
    MintedValue bound result := by
  obtain ⟨a, _, tail⟩ := except_success left _ result run
  exact except_map_minted bound right (fun b => .bool (encode a b)) result
    (fun b => mintedValue_bool bound _) tail

theorem integer_compare_lanes_minted (bound : Nat) (op : ICmpOp) (width : Nat) (left right output : List Value)
    (run : semVectorICmp op width left right = .ok output) :
    ∀ value ∈ output, MintedValue bound value := by
  induction left generalizing right output with
  | nil =>
    cases right <;> simp [semVectorICmp] at run
    cases run
    intro value member
    cases member
  | cons first left ih =>
    cases right with
    | nil => simp [semVectorICmp] at run
    | cons second right =>
      obtain ⟨a, _, tail1⟩ := except_success (icmpIntValue width first) _ output run
      obtain ⟨b, _, tail2⟩ := except_success (icmpIntValue width second) _ output tail1
      obtain ⟨rest, computed, tail3⟩ := except_success (semVectorICmp op width left right) _ output tail2
      change Except.ok (Value.bool _ :: rest) = Except.ok output at tail3
      cases tail3
      intro value member
      cases member with
      | head => exact mintedValue_bool bound _
      | tail _ member => exact ih right rest computed value member

theorem bool_compare_lanes_minted (bound : Nat) (op : ICmpOp) (left right output : List Value)
    (run : semVectorBoolICmp op left right = .ok output) :
    ∀ value ∈ output, MintedValue bound value := by
  induction left generalizing right output with
  | nil =>
    cases right <;> simp [semVectorBoolICmp] at run
    cases run
    intro value member
    cases member
  | cons first left ih =>
    cases right with
    | nil => simp [semVectorBoolICmp] at run
    | cons second right =>
      obtain ⟨a, _, tail1⟩ := except_success (icmpBoolValue first) _ output run
      obtain ⟨b, _, tail2⟩ := except_success (icmpBoolValue second) _ output tail1
      obtain ⟨rest, computed, tail3⟩ := except_success (semVectorBoolICmp op left right) _ output tail2
      change Except.ok (Value.bool _ :: rest) = Except.ok output at tail3
      cases tail3
      intro value member
      cases member with
      | head => exact mintedValue_bool bound _
      | tail _ member => exact ih right rest computed value member

/-- All successful integer comparisons return a frame-free Bool or Bool vector,
including pointer comparisons under the caller's byte model. -/
theorem integer_compare_value_minted (bound : Nat) (op : ICmpOp) (ty : Ty)
    (left right result : Value) (model : ByteModel)
    (run : semICmpValues op ty left right model = .ok result) : MintedValue bound result := by
  unfold semICmpValues at run
  split at run
  · exact bool_pair_minted bound _ _ _ result run
  · exact bool_pair_minted bound _ _ _ result run
  · split at run
    · cases run
    · split at run
      · split at run
        · cases run
        · split at run
          · obtain ⟨output, computed, tail⟩ := except_success (semVectorBoolICmp op _ _) _ result run
            change Except.ok (.vector output) = Except.ok result at tail
            cases tail
            exact (mintedValue_iff_shape bound (.vector output)).2
              (bool_compare_lanes_minted bound op _ _ output computed)
          · split at run
            · obtain ⟨output, computed, tail⟩ := except_success (semVectorICmp op _ _ _) _ result run
              change Except.ok (.vector output) = Except.ok result at tail
              cases tail
              exact (mintedValue_iff_shape bound (.vector output)).2
                (integer_compare_lanes_minted bound op _ _ _ output computed)
            · cases run
      · cases run
  · split at run
    · split at run
      · exact bool_pair_minted bound _ _ _ result run
      · cases run
    · cases run

theorem float_compare_lanes_minted (bound : Nat) (op : FCmpOp) (ty : Ty)
    (left right output : List Value) (run : semVectorFCmp op ty left right = .ok output) :
    ∀ value ∈ output, MintedValue bound value := by
  induction left generalizing right output with
  | nil =>
    cases right <;> simp [semVectorFCmp] at run
    cases run
    intro value member
    cases member
  | cons first left ih =>
    cases right with
    | nil => simp [semVectorFCmp] at run
    | cons second right =>
      obtain ⟨unit, _, tail1⟩ := except_success (checkVectorLaneType ty false first) _ output run
      cases unit
      obtain ⟨unit, _, tail2⟩ := except_success (checkVectorLaneType ty false second) _ output tail1
      cases unit
      split at tail2
      · obtain ⟨head, headRun, tail3⟩ := except_success _ _ output tail2
        change Except.ok (Value.bool _) = Except.ok head at headRun
        cases headRun
        obtain ⟨rest, computed, tail4⟩ := except_success (semVectorFCmp op ty left right) _ output tail3
        change Except.ok (Value.bool _ :: rest) = Except.ok output at tail4
        cases tail4
        intro value member
        cases member with
        | head => exact mintedValue_bool bound _
        | tail _ member => exact ih right rest computed value member
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at tail2

/-- Every successful floating comparison returns only Bool leaves; original
width and lane checks are consumed from the actual computation. -/
theorem float_compare_value_minted (bound : Nat) (op : FCmpOp) (ty : Ty)
    (left right result : Value)
    (run : semFCmpValues op ty left right = .ok result) : MintedValue bound result := by
  unfold semFCmpValues at run
  split at run
  · obtain ⟨unit, _, tail1⟩ := except_success (checkVectorShape _ _ _) _ result run
    cases unit
    obtain ⟨unit, _, tail2⟩ := except_success (checkVectorShape _ _ _) _ result tail1
    cases unit
    split at tail2
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at tail2
    · obtain ⟨output, computed, tail4⟩ := except_success (semVectorFCmp op _ _ _) _ result tail2
      change Except.ok (.vector output) = Except.ok result at tail4
      cases tail4
      exact (mintedValue_iff_shape bound (.vector output)).2
        (float_compare_lanes_minted bound op _ _ _ output computed)
  · exact bool_pair_minted bound (checkFloatAt _ _) (checkFloatAt _ _) (fun _ _ => _) result run
  · simp [throw, throwThe, MonadExceptOf.throw] at run

private theorem reject_success_state (value : Value) (label : String) (s final : MachineState)
    (run : Sem.run (Sem.rejectPartial value label) s = .ok ((), final)) : final = s := by
  cases value <;>
    simp [Sem.rejectPartial, Sem.run, Sem.throwUB, StateT.run, StateT.pure,
      StateT.lift, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      bind, Except.bind] at run <;> exact run.symm

private theorem checked_compare_success (compute : Value → Value → Except SemError Value)
    (label : String) (left right : ValueId) (s final : MachineState) (id : ValueId)
    (valid : WellMintedState s)
    (free : ∀ lhs rhs result, compute lhs rhs = .ok result → MintedValue s.nextFrameLineage result)
    (run : Sem.run (do
      let lhs ← Sem.lookupValue left
      let rhs ← Sem.lookupValue right
      Sem.rejectPartial lhs label
      Sem.rejectPartial rhs label
      match compute lhs rhs with
      | .ok result => Sem.bindFresh result
      | .error error => throw error) s = .ok (id, final)) : WellMintedState final := by
  obtain ⟨lhs, middle, looked, tail1⟩ := split_bind_success (Sem.lookupValue left) _ s final id run
  obtain ⟨_, same⟩ := lookup_success s middle left lhs looked
  subst middle
  obtain ⟨rhs, middle, looked, tail2⟩ := split_bind_success (Sem.lookupValue right) _ s final id tail1
  obtain ⟨_, same⟩ := lookup_success s middle right rhs looked
  subst middle
  obtain ⟨unit, middle, guarded, tail3⟩ := split_bind_success (Sem.rejectPartial lhs label) _ s final id tail2
  cases unit
  have same := reject_success_state lhs label s middle guarded
  subst middle
  obtain ⟨unit, middle, guarded, tail4⟩ := split_bind_success (Sem.rejectPartial rhs label) _ s final id tail3
  cases unit
  have same := reject_success_state rhs label s middle guarded
  subst middle
  cases computed : compute lhs rhs with
  | error error =>
    simp [computed, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at tail4
  | ok result =>
    exact valid.fresh_success s final result id (free lhs rhs result computed)
      (by simpa [computed] using tail4)

theorem WellMintedState.integer_compare_success (s final : MachineState) (op : ICmpOp)
    (ty : Ty) (left right id : ValueId) (model : ByteModel) (valid : WellMintedState s)
    (run : Sem.run (semICmpInst op ty left right model) s = .ok (id, final)) : WellMintedState final :=
  checked_compare_success (fun lhs rhs => semICmpValues op ty lhs rhs model) "ICmp" left right s final id valid
    (fun lhs rhs result computed => integer_compare_value_minted _ op ty lhs rhs result model computed) run

theorem WellMintedState.float_compare_success (s final : MachineState) (op : FCmpOp)
    (ty : Ty) (left right id : ValueId) (valid : WellMintedState s)
    (run : Sem.run (semFCmpInst op ty left right) s = .ok (id, final)) : WellMintedState final :=
  checked_compare_success (semFCmpValues op ty) "FCmp" left right s final id valid
    (fun lhs rhs result computed => float_compare_value_minted _ op ty lhs rhs result computed) run

end TrustIr.FrameLifetime
