-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameAliasValidity

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
theorem mintedValue_int (bound width : Nat) (value : Int) : MintedValue bound (.int width value) := by
  intro lineage occurrence
  cases occurrence

theorem mintedValue_float (bound : Nat) (value : Float) : MintedValue bound (.float value) := by
  intro lineage occurrence
  cases occurrence

theorem mintedValue_bool (bound : Nat) (value : Bool) : MintedValue bound (.bool value) := by
  intro lineage occurrence
  cases occurrence

theorem mintedValue_null (bound : Nat) : MintedValue bound .nullPtr := by
  intro lineage occurrence
  cases occurrence

private theorem except_map_minted {α : Type} (bound : Nat) (action : Except SemError α)
    (encode : α → Value) (result : Value) (known : ∀ value, MintedValue bound (encode value))
    (run : (do let value ← action; pure (encode value)) = .ok result) : MintedValue bound result := by
  cases computed : action with
  | error error => simp [computed, bind, Except.bind] at run
  | ok value =>
    simp [computed, bind, pure, Except.bind, Except.pure] at run
    cases run
    exact known value

/-- Original checked vector unary lanes produce only frame-free scalar leaves. -/
theorem unary_lane_minted (bound : Nat) (op : UnOp) (ty : Ty) (operand result : Value)
    (run : semVectorUnOpLane op ty operand = .ok result) : MintedValue bound result := by
  obtain ⟨unit, _, tail⟩ := except_success (checkVectorLaneType ty false operand) _ result run
  cases unit
  cases operand with
  | bool bit =>
    cases op <;> simp [pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
    cases tail
    exact mintedValue_bool bound _
  | int width raw =>
    exact except_map_minted bound (semIntUnOp op width raw) (.int width) result
      (mintedValue_int bound width) tail
  | float value =>
    exact except_map_minted bound (semFloatUnOpAt op ty value) .float result
      (mintedValue_float bound) tail
  | ptr _ _ => simp [throw, throwThe, MonadExceptOf.throw] at tail
  | array _ => simp [throw, throwThe, MonadExceptOf.throw] at tail
  | aggregate _ => simp [throw, throwThe, MonadExceptOf.throw] at tail
  | vector _ => simp [throw, throwThe, MonadExceptOf.throw] at tail
  | frame _ _ => simp [throw, throwThe, MonadExceptOf.throw] at tail
  | set _ => simp [throw, throwThe, MonadExceptOf.throw] at tail
  | sequence _ => simp [throw, throwThe, MonadExceptOf.throw] at tail
  | record _ => simp [throw, throwThe, MonadExceptOf.throw] at tail
  | closure _ _ => simp [throw, throwThe, MonadExceptOf.throw] at tail
  | fnDef _ _ => simp [throw, throwThe, MonadExceptOf.throw] at tail
  | typedClosure _ _ _ => simp [throw, throwThe, MonadExceptOf.throw] at tail
  | fatPtr _ _ _ => simp [throw, throwThe, MonadExceptOf.throw] at tail
  | «partial» _ => simp [throw, throwThe, MonadExceptOf.throw] at tail
  | undef _ => simp [throw, throwThe, MonadExceptOf.throw] at tail
  | nullPtr  => simp [throw, throwThe, MonadExceptOf.throw] at tail
  | uninit  => simp [throw, throwThe, MonadExceptOf.throw] at tail

theorem unary_lanes_minted (bound : Nat) (op : UnOp) (ty : Ty) (operands output : List Value)
    (run : semVectorUnOp op ty operands = .ok output) :
    ∀ value ∈ output, MintedValue bound value := by
  induction operands generalizing output with
  | nil =>
    simp [semVectorUnOp] at run
    cases run
    intro value member
    cases member
  | cons head rest ih =>
    obtain ⟨first, computed, tail1⟩ := except_success (semVectorUnOpLane op ty head) _ output run
    obtain ⟨remaining, computedRest, tail2⟩ := except_success (semVectorUnOp op ty rest) _ output tail1
    change Except.ok (first :: remaining) = Except.ok output at tail2
    cases tail2
    intro value member
    cases member with
    | head => exact unary_lane_minted bound op ty head first computed
    | tail _ member => exact ih remaining computedRest value member

/-- Every successful original scalar/vector unary computation is recursively
frame-free. This is an identity law, not a numeric correctness claim. -/
theorem unary_value_minted (bound : Nat) (op : UnOp) (ty : Ty) (operand result : Value)
    (run : semUnOpValue op ty operand = .ok result) : MintedValue bound result := by
  cases operand with
  | int width raw =>
    apply except_map_minted bound (semIntUnOp op width raw) (.int width) result (mintedValue_int bound width)
    cases ty <;> exact run
  | float value =>
    apply except_map_minted bound (semFloatUnOpAt op ty value) .float result (mintedValue_float bound)
    cases ty <;> exact run
  | vector lanes =>
    cases ty <;> try { simp [semUnOpValue, throw, throwThe, MonadExceptOf.throw] at run }
    case Vector count elemTy =>
      obtain ⟨unit, _, tail1⟩ := except_success (checkVectorShape count elemTy lanes) _ result run
      cases unit
      obtain ⟨output, computed, tail2⟩ := except_success (semVectorUnOp op elemTy lanes) _ result tail1
      change Except.ok (.vector output) = Except.ok result at tail2
      cases tail2
      exact (mintedValue_iff_shape bound (.vector output)).2 (unary_lanes_minted bound op elemTy lanes output computed)
  | bool _ => simp [semUnOpValue, throw, throwThe, MonadExceptOf.throw] at run
  | ptr _ _ => simp [semUnOpValue, throw, throwThe, MonadExceptOf.throw] at run
  | array _ => simp [semUnOpValue, throw, throwThe, MonadExceptOf.throw] at run
  | aggregate _ => simp [semUnOpValue, throw, throwThe, MonadExceptOf.throw] at run
  | frame _ _ => simp [semUnOpValue, throw, throwThe, MonadExceptOf.throw] at run
  | set _ => simp [semUnOpValue, throw, throwThe, MonadExceptOf.throw] at run
  | sequence _ => simp [semUnOpValue, throw, throwThe, MonadExceptOf.throw] at run
  | record _ => simp [semUnOpValue, throw, throwThe, MonadExceptOf.throw] at run
  | closure _ _ => simp [semUnOpValue, throw, throwThe, MonadExceptOf.throw] at run
  | fnDef _ _ => simp [semUnOpValue, throw, throwThe, MonadExceptOf.throw] at run
  | typedClosure _ _ _ => simp [semUnOpValue, throw, throwThe, MonadExceptOf.throw] at run
  | fatPtr _ _ _ => simp [semUnOpValue, throw, throwThe, MonadExceptOf.throw] at run
  | «partial» _ => simp [semUnOpValue, throw, throwThe, MonadExceptOf.throw] at run
  | undef _ => simp [semUnOpValue, throw, throwThe, MonadExceptOf.throw] at run
  | nullPtr  => simp [semUnOpValue, throw, throwThe, MonadExceptOf.throw] at run
  | uninit  => simp [semUnOpValue, throw, throwThe, MonadExceptOf.throw] at run

private theorem reject_success_state (value : Value) (s final : MachineState)
    (run : Sem.run (Sem.rejectPartial value "UnOp") s = .ok ((), final)) : final = s := by
  cases value <;>
    simp [Sem.rejectPartial, Sem.run, Sem.throwUB, StateT.run, StateT.pure,
      StateT.lift, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      bind, Except.bind] at run <;> exact run.symm

/-- Actual unary execution preserves all existing identities and publishes
only a frame-free result, with no successful numeric check assumed separately. -/
theorem WellMintedState.unary_success (s final : MachineState) (op : UnOp) (ty : Ty)
    (operand id : ValueId) (valid : WellMintedState s)
    (run : Sem.run (semUnOp op ty operand) s = .ok (id, final)) : WellMintedState final := by
  obtain ⟨value, middle, looked, tail1⟩ := split_bind_success (Sem.lookupValue operand) _ s final id run
  obtain ⟨_, same⟩ := lookup_success s middle operand value looked
  subst middle
  obtain ⟨unit, middle, guarded, tail2⟩ := split_bind_success (Sem.rejectPartial value "UnOp") _ s final id tail1
  cases unit
  have same := reject_success_state value s middle guarded
  subst middle
  cases computed : semUnOpValue op ty value with
  | error error =>
    simp [computed, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at tail2
  | ok result =>
    exact WellMintedState.fresh_success s final result id valid
      (unary_value_minted s.nextFrameLineage op ty value result computed)
      (by simpa [computed] using tail2)

end TrustIr.FrameLifetime
