-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameUnaryValidity
import TrustIr.Semantics.Cast

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

/-- Numeric pointers carry no frame identities, regardless of provenance. -/
theorem mintedValue_pointer (bound address : Nat) (provenance : Option AllocId) :
    MintedValue bound (.ptr address provenance) := by
  intro lineage occurs
  cases occurs

private theorem free_fresh_success (s final : MachineState) (value : Value) (id : ValueId)
    (valid : WellMintedState s) (free : MintedValue 0 value)
    (run : Sem.run (Sem.bindFresh value) s = .ok (id, final)) : WellMintedState final :=
  valid.fresh_success s final value id (free.mono (Nat.zero_le _)) run

private theorem throw_success {α : Type} (s final : MachineState) (value : α) (error : SemError)
    (run : Sem.run (throw error : Sem α) s = .ok (value, final)) : False := by
  cases run

private theorem address_success_state (op : String) (width : Nat) (raw : Int)
    (model : ByteModel) (s final : MachineState) (address : Nat)
    (run : Sem.run (Sem.addrOfInt op width raw model) s = .ok (address, final)) : final = s := by
  by_cases carrier : (raw % (2 ^ width)).toNat < 2 ^ Sem.addrBits
  all_goals
    by_cases target : (raw % (2 ^ width)).toNat < model.addressLimit
    all_goals
      cases model <;>
        simp [Sem.addrOfInt, carrier, target, Sem.run, Sem.throwUB,
          StateT.run, StateT.pure, StateT.lift, pure, Except.pure,
          throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at run
      all_goals exact run.2.symm

private theorem resolve_fresh_success (op : String) (width : Nat) (raw : Int)
    (model : ByteModel) (s final : MachineState) (id : ValueId) (valid : WellMintedState s)
    (run : Sem.run (do
      let address ← Sem.addrOfInt op width raw model
      let state ← Sem.getState
      Sem.bindFresh (state.memory.resolveAddr address)) s = .ok (id, final)) : WellMintedState final := by
  obtain ⟨address, middle, computed, tail⟩ := split_bind_success _ _ s final id run
  have same := address_success_state op width raw model s middle address computed
  subst middle
  change Sem.run (Sem.bindFresh (s.memory.resolveAddr address)) s = .ok (id, final) at tail
  apply free_fresh_success s final _ id valid ?_ tail
  unfold Memory.resolveAddr
  split
  · exact mintedValue_null 0
  · exact mintedValue_pointer 0 _ _

private theorem pointer_integer_success (op : String) (ty : Ty) (address : Nat)
    (model : ByteModel) (s final : MachineState) (id : ValueId) (valid : WellMintedState s)
    (run : Sem.run (Sem.bindPointerInteger op ty address model) s = .ok (id, final)) :
    WellMintedState final := by
  unfold Sem.bindPointerInteger at run
  cases widthEq : getTyWidth ty model with
  | error error =>
    simp [widthEq, Sem.run, StateT.run, StateT.bind, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at run
  | ok width =>
    simp only [widthEq] at run
    change Sem.run (if address < model.addressLimit then Sem.bindFresh (Value.intAt width (Int.ofNat address))
      else Sem.throwUB _) s = .ok (id, final) at run
    split at run
    · exact free_fresh_success s final _ id valid (mintedValue_int 0 _ _) run
    · exact False.elim (throw_success s final id _ run)

private theorem pointer_provenance_success (op : String) (ty : Ty) (address : Nat)
    (provenance : Option AllocId) (model : ByteModel) (s final : MachineState) (id : ValueId)
    (valid : WellMintedState s)
    (run : Sem.run (Sem.bindPointerIntegerWithProvenance op ty address provenance model) s = .ok (id, final)) :
    WellMintedState final := by
  cases provenance with
  | some alloc => exact pointer_integer_success op ty address model s final id valid run
  | none =>
    unfold Sem.bindPointerIntegerWithProvenance at run
    cases widthEq : getTyWidth ty model with
    | error error =>
      simp [widthEq, Sem.run, StateT.run, StateT.bind, StateT.lift,
        throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at run
    | ok width =>
      simp only [widthEq] at run
      change Sem.run (if address < word64Limit then Sem.bindFresh (Value.intAt width (Int.ofNat address))
        else Sem.throwUB _) s = .ok (id, final) at run
      split at run
      · exact free_fresh_success s final _ id valid (mintedValue_int 0 _ _) run
      · exact False.elim (throw_success s final id _ run)

private theorem reject_success_state (value : Value) (s final : MachineState)
    (run : Sem.run (Sem.rejectPartial value "Cast") s = .ok ((), final)) : final = s := by
  cases value <;>
    simp [Sem.rejectPartial, Sem.run, Sem.throwUB, StateT.run, StateT.pure,
      StateT.lift, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      bind, Except.bind] at run <;> exact run.symm

/-- All seventeen actual cast paths preserve recursive frame identities.
The legacy closure reification transports its original nested captures; numeric
and pointer paths produce frame-free values with all original guards retained. -/
theorem WellMintedState.cast_success (s final : MachineState) (op : CastOp)
    (srcTy dstTy : Ty) (operandId id : ValueId) (model : ByteModel) (valid : WellMintedState s)
    (run : Sem.run (semCast op srcTy dstTy operandId model) s = .ok (id, final)) :
    WellMintedState final := by
  obtain ⟨operand, middle, looked, tail⟩ := split_bind_success (Sem.lookupValue operandId) _ s final id run
  obtain ⟨lookup, same⟩ := lookup_success s middle operandId operand looked
  subst middle
  have operandValid := valid.values operandId operand lookup
  obtain ⟨unit, middle, guarded, tail⟩ := split_bind_success (Sem.rejectPartial operand "Cast") _ s final id tail
  cases unit
  have same := reject_success_state operand s middle guarded
  subst middle
  cases op <;> dsimp only at tail
  all_goals simp only [Sem.throwTypeError, Sem.throwUB, Sem.throwUnsupported] at tail
  all_goals
    repeat' first
      | with_reducible exact free_fresh_success s final _ id valid (mintedValue_int 0 _ _) tail
      | with_reducible exact free_fresh_success s final _ id valid (mintedValue_float 0 _) tail
      | with_reducible exact free_fresh_success s final _ id valid (mintedValue_bool 0 _) tail
      | with_reducible exact free_fresh_success s final _ id valid (mintedValue_pointer 0 _ _) tail
      | with_reducible exact free_fresh_success s final _ id valid (mintedValue_null 0) tail
      | with_reducible exact valid.fresh_success s final _ id operandValid tail
      | with_reducible exact resolve_fresh_success _ _ _ model s final id valid tail
      | with_reducible exact pointer_integer_success _ _ _ model s final id valid tail
      | with_reducible exact pointer_provenance_success _ _ _ _ model s final id valid tail
      | with_reducible exact False.elim (throw_success s final id _ tail)
      | split at tail

end TrustIr.FrameLifetime
