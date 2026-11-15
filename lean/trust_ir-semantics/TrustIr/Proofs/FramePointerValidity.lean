-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameCastValidity
import TrustIr.Semantics.Memory

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

/-- A fat-pointer data projection cannot expose a frame identity. -/
theorem pointer_data_minted (bound : Nat) (pointer result : Value)
    (run : fatPtrDataValue pointer = some result) : MintedValue bound result := by
  cases pointer <;> simp only [fatPtrDataValue] at run <;> try contradiction
  case fatPtr address provenance metadata =>
    cases run
    cases address with
    | zero => exact mintedValue_null bound
    | succ address => exact mintedValue_pointer bound _ _

/-- Metadata projection transports the original recursively valid payload. -/
theorem pointer_metadata_minted (bound : Nat) (pointer result : Value)
    (valid : MintedValue bound pointer) (run : fatPtrMetadataValue pointer = some result) :
    MintedValue bound result := by
  cases pointer <;> simp only [fatPtrMetadataValue] at run <;> try contradiction
  case fatPtr address provenance metadata =>
    cases run
    exact (mintedValue_iff_shape bound _).1 valid

/-- Injection retains the metadata identities, independently of data provenance. -/
theorem pointer_from_parts_minted (bound : Nat) (data metadata result : Value)
    (valid : MintedValue bound metadata) (run : fatPtrFromPartsValue data metadata = some result) :
    MintedValue bound result := by
  cases data <;> simp only [fatPtrFromPartsValue] at run <;> try contradiction
  all_goals
    cases run
    exact (mintedValue_iff_shape bound _).2 valid

private theorem free_fresh_success (s final : MachineState) (value : Value) (id : ValueId)
    (valid : WellMintedState s) (free : MintedValue 0 value)
    (run : Sem.run (Sem.bindFresh value) s = .ok (id, final)) : WellMintedState final :=
  valid.fresh_success s final value id (free.mono (Nat.zero_le _)) run

private theorem throw_success {α : Type} (s final : MachineState) (value : α) (error : SemError)
    (run : Sem.run (throw error : Sem α) s = .ok (value, final)) : False := by
  cases run

private theorem target_success_state (model : ByteModel) (address : Nat) (s final : MachineState) (result : Nat)
    (run : Sem.run (Sem.targetAddress model "pointer projection/injection" address) s = .ok (result, final)) : final = s := by
  cases model with
  | le64 =>
    change Except.ok (address, s) = Except.ok (result, final) at run
    cases run
    rfl
  | le32 =>
    unfold Sem.targetAddress at run
    dsimp only at run
    split at run
    · change Except.ok (address, s) = Except.ok (result, final) at run
      cases run
      rfl
    · exact False.elim (throw_success s final result _ run)

/-- Actual PtrData retains all guards and provenance; it produces a frame-free
thin pointer without weakening any preexisting recursive identity invariant. -/
theorem WellMintedState.pointer_data_success (s final : MachineState) (ty : Ty)
    (operand id : ValueId) (model : ByteModel) (valid : WellMintedState s)
    (run : Sem.run (semPtrData ty operand model) s = .ok (id, final)) : WellMintedState final := by
  unfold semPtrData at run
  split at run
  · obtain ⟨held, middle, looked, tail⟩ := split_bind_success (Sem.lookupValue operand) _ s final id run
    obtain ⟨_, same⟩ := lookup_success s middle operand held looked
    subst middle
    simp only [Sem.throwTypeError] at tail
    repeat' first
      | (with_reducible refine free_fresh_success s final _ id valid ?_ tail)
        exact pointer_data_minted 0 held _ (by assumption)
      | with_reducible exact False.elim (throw_success s final id _ tail)
      | split at tail
  · split at run
    · obtain ⟨held, middle, looked, tail⟩ := split_bind_success (Sem.lookupValue operand) _ s final id run
      obtain ⟨_, same⟩ := lookup_success s middle operand held looked
      subst middle
      split at tail
      · obtain ⟨address, middle, checked, tail⟩ := split_bind_success _ _ s final id tail
        have same := target_success_state model _ s middle address checked
        subst middle
        exact free_fresh_success s final _ id valid (mintedValue_pointer 0 _ _) tail
      · exact free_fresh_success s final _ id valid (mintedValue_null 0) tail
      · exact False.elim (throw_success s final id _ tail)
    · exact False.elim (throw_success s final id _ run)

/-- Actual PtrMetadata transports recursively valid stored metadata or returns
frame-free Unit for thin pointers; original kind and target guards remain. -/
theorem WellMintedState.pointer_metadata_success (s final : MachineState) (ty metadataTy : Ty)
    (operand id : ValueId) (model : ByteModel) (valid : WellMintedState s)
    (run : Sem.run (semPtrMetadata ty metadataTy operand model) s = .ok (id, final)) : WellMintedState final := by
  unfold semPtrMetadata at run
  split at run
  · split at run
    · exact False.elim (throw_success s final id _ run)
    · obtain ⟨held, middle, looked, tail⟩ := split_bind_success (Sem.lookupValue operand) _ s final id run
      obtain ⟨lookup, same⟩ := lookup_success s middle operand held looked
      subst middle
      have original := valid.values operand held lookup
      simp only [Sem.throwTypeError] at tail
      repeat' first
        | (with_reducible refine valid.fresh_success s final _ id ?_ tail)
          exact pointer_metadata_minted _ held _ original (by assumption)
        | with_reducible exact False.elim (throw_success s final id _ tail)
        | split at tail
  · split at run
    · obtain ⟨held, middle, looked, tail⟩ := split_bind_success (Sem.lookupValue operand) _ s final id run
      obtain ⟨_, same⟩ := lookup_success s middle operand held looked
      subst middle
      have unitValid : MintedValue s.nextFrameLineage unitValue :=
        (mintedValue_iff_shape _ _).2 (fun _ member => nomatch member)
      simp only [Sem.throwTypeError] at tail
      repeat' first
        | with_reducible exact valid.fresh_success s final unitValue id unitValid tail
        | with_reducible exact False.elim (throw_success s final id _ tail)
        | split at tail
    · exact False.elim (throw_success s final id _ run)

private theorem reject_success_state (value : Value) (label : String) (s final : MachineState)
    (run : Sem.run (Sem.rejectPartial value label) s = .ok ((), final)) : final = s := by
  cases value <;>
    simp [Sem.rejectPartial, Sem.run, Sem.throwUB, StateT.run, StateT.pure,
      StateT.lift, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      bind, Except.bind] at run <;> exact run.symm

/-- Actual pointer injection preserves every metadata identity on the original
success path, including kind/metadata/Unit/poison checks and source lookups. -/
theorem WellMintedState.pointer_from_parts_success (s final : MachineState) (ty metadataTy : Ty)
    (dataId metadataId id : ValueId) (model : ByteModel) (valid : WellMintedState s)
    (run : Sem.run (semPtrFromParts ty metadataTy dataId metadataId model) s = .ok (id, final)) : WellMintedState final := by
  obtain ⟨data, middle, looked, tail⟩ := split_bind_success _ _ s final id run
  obtain ⟨_, same⟩ := lookup_success s middle dataId data looked
  subst middle
  obtain ⟨metadata, middle, looked, tail⟩ := split_bind_success _ _ s final id tail
  obtain ⟨lookup, same⟩ := lookup_success s middle metadataId metadata looked
  subst middle
  have original := valid.values metadataId metadata lookup
  obtain ⟨unit, middle, checked, tail⟩ := split_bind_success _ _ s final id tail
  cases unit
  have same := reject_success_state data "PtrFromParts data" s middle checked
  subst middle
  obtain ⟨unit, middle, checked, tail⟩ := split_bind_success _ _ s final id tail
  cases unit
  have same := reject_success_state metadata "PtrFromParts metadata" s middle checked
  subst middle
  simp only [Sem.throwTypeError] at tail
  repeat' first
    | with_reducible exact free_fresh_success s final _ id valid (mintedValue_pointer 0 _ _) tail
    | with_reducible exact free_fresh_success s final _ id valid (mintedValue_null 0) tail
    | (with_reducible refine valid.fresh_success s final _ id ?_ tail)
      exact pointer_from_parts_minted _ data metadata _ original (by assumption)
    | with_reducible exact False.elim (throw_success s final id _ tail)
    | split at tail

end TrustIr.FrameLifetime
