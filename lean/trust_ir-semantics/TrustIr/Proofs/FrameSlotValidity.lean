-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameValueValidity

namespace TrustIr.FrameLifetime

/-- Slot typing transports unbound poison separately from initialized values.
`accepts` is the input language's value-typing relation, not a new runtime check. -/
def SlotTyped (accepts : Ty → Value → Prop) (ty : Ty) (value : Value) : Prop :=
  value = .undef ty ∨ accepts ty value

/-- Exact positional agreement with the original declared slot signature.
Unlike zip-based checks, this relation also enforces equal lengths. -/
inductive SlotsTyped (accepts : Ty → Value → Prop) : List BindingSlot → List Value → Prop where
  | nil : SlotsTyped accepts [] []
  | cons {declared : BindingSlot} {value : Value} {signature : List BindingSlot} {values : List Value} :
      SlotTyped accepts declared.ty value → SlotsTyped accepts signature values →
      SlotsTyped accepts (declared :: signature) (value :: values)

theorem SlotsTyped.length {accepts : Ty → Value → Prop} {signature : List BindingSlot}
    {values : List Value} (valid : SlotsTyped accepts signature values) :
    signature.length = values.length := by
  induction valid with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem slots_initial (accepts : Ty → Value → Prop) (signature : List BindingSlot) :
    SlotsTyped accepts signature (signature.map (fun slot => .undef slot.ty)) := by
  induction signature with
  | nil => exact .nil
  | cons slot rest ih => exact .cons (Or.inl rfl) ih

/-- A declared slot lookup recovers the corresponding actual payload and its
type relation, including an unbound poison payload. -/
theorem SlotsTyped.lookup {accepts : Ty → Value → Prop} {signature : List BindingSlot}
    {values : List Value} (valid : SlotsTyped accepts signature values)
    (index : Nat) (declared : BindingSlot) (found : trustIrListGet? signature index = some declared) :
    ∃ value, trustIrListGet? values index = some value ∧ SlotTyped accepts declared.ty value := by
  induction valid generalizing index with
  | nil => cases found
  | @cons head value signature values typed _ ih =>
    cases index with
    | zero =>
      simp at found
      cases found
      exact ⟨value, rfl, typed⟩
    | succ index => exact ih index found

/-- Functional update preserves the complete declaration, not just the
selected slot, when the inserted value has that slot's declared type. -/
theorem SlotsTyped.update {accepts : Ty → Value → Prop} {signature : List BindingSlot}
    {values : List Value} (valid : SlotsTyped accepts signature values)
    (index : Nat) (declared : BindingSlot) (found : trustIrListGet? signature index = some declared)
    (value : Value) (operand : accepts declared.ty value) :
    SlotsTyped accepts signature (values.set index value) := by
  induction valid generalizing index with
  | nil => cases found
  | @cons head original signature values typed tail ih =>
    cases index with
    | zero =>
      simp at found
      cases found
      exact .cons (Or.inr operand) tail
    | succ index => exact .cons typed (ih index found)

/-- A source SSA handle with its actual snapshot and declared signature. The
signature is an explicit validated-input premise, not recovered from lineage. -/
def TypedFrameAt (accepts : Ty → Value → Prop) (signature : List BindingSlot)
    (state : MachineState) (id : ValueId) : Prop :=
  ∃ lineage values, state.lookupValue id = some (.frame lineage values) ∧
    SlotsTyped accepts signature values

theorem open_success_signature (accepts : Ty → Value → Prop)
    (s final : MachineState) (definition : BindingFrameDef) (result : ValueId)
    (run : Sem.run (semOpenFrame definition) s = .ok (result, final)) :
    TypedFrameAt accepts definition.slots final result := by
  by_cases room : s.nextFrameLineage < 2^64-1
  · rw [open_run s definition room] at run
    cases run
    refine ⟨s.nextFrameLineage, definition.slots.map (fun slot => .undef slot.ty), ?_,
      slots_initial accepts definition.slots⟩
    simp [afterOpen, initFrame, MachineState.lookupValue, ValueMap.get, ValueMap.set]
  · rw [open_overflow_run s definition room] at run
    contradiction

theorem bind_success_signature (accepts : Ty → Value → Prop)
    (signature : List BindingSlot) (s final : MachineState)
    (frame rhs result : ValueId) (index : Nat) (declared : BindingSlot)
    (source : TypedFrameAt accepts signature s frame)
    (found : trustIrListGet? signature index = some declared)
    (operand : ∀ value, s.lookupValue rhs = some value → accepts declared.ty value)
    (run : Sem.run (semBindSlot frame index rhs) s = .ok (result, final)) :
    TypedFrameAt accepts signature final result := by
  obtain ⟨origin, lineage, values, value, lookup, rhsLookup, _, _, rfl, rfl⟩ :=
    bind_success_state s final frame rhs result index run
  obtain ⟨originalLineage, originalValues, originalLookup, typed⟩ := source
  cases origin with
  | none =>
    rw [lookup] at originalLookup
    cases originalLookup
    exact ⟨lineage, values.set index value,
      bind_new_snapshot s lineage values index value,
      typed.update index declared found value (operand value rhsLookup)⟩
  | some origin =>
    rcases origin with ⟨function, declaration⟩
    rw [lookup] at originalLookup
    cases originalLookup

/-- A successful load returns the declaration's value or its own unbound
poison, regardless of the requested type. Validation supplies the type bridge. -/
theorem load_success_declared_signature (accepts : Ty → Value → Prop)
    (signature : List BindingSlot) (s final : MachineState)
    (frame result : ValueId) (index : Nat) (declared : BindingSlot) (requested : Ty)
    (source : TypedFrameAt accepts signature s frame)
    (found : trustIrListGet? signature index = some declared)
    (run : Sem.run (semLoadSlot frame index requested) s = .ok (result, final)) :
    ∃ value, final.lookupValue result = some value ∧ SlotTyped accepts declared.ty value := by
  obtain ⟨origin, lineage, values, value, lookup, _, selected, rfl, rfl⟩ :=
    load_success_state s final frame result index requested run
  obtain ⟨originalLineage, originalValues, originalLookup, typed⟩ := source
  cases origin with
  | none =>
    rw [lookup] at originalLookup
    cases originalLookup
    obtain ⟨expected, payload, valid⟩ := typed.lookup index declared found
    rw [selected] at payload
    cases payload
    refine ⟨value, ?_, ?_⟩
    · simp [afterLoad, MachineState.lookupValue, ValueMap.get, ValueMap.set]
    · exact valid
  | some origin =>
    rcases origin with ⟨function, declaration⟩
    rw [lookup] at originalLookup
    cases originalLookup

/-- Exact declaration agreement transports the load result to the requested
type. A refinement bridge may instead use load_success_declared_signature. -/
theorem load_success_signature (accepts : Ty → Value → Prop)
    (signature : List BindingSlot) (s final : MachineState)
    (frame result : ValueId) (index : Nat) (declared : BindingSlot) (requested : Ty)
    (source : TypedFrameAt accepts signature s frame)
    (found : trustIrListGet? signature index = some declared) (agreement : requested = declared.ty)
    (run : Sem.run (semLoadSlot frame index requested) s = .ok (result, final)) :
    ∃ value, final.lookupValue result = some value ∧ SlotTyped accepts requested value := by
  obtain ⟨value, lookup, valid⟩ :=
    load_success_declared_signature accepts signature s final frame result index declared requested source found run
  exact ⟨value, lookup, agreement.symm ▸ valid⟩

/-- Closing a lineage preserves its snapshot's typing even though subsequent
loads must refuse the closed handle. Typing is not a liveness assertion. -/
theorem close_success_signature (accepts : Ty → Value → Prop)
    (signature : List BindingSlot) (s final : MachineState) (closing handle : ValueId)
    (source : TypedFrameAt accepts signature s handle)
    (run : Sem.run (semCloseFrame closing) s = .ok ((), final)) :
    TypedFrameAt accepts signature final handle := by
  obtain ⟨_, lineage, _, _, _, rfl⟩ := close_success_state s final closing run
  exact source

/-- Negative boundary: the actual runtime ignores LoadSlot's requested type.
A valid unbound I32 snapshot can return I32 poison from a Bool-typed load. -/
theorem requested_type_needs_validation :
    let s := { MachineState.empty with
      locals := ValueMap.empty.set ⟨0⟩ (.frame 0 [.undef .I32])
      nextValueId := 1, openFrameLineages := [0], nextFrameLineage := 1 }
    TypedFrameAt (fun _ _ => False) [⟨"x", .I32⟩] s ⟨0⟩ ∧
      (Sem.run (do let id ← semLoadSlot ⟨0⟩ 0 .Bool; Sem.lookupValue id) s).map Prod.fst =
        .ok (.undef .I32) ∧
      ¬ SlotTyped (fun _ _ => False) .Bool (.undef .I32) := by
  refine ⟨⟨0, [.undef .I32], rfl, .cons (Or.inl rfl) .nil⟩, rfl, ?_⟩
  simp [SlotTyped]

/-- The actual bind/load pipeline does not establish operand typing. Here a
well-typed unbound scalar slot is overwritten by a Bool and loaded as I32. -/
theorem inserted_type_needs_validation :
    let accepts := fun ty value => ty = Ty.I32 ∧ ∃ n, value = Value.int 32 n
    let s := { MachineState.empty with
      locals := (ValueMap.empty.set ⟨0⟩ (.frame 0 [.undef .I32])).set ⟨1⟩ (.bool true)
      nextValueId := 2, openFrameLineages := [0], nextFrameLineage := 1 }
    TypedFrameAt accepts [⟨"x", .I32⟩] s ⟨0⟩ ∧
      (Sem.run (do
        let frame ← semBindSlot ⟨0⟩ 0 ⟨1⟩
        let value ← semLoadSlot frame 0 .I32
        Sem.lookupValue value) s).map Prod.fst = .ok (.bool true) ∧
      ¬ SlotTyped accepts .I32 (.bool true) := by
  refine ⟨⟨0, [.undef .I32], rfl, .cons (Or.inl rfl) .nil⟩, rfl, ?_⟩
  simp [SlotTyped]

end TrustIr.FrameLifetime
