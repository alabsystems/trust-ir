-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.PointerObservationProps

namespace TrustIr

/-- Complete raw-carrier result, including destination-type errors and the
    u64 boundary. Every successful integer is canonical at its target width. -/
theorem rawPointerInteger_run (op : String) (ty : Ty) (address : Nat)
    (model : ByteModel) (state : MachineState) :
    Sem.run (Sem.bindPointerIntegerWithProvenance op ty address none model) state =
      match getTyWidth ty model with
      | .error error => .error error
      | .ok width =>
        if address < word64Limit then
          .ok (state.bindValue (Value.intAt width (Int.ofNat address)))
        else .error (.ub s!"{op}: pointer address exceeds the u64 carrier") := by
  unfold Sem.bindPointerIntegerWithProvenance
  cases getTyWidth ty model with
  | error error => simp only [Sem.run, sr_bind, sr_throw, Except.bind]
  | ok width =>
    simp only [pure_bind]
    split <;> rfl

/-- Allocation-derived pointers retain the original target-bounded helper. -/
theorem derivedPointerInteger_unchanged (op : String) (ty : Ty) (address : Nat)
    (allocation : AllocId) (model : ByteModel) :
    Sem.bindPointerIntegerWithProvenance op ty address (some allocation) model =
      Sem.bindPointerInteger op ty address model := by rfl

/-- Invalid destination types are reported before any carrier-range refusal. -/
theorem rawPointerInteger_width_error_first (op : String) (ty : Ty) (address : Nat)
    (model : ByteModel) (state : MachineState) (error : SemError)
    (widthError : getTyWidth ty model = .error error) :
    Sem.run (Sem.bindPointerIntegerWithProvenance op ty address none model) state =
      .error error := by
  rw [rawPointerInteger_run, widthError]

/-- Raw success publishes one canonical integer and retains the u64 bound. -/
theorem rawPointerInteger_success (op : String) (ty : Ty) (address : Nat)
    (model : ByteModel) (state finalState : MachineState) (id : ValueId)
    (success : Sem.run (Sem.bindPointerIntegerWithProvenance op ty address none model) state =
      .ok (id, finalState)) :
    address < word64Limit ∧
      ∃ width raw, getTyWidth ty model = .ok width ∧
        finalState.lookupValue id = some (.int width raw) ∧
        0 ≤ raw ∧ raw < 2 ^ width := by
  trustIrCompilerProof {
    rw [rawPointerInteger_run] at success
    cases widthResult : getTyWidth ty model with
    | error error => simp only [widthResult] at success
    | ok width =>
      simp only [widthResult] at success
      by_cases bound : address < word64Limit
      · simp only [bound, if_pos] at success
        have pair := Except.ok.inj success
        have hi : (state.bindValue (Value.intAt width (Int.ofNat address))).fst = id :=
          congrArg Prod.fst pair
        have hs : (state.bindValue (Value.intAt width (Int.ofNat address))).snd = finalState :=
          congrArg Prod.snd pair
        refine ⟨bound, width, truncateUnsigned (Int.ofNat address) width, rfl, ?_,
          truncateUnsigned_nonneg _ _, truncateUnsigned_lt _ _⟩
        rw [← hs, ← hi]
        simp [MachineState.bindValue, MachineState.lookupValue, ValueMap.get,
          ValueMap.set, Value.intAt]
      · simp only [bound, if_neg] at success
        cases success
  } {
    rw [rawPointerInteger_run] at success
    cases widthResult : getTyWidth ty model with
    | error error =>
      simp only [widthResult] at success
      cases success
    | ok width =>
      simp only [widthResult] at success
      by_cases bound : address < word64Limit
      · simp only [bound, if_pos] at success
        have pair := Except.ok.inj success
        have hi : (state.bindValue (Value.intAt width (Int.ofNat address))).fst = id :=
          congrArg Prod.fst pair
        have hs : (state.bindValue (Value.intAt width (Int.ofNat address))).snd = finalState :=
          congrArg Prod.snd pair
        refine ⟨bound, width, truncateUnsigned (Int.ofNat address) width, rfl, ?_,
          truncateUnsigned_nonneg _ _, truncateUnsigned_lt _ _⟩
        rw [← hs, ← hi]
        simp [MachineState.bindValue, MachineState.lookupValue, ValueMap.get,
          ValueMap.set, Value.intAt]
      · simp only [bound, if_neg] at success
        cases success
  }

/-- The actual PtrToInt branch selects the provenance-aware helper after its
    ordinary lookup and partial-value check; no extra state premise occurs. -/
theorem ptrToInt_raw_lookup (ty : Ty) (address : Nat) (input : ValueId)
    (model : ByteModel) (state : MachineState)
    (lookup : state.lookupValue input = some (.ptr address none)) :
    Sem.run (semCast .PtrToInt .Ptr ty input model) state =
      Sem.run (Sem.bindPointerIntegerWithProvenance "PtrToInt" ty address none model) state := by
  simp only [semCast, Sem.run, sr_bind, sr_lookup, lookup, Except.bind]
  rfl

/-- A raw address already representable in the destination is unchanged. -/
theorem rawPointerInteger_in_range (op : String) (ty : Ty) (address width : Nat)
    (model : ByteModel) (state : MachineState)
    (destination : getTyWidth ty model = .ok width)
    (carrier : address < word64Limit) (fits : (Int.ofNat address) < 2 ^ width) :
    Sem.run (Sem.bindPointerIntegerWithProvenance op ty address none model) state =
      .ok (state.bindValue (.int width (Int.ofNat address))) := by
  rw [rawPointerInteger_run, destination]
  dsimp only
  rw [if_pos carrier]
  unfold Value.intAt
  rw [truncateUnsigned_of_residue (v := Int.ofNat address) (w := width)
    (Int.ofNat_zero_le address) fits]

theorem raw_far32_to_u128 (state : MachineState) :
    Sem.run (Sem.bindPointerIntegerWithProvenance "PtrToInt" .U128 4294967297 none .le32) state =
      .ok (state.bindValue (Value.intAt 128 4294967297)) := by rfl

theorem raw_far32_to_u32 (state : MachineState) :
    Sem.run (Sem.bindPointerIntegerWithProvenance "Bitcast" .U32 4294967297 none .le32) state =
      .ok (state.bindValue (.int 32 1)) := by rfl

theorem raw_far32_to_usize (state : MachineState) :
    Sem.run (Sem.bindPointerIntegerWithProvenance "PtrToInt" .Usize 4294967297 none .le32) state =
      .ok (state.bindValue (.int 32 1)) := by rfl

theorem raw_u64_max_to_u128 (state : MachineState) :
    Sem.run (Sem.bindPointerIntegerWithProvenance "PtrToInt" .U128 18446744073709551615 none .le32) state =
      .ok (state.bindValue (Value.intAt 128 18446744073709551615)) := by rfl

theorem raw_u64_overflow_refused (state : MachineState) :
    Sem.run (Sem.bindPointerIntegerWithProvenance "PtrToInt" .U128 18446744073709551616 none .le32) state =
      .error (.ub "PtrToInt: pointer address exceeds the u64 carrier") := by rfl

theorem derived_far32_still_refused (state : MachineState) (allocation : AllocId) :
    Sem.run (Sem.bindPointerIntegerWithProvenance "PtrToInt" .U128 4294967296 (some allocation) .le32) state =
      .error (.ub "PtrToInt: pointer address exceeds the target width") := by rfl

end TrustIr
