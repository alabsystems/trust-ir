/- Copyright 2026 Andrew Yates. Apache-2.0.
   Checked inversion contracts for the existing enum entry operations.
   No runtime/model definition is replaced. In particular, readInt does not
   normalize raw bits, and success does not establish canonical bit patterns
   or that the integer lane's type equals the declaration's canonical tag. -/
import ClosureConstruction

namespace SemR.EntryDomain

/-- Position denotes the original list entry, not an ordinal used as a tag. -/
theorem posOf_some_lookup {xs : List Int} {x : Int} {i : Nat}
    (h : posOf xs x = some i) : nth? xs i = some x := by
  induction xs generalizing i with
  | nil => simp [posOf] at h
  | cons y ys ih =>
    by_cases hy : y = x
    · simp [posOf, hy] at h
      subst i
      simp [nth?, hy]
    · cases hp : posOf ys x with
      | none => simp [posOf, hy, hp] at h
      | some j =>
        simp [posOf, hy, hp] at h
        subst i
        simpa [nth?] using ih hp

theorem nth_some_member {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : nth? xs i = some x) : x ∈ xs := by
  induction xs generalizing i with
  | nil => cases i <;> simp [nth?] at h
  | cons y ys ih =>
    cases i with
    | zero =>
      simp [nth?] at h
      simp [h]
    | succ i =>
      exact List.mem_cons_of_mem y (ih h)

/-- Successful nominal lookup identifies an actual declaration with this ID. -/
theorem findEnum_identity {defs : List EnumDef} {id : Nat} {d : EnumDef}
    (h : findEnum defs id = some d) : d.id = id ∧ d ∈ defs := by
  induction defs with
  | nil => simp [findEnum] at h
  | cons e es ih =>
    by_cases he : e.id = id
    · simp [findEnum, he] at h
      subst d
      exact ⟨he, by simp⟩
    · simp [findEnum, he] at h
      obtain ⟨hid, hm⟩ := ih h
      exact ⟨hid, List.mem_cons_of_mem e hm⟩

/-- Every successful active-field lookup retains the exact nominal declaration,
    actual integer lane/readInt value, tag position and original active variant.
    No canonical-bits or lane-type-equals-declared-tag conclusion is invented. -/
theorem activeFields_exact {m : Module} {id : Nat} {lanes : List Val} {fs : List Ty}
    (h : activeFields m id lanes = .ok fs) :
    ∃ (d : EnumDef) (t : IntTy) (raw : Nat) (tail : List Val) (i : Nat) (v : Variant),
      findEnum m.enums id = some d ∧ d.id = id ∧ d ∈ m.enums ∧
      lanes = .int t raw :: tail ∧
      posOf d.discs (readInt t.signed (t.bits m.pointerBits) raw) = some i ∧
      nth? d.discs i = some (readInt t.signed (t.bits m.pointerBits) raw) ∧
      nth? d.variants i = some v ∧ fs = v.fields := by
  cases hd : findEnum m.enums id with
  | none => simp [activeFields, hd, tyR] at h
  | some d =>
    cases lanes with
    | nil => simp [activeFields, hd, tyR] at h
    | cons lane tail =>
      cases lane <;> try { simp [activeFields, hd, tyR] at h }
      case int t raw =>
        cases hp : posOf d.discs (readInt t.signed (t.bits m.pointerBits) raw) with
        | none => simp [activeFields, hd, hp, tyR] at h
        | some i =>
          cases hv : nth? d.variants i with
          | none => simp [activeFields, hd, hp, hv, tyR] at h
          | some v =>
            simp [activeFields, hd, hp, hv] at h
            obtain ⟨hid, hm⟩ := findEnum_identity hd
            exact ⟨d, t, raw, tail, i, v, rfl, hid, hm, rfl,
              hp, posOf_some_lookup hp, hv, h.symm⟩

/-- The actual signed reading belongs to the declaration's tag set. Payload
    values and raw patterns remain untouched by this inversion theorem. -/
theorem activeFields_declared_tag {m : Module} {id : Nat} {lanes : List Val} {fs : List Ty}
    (h : activeFields m id lanes = .ok fs) :
    ∃ (d : EnumDef) (t : IntTy) (raw : Nat) (tail : List Val),
      findEnum m.enums id = some d ∧ d.id = id ∧
      lanes = .int t raw :: tail ∧
      readInt t.signed (t.bits m.pointerBits) raw ∈ d.discs := by
  obtain ⟨d, t, raw, tail, i, v, hd, hid, _, hl, _, hn, _, _⟩ := activeFields_exact h
  exact ⟨d, t, raw, tail, hd, hid, hl, nth_some_member hn⟩

/-- A successful payload lane guard uses precisely the active variant's
    declared field. The positive lane requirement reflects evalExtract's guard;
    checkLane alone does not distinguish payload lane one from lane zero. -/
theorem checkLane_exact {m : Module} {id : Nat} {lanes : List Val} {field : Nat} {t : Ty}
    (hf : 1 ≤ field) (h : checkLane m id lanes field t = .ok ()) :
    1 ≤ field ∧ ∃ fs, activeFields m id lanes = .ok fs ∧ nth? fs (field - 1) = some t := by
  refine ⟨hf, ?_⟩
  unfold checkLane at h
  change R.bind _ _ = R.ok () at h
  cases ha : activeFields m id lanes with
  | stop o => simp [ha, R.bind] at h
  | ok fs =>
    cases hn : nth? fs (field - 1) with
    | none => simp [ha, R.bind, hn, ubR] at h
    | some lt =>
      by_cases ht : lt = t
      · subst lt
        exact ⟨fs, rfl, hn⟩
      · have hb : lt.beq t = false := by
          cases hb : lt.beq t with
          | false => rfl
          | true => exact False.elim (ht ((ty_beq_exact lt t).mp hb))
        simp [ha, R.bind, hn, hb, ubR] at h

/-- Compose the checked inversions: the requested payload type belongs to the
    exact original active variant of the nominal definition. This says nothing
    about the existence, initialization or normalization of a payload VALUE. -/
theorem checkLane_nominal_field {m : Module} {id : Nat} {lanes : List Val}
    {field : Nat} {ty : Ty} (hf : 1 ≤ field)
    (h : checkLane m id lanes field ty = .ok ()) :
    ∃ (d : EnumDef) (t : IntTy) (raw : Nat) (tail : List Val) (i : Nat) (v : Variant),
      findEnum m.enums id = some d ∧ d.id = id ∧ d ∈ m.enums ∧
      lanes = .int t raw :: tail ∧
      nth? d.discs i = some (readInt t.signed (t.bits m.pointerBits) raw) ∧
      nth? d.variants i = some v ∧ nth? v.fields (field - 1) = some ty := by
  obtain ⟨_, fs, hfs, hty⟩ := checkLane_exact hf h
  obtain ⟨d, t, raw, tail, i, v, hd, hid, hm, hl, _, htag, hv, hfields⟩ := activeFields_exact hfs
  exact ⟨d, t, raw, tail, i, v, hd, hid, hm, hl, htag, hv, by simpa [hfields] using hty⟩

end SemR.EntryDomain
