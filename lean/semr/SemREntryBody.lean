/- Copyright 2026 Andrew Yates. Apache-2.0.
   Actual enum payload reads compose the declared entry contract with an
   existing value and the evaluator's own type/range check. No source marker,
   new runtime/model operation or source-certification authority is supplied. -/
import SemREntry

namespace SemR.EntryDomain

private theorem bind_success {α β : Type} {x : R α} {f : α → R β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | stop o => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- The value is an actual selected lane, not a fabricated inhabitant of its
    declared field type. Type/range admission is the real evaluator check. -/
theorem evalExtract_enum_of_checked (m : Module) (ty : Ty) (id field : Nat)
    (lanes : List Val) (value : Val)
    (hc : checkLane m id lanes field ty = .ok ()) (hp : 1 ≤ field)
    (hv : nth? lanes field = some value)
    (ht : expectTy m.pointerBits value ty = .ok ()) :
    evalExtract m ty (.enum id lanes) field = .ok value := by
  simp [evalExtract, rejectPoison, hp, hc, hv, ht, ok_bind] <;> rfl

/-- A successful read supplies its own guard, existing value and actual type
    check. In particular declaration lookup alone supplies none of these. -/
theorem evalExtract_enum_success {m : Module} {ty : Ty} {id field : Nat}
    {lanes : List Val} {value : Val} (hp : 1 ≤ field)
    (h : evalExtract m ty (.enum id lanes) field = .ok value) :
    checkLane m id lanes field ty = .ok () ∧
    nth? lanes field = some value ∧ expectTy m.pointerBits value ty = .ok () := by
  have hx : (checkLane m id lanes field ty >>= fun _ =>
      match nth? lanes field with
      | none => ubR "field is out of bounds"
      | some v => do expectTy m.pointerBits v ty; pure v) = .ok value := by
    simpa [evalExtract, rejectPoison, hp, ok_bind] using h
  obtain ⟨u, hc, hr⟩ := bind_success hx
  cases u
  cases hv : nth? lanes field with
  | none => simp [hv, ubR] at hr
  | some v =>
    have ht : (expectTy m.pointerBits v ty >>= fun _ => R.ok v) = .ok value := by
      simpa [hv] using hr
    obtain ⟨u, htype, he⟩ := bind_success ht
    cases u
    have heq : v = value := R.ok.inj he
    subst value
    exact ⟨hc, rfl, htype⟩

/-- Only the successful integer type check, not a raw type tag, establishes
    the full word representation bound required by later numeric semantics. -/
theorem checked_integer_raw_bound {pointerBits : Nat} {t : IntTy} {raw : Nat}
    (h : expectTy pointerBits (.int t raw) (.int t) = .ok ()) :
    raw < modulus (t.bits pointerBits) := by
  by_cases hn : raw < modulus (t.bits pointerBits)
  · exact hn
  · simp [expectTy, Val.ty, Ty.beq, hn, tyR] at h

/-- Read success ties the exact returned value to the original active nominal
    field. It grants no initialization, byte-refinement or source authority. -/
theorem evalExtract_enum_nominal {m : Module} {ty : Ty} {id field : Nat}
    {lanes : List Val} {value : Val} (hp : 1 ≤ field)
    (h : evalExtract m ty (.enum id lanes) field = .ok value) :
    ∃ (d : EnumDef) (t : IntTy) (raw : Nat) (tail : List Val) (i : Nat) (v : Variant),
      findEnum m.enums id = some d ∧ d.id = id ∧ d ∈ m.enums ∧
      lanes = .int t raw :: tail ∧
      nth? d.discs i = some (readInt t.signed (t.bits m.pointerBits) raw) ∧
      nth? d.variants i = some v ∧ nth? v.fields (field - 1) = some ty ∧
      nth? lanes field = some value ∧ expectTy m.pointerBits value ty = .ok () := by
  obtain ⟨hc, hv, ht⟩ := evalExtract_enum_success hp h
  obtain ⟨d, t, raw, tail, i, v, hd, hid, hm, hl, hg, hvar, hf⟩ := checkLane_nominal_field hp hc
  exact ⟨d, t, raw, tail, i, v, hd, hid, hm, hl, hg, hvar, hf, hv, ht⟩

/-- The magnitude-comparison leaf used by coverage_supports: two successful
    ORIGINAL u64 payload reads supply their real word bounds and compose with
    the existing unsigned comparison. These are execution results, never
    authored domain preconditions or a claim that a MIR quotation was proved. -/
theorem enum_u64_payload_ge {m : Module} {leftId rightId leftField rightField : Nat}
    {left right : List Val} {supply need : Nat}
    (hlp : 1 ≤ leftField) (hrp : 1 ≤ rightField)
    (hl : evalExtract m (.int .u64) (.enum leftId left) leftField = .ok (.int .u64 supply))
    (hr : evalExtract m (.int .u64) (.enum rightId right) rightField = .ok (.int .u64 need)) :
    supply < modulus 64 ∧ need < modulus 64 ∧
    (do let l ← evalExtract m (.int .u64) (.enum leftId left) leftField
        let r ← evalExtract m (.int .u64) (.enum rightId right) rightField
        evalIcmp m.pointerBits .uge (.int .u64) l r) = .ok (.bool (decide (need ≤ supply))) := by
  obtain ⟨_, _, hlt⟩ := evalExtract_enum_success hlp hl
  obtain ⟨_, _, hrt⟩ := evalExtract_enum_success hrp hr
  have cmp : evalIcmp m.pointerBits .uge (.int .u64) (.int .u64 supply) (.int .u64 need) =
      .ok (.bool (decide (need ≤ supply))) := by
    simp only [evalIcmp, hlt, hrt, ok_bind]
    rfl
  exact ⟨checked_integer_raw_bound hlt, checked_integer_raw_bound hrt,
    by simpa only [hl, hr, ok_bind] using cmp⟩

/-- The original SSA operation changes exactly its PC/result binding. No new
    value, allocation, memory, lineage or payload environment is invented. -/
theorem extractEnumStep_exact (m : Module) (k : Core) (ty : Ty)
    (id aggregate field result : Nat) (lanes : List Val) (value : Val)
    (ha : getV k aggregate = .ok (.enum id lanes))
    (he : evalExtract m ty (.enum id lanes) field = .ok value) :
    extractFieldStep m k ⟨.extractField ty aggregate field, [result]⟩ ty aggregate field =
      .ok { next k with env := (result, value) :: k.env } := by
  simp only [extractFieldStep, ha, ok_bind, he]
  rfl

/-- Consume an actual relational body step, not a solver's free Boolean. -/
theorem extractEnum_step_exact (m : Module) (k after : Core) (ty : Ty)
    (id aggregate field result : Nat) (lanes : List Val) (value : Val)
    (hn : nth? k.block.body k.pc = some ⟨.extractField ty aggregate field, [result]⟩)
    (ha : getV k aggregate = .ok (.enum id lanes))
    (he : evalExtract m ty (.enum id lanes) field = .ok value)
    (h : Step m k (.cont after)) :
    after = { next k with env := (result, value) :: k.env } := by
  have run := step_sound m k (.cont after) h
  simp only [stepCore, hn, execNode,
    extractEnumStep_exact m k ty id aggregate field result lanes value ha he,
    ofR, StepR.cont.injEq] at run
  exact run.symm

end SemR.EntryDomain
