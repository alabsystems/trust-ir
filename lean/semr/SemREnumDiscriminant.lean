/- Declaration-derived tag/read/cast contracts for existing enum semantics.
   No runtime operation, interpreter, frontend profile or source grade changes.
   Tag read success alone does NOT establish canonical declaration tag typing
   or variant membership; actual active-field success supplies the latter. -/
import SemREntryBody
namespace SemR.EntryDomain

private theorem stop_bind {α β : Type} (out : Out) (f : α → R β) :
    (R.stop out >>= f) = R.stop out := rfl

private theorem pure_ok {α : Type} (x : α) : (pure x : R α) = .ok x := rfl

/-- A successful actual tag read keeps the original head lane and its actual
    integer range check. It supplies no new/canonical bits or variant identity. -/
theorem enum_tag_read_success {m : Module} {id : Nat} {lanes : List Val}
    {t : IntTy} {raw : Nat}
    (read : evalExtract m (.int t) (.enum id lanes) 0 = .ok (.int t raw)) :
    ∃ tail, lanes = .int t raw :: tail ∧ raw < modulus (t.bits m.pointerBits) := by
  cases lanes with
  | nil => simp [evalExtract, rejectPoison, nth?, ok_bind, pure_ok, ubR] at read
  | cons head tail =>
    cases hc : expectTy m.pointerBits head (.int t) with
    | stop out => simp [evalExtract, rejectPoison, nth?, ok_bind, stop_bind, pure_ok, hc] at read
    | ok u =>
      cases u
      have same : head = .int t raw := by
        simpa [evalExtract, rejectPoison, nth?, ok_bind, stop_bind, pure_ok, hc] using read
      subst head
      exact ⟨tail,rfl,checked_integer_raw_bound hc⟩

/-- The source lane's signedness selects SExt or ZExt. No destination signedness
    heuristic or global arbitrary-tag assumption replaces the actual word check.
    Strict widening is an explicit instruction-admission boundary. -/
theorem checked_tag_cast {pointerBits : Nat} {t destination : IntTy} {raw : Nat}
    (checked : expectTy pointerBits (.int t raw) (.int t) = .ok ())
    (_widen : t.bits pointerBits < destination.bits pointerBits) :
    evalCast pointerBits (if t.signed then .sext else .zext)
      (.int t) (.int destination) (.int t raw) =
      .ok (.int destination (resid (destination.bits pointerBits)
        (readInt t.signed (t.bits pointerBits) raw))) := by
  cases hs : t.signed <;>
    simp [evalCast, rejectPoison, checked, castCore, resizeOf, hs, readInt, resid, ok_bind, pure_ok]

/-- ACTUAL active-field and tag-read results identify the original declaration,
    ordinal and variant, then compose with the existing cast implementation.
    No integer bounds, canonical-tag equality or Rust valid-value embedding are
    authored as source preconditions. In particular activeFields itself does
    not validate raw bounds or canonical lane typing; the actual read supplies
    bounds and the declaration/host relation stays explicit. -/
theorem enum_discriminant_cast {m : Module} {id : Nat} {lanes : List Val}
    {fields : List Ty} {t destination : IntTy} {raw : Nat}
    (active : activeFields m id lanes = .ok fields)
    (read : evalExtract m (.int t) (.enum id lanes) 0 = .ok (.int t raw))
    (widen : t.bits m.pointerBits < destination.bits m.pointerBits) :
    ∃ (declaration : EnumDef) (ordinal : Nat) (variant : Variant),
      findEnum m.enums id = some declaration ∧ declaration.id = id ∧
      declaration ∈ m.enums ∧
      nth? declaration.discs ordinal =
        some (readInt t.signed (t.bits m.pointerBits) raw) ∧
      nth? declaration.variants ordinal = some variant ∧ variant.fields = fields ∧
      raw < modulus (t.bits m.pointerBits) ∧
      evalCast m.pointerBits (if t.signed then .sext else .zext)
        (.int t) (.int destination) (.int t raw) =
        .ok (.int destination (resid (destination.bits m.pointerBits)
          (readInt t.signed (t.bits m.pointerBits) raw))) := by
  obtain ⟨tail,hl,bound⟩ := enum_tag_read_success read
  subst lanes
  obtain ⟨d,t',raw',tail',ordinal,variant,hd,hid,hm,hl,hpos,hdisc,hvariant,hfields⟩ :=
    activeFields_exact active
  cases hl
  have checked : expectTy m.pointerBits (.int t raw) (.int t) = .ok () := by
    simp [expectTy, Val.ty, Ty.beq, bound]
  exact ⟨d,ordinal,variant,hd,hid,hm,hdisc,hvariant,hfields.symm,bound,
    checked_tag_cast checked widen⟩
end SemR.EntryDomain
