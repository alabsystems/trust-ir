/- Copyright 2026 Andrew Yates. Apache-2.0.
   Laws for the canonical quoted sited assertion. No binary decoder path.
   Static metadata below is an explicit projection; its binding to complete
   canonical module bytes remains owed. -/
import SemR

namespace SemR.SitedDivPanic

/-- Metadata missing from SemR.Func today. No convention, linkage or global
    initializer bytes are reconstructed from this field projection. -/
structure EntryHeader where
  id : Nat
  weak : Bool

structure GlobalHeader where
  mutable : Bool
  threadLocal : Bool

/-- Static projection, not a new module decoder or validator equivalence.
    Function identities use sparse keys; globals use vector positions. -/
structure Metadata where
  module : Module
  entries : List EntryHeader
  globals : List GlobalHeader

def entryMatches (id : Nat) (fs : List Func) : List Func :=
  fs.filter (fun f => f.id == id)

def headerMatches (id : Nat) (hs : List EntryHeader) : List EntryHeader :=
  hs.filter (fun h => h.id == id)

/-- Exact supported pointer signature. Ref/PtrConst are not collapsed into
    Ptr; those canonical type forms remain outside this semantic slice. -/
def ptrEntry (signature : FuncTy) : Bool :=
  match signature.params, signature.returns, signature.vararg with
  | [.ptr], [], false => true
  | _, _, _ => false

def admissible (metadata : Metadata) (site : Site) : Bool :=
  match entryMatches site.entry metadata.module.functions,
      headerMatches site.entry metadata.entries,
      nth? metadata.globals site.global with
  | [f], [header], some global =>
    match nth? metadata.module.funcTys f.ty with
    | some signature => !header.weak && !global.mutable && !global.threadLocal && ptrEntry signature
    | none => false
  | _, _, _ => false

/-- Independent static proposition with all supported admission conditions.
    It assumes the projection's binding to its source; no theorem here supplies
    that absent byte-level/module-header correspondence. -/
def Admissible (metadata : Metadata) (site : Site) : Prop :=
  ∃ f header global signature,
    entryMatches site.entry metadata.module.functions = [f] ∧
    headerMatches site.entry metadata.entries = [header] ∧
    nth? metadata.globals site.global = some global ∧
    nth? metadata.module.funcTys f.ty = some signature ∧
    header.weak = false ∧ global.mutable = false ∧ global.threadLocal = false ∧
    signature.params = [.ptr] ∧ signature.returns = [] ∧ signature.vararg = false

theorem admissible_of (metadata : Metadata) (site : Site) (h : Admissible metadata site) :
    admissible metadata site = true := by
  rcases h with ⟨f, header, global, signature, hf, hh, hg, hs, hw, hm, ht, hp, hr, hv⟩
  simp [admissible, hf, hh, hg, hs, hw, hm, ht, ptrEntry, hp, hr, hv]

theorem ptrEntry_sound (signature : FuncTy) (h : ptrEntry signature = true) :
    signature.params = [.ptr] ∧ signature.returns = [] ∧ signature.vararg = false := by
  unfold ptrEntry at h
  split at h <;> simp_all

theorem admissible_sound (metadata : Metadata) (site : Site)
    (h : admissible metadata site = true) : Admissible metadata site := by
  unfold admissible at h
  split at h
  · rename_i f header global hf hh hg
    split at h
    · rename_i signature hs
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      rcases h with ⟨⟨⟨hw, hm⟩, ht⟩, hp⟩
      obtain ⟨hparams, hreturns, hvararg⟩ := ptrEntry_sound signature hp
      exact ⟨f, header, global, signature, hf, hh, hg, hs, hw, hm, ht,
        hparams, hreturns, hvararg⟩
    · contradiction
  · contradiction

theorem admissible_iff (metadata : Metadata) (site : Site) :
    admissible metadata site = true ↔ Admissible metadata site :=
  ⟨admissible_sound metadata site, admissible_of metadata site⟩

theorem true_exact (k : Core) (kind : DivPanicKind) (site : Site) :
    on k kind site (.bool true) = .ok (next k) := by rfl

theorem false_exact (k : Core) (kind : DivPanicKind) (site : Site) :
    on k kind site (.bool false) =
      .stop (.globalDivPanic ⟨kind, none, site.entry, site.global, 0⟩) := by rfl

/-- All Core fields are preserved except the instruction counter. -/
theorem true_preserves (k : Core) (kind : DivPanicKind) (site : Site) :
    on k kind site (.bool true) = .ok { k with pc := k.pc + 1 } := by rfl

theorem true_site_irrelevant (k : Core) (kind : DivPanicKind) (a b : Site) :
    on k kind a (.bool true) = on k kind b (.bool true) := by rfl

theorem false_state_irrelevant (a b : Core) (kind : DivPanicKind) (site : Site) :
    on a kind site (.bool false) = on b kind site (.bool false) := by rfl

theorem step_true (k : Core) (condition : Nat) (kind : DivPanicKind) (site : Site)
    (value : getV k condition = .ok (.bool true)) :
    step k condition kind site = .ok (next k) := by
  simp only [step, value, ok_bind]
  rfl

theorem step_false (k : Core) (condition : Nat) (kind : DivPanicKind) (site : Site)
    (value : getV k condition = .ok (.bool false)) :
    step k condition kind site =
      .stop (.globalDivPanic ⟨kind, none, site.entry, site.global, 0⟩) := by
  simp only [step, value, ok_bind]
  rfl

theorem false_preserves_identity (k : Core) (kind : DivPanicKind) (site : Site)
    (outcome : GlobalDivPanic) (h : on k kind site (.bool false) = .stop (.globalDivPanic outcome)) :
    outcome.kind = kind ∧ outcome.operands = none ∧ outcome.entry = site.entry ∧
    outcome.global = site.global ∧ outcome.offset = 0 := by
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem failure_is_bad (kind : DivPanicKind) (site : Site) :
    Bad (.globalDivPanic (failure kind site)) := by trivial

theorem step_false_is_bad (k : Core) (condition : Nat) (kind : DivPanicKind) (site : Site)
    (value : getV k condition = .ok (.bool false)) :
    ∃ output, step k condition kind site = .stop output ∧ Bad output := by
  exact ⟨.globalDivPanic (failure kind site), step_false k condition kind site value,
    failure_is_bad kind site⟩

theorem div_message (k : Core) : assertMessage k .divByZero = .ok (message .divByZero) := by rfl
theorem rem_message (k : Core) : assertMessage k .remByZero = .ok (message .remByZero) := by rfl

end SemR.SitedDivPanic
