-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- SOUNDNESS OF THE PREDICATE LATTICE (G5).
--
-- STATUS: machine-checked as part of the `trust_ir-semantics` `lake build`;
-- AxiomAudit.lean enforces the admitted axiom budget for the public results.
--
-- What is proved:
--   * `impliesFuel_sound`      — implies a b = true → ∀ v, ⟦a⟧ v → ⟦b⟧ v
--   * `implies_sound`          — the same at the shipped fuel budget
--   * `join_upper_bound_left`  — ∀ v, ⟦a⟧ v → ⟦join a b⟧ v
--   * `join_upper_bound_right` — ∀ v, ⟦b⟧ v → ⟦join a b⟧ v
--   * `denote_Top`             — ⟦top⟧ v, for every v
--   * `top_certifies_only_trivia` — implies top b = true → b holds everywhere
--   * `index_never_implies_member` — THE miscompile class, as a theorem
--
-- Everything is proved for an ARBITRARY interpretation `m` of the non-scalar
-- constants (floats, bytes, aggregates), universally quantified: the decision
-- procedures never look inside one, and the theorems may not depend on how
-- they are read.

import TrustIr.Pred

namespace TrustIr

variable {m : Constant → Value → Prop}

/-! ## Constant keys determine constants -/

/-- Two constants with the same key ARE the same constant. This is what lets
    key-level membership tests (`membersContainKey`, `membersSubset`) carry
    denotational weight: finding *a* constant with the right key finds *the*
    constant. -/
theorem constantKey_inj {c d : Constant} {k : Nat × Int}
    (hc : constantKey c = some k) (hd : constantKey d = some k) : c = d := by
  have hcd : constantKey c = constantKey d := hc.trans hd.symm
  cases c <;> cases d <;> simp [constantKey] at hc hd hcd ⊢
  · assumption
  · rename_i b₁ b₂
    cases b₁ <;> cases b₂ <;> simp_all

/-- An integer key names an integer constant. -/
theorem constantKey_int {c : Constant} {n : Int} (h : constantKey c = some (0, n)) :
    c = .int n :=
  constantKey_inj h (by simp [constantKey])

/-- The denotation of an integer constant, spelled out. -/
theorem constDenote_int (n : Int) (w : Nat) : constDenote m (.int n) (.int w n) :=
  ⟨w, rfl⟩

/-! ## Extensions -/

theorem membersContainKey_mem {items : List Constant} {k : Nat × Int}
    (h : membersContainKey items k = true) : ∃ c ∈ items, constantKey c = some k := by
  obtain ⟨c, hc, hk⟩ := List.any_eq_true.mp h
  exact ⟨c, hc, by simpa using hk⟩

/-- `membersSubset` is sound: everything the source extension admits, the
    target extension admits. -/
theorem membersSubset_sound {x y : List Constant} (h : membersSubset x y = true)
    {v : Value} (hv : ∃ c ∈ x, constDenote m c v) : ∃ d ∈ y, constDenote m d v := by
  obtain ⟨c, hcx, hcv⟩ := hv
  simp only [membersSubset, Bool.and_eq_true] at h
  have hall := h.2
  have hc := List.all_eq_true.mp hall c hcx
  cases hkey : constantKey c with
  | none => rw [hkey] at hc; exact absurd hc (by simp)
  | some k =>
    rw [hkey] at hc
    obtain ⟨d, hdy, hdk⟩ := membersContainKey_mem hc
    exact ⟨d, hdy, (constantKey_inj hdk hkey) ▸ hcv⟩

theorem mem_intRangeFrom {lo n : Int} {count : Nat} (h1 : lo ≤ n)
    (h2 : n < lo + (count : Int)) : n ∈ intRangeFrom lo count := by
  induction count generalizing lo n with
  | zero => omega
  | succ count ih =>
    simp only [intRangeFrom, List.mem_cons]
    by_cases heq : n = lo
    · exact Or.inl heq
    · exact Or.inr (ih (by omega) (by omega))

theorem mem_intRangeList {lo hi n : Int} (h1 : lo ≤ n) (h2 : n ≤ hi) :
    n ∈ intRangeList lo hi := by
  unfold intRangeList
  rw [if_neg (by omega : ¬ lo > hi)]
  apply mem_intRangeFrom h1
  have hnonneg : (0 : Int) ≤ hi - lo := by omega
  first
  | rw [Int.ofNat_add, Int.toNat_of_nonneg hnonneg]; omega
  | rw [Int.natCast_add, Int.toNat_of_nonneg hnonneg]; omega

/-- `membersContainInterval` is sound: every integer of the interval really is
    in the extension. -/
theorem membersContainInterval_sound {items : List Constant} {lo hi n : Int} {w : Nat}
    (h : membersContainInterval items lo hi = true) (h1 : lo ≤ n) (h2 : n ≤ hi) :
    ∃ c ∈ items, constDenote m c (.int w n) := by
  unfold membersContainInterval at h
  rw [if_neg (by omega : ¬ (lo > hi))] at h
  simp only [Bool.and_eq_true] at h
  have hall := h.2
  have hmem := List.all_eq_true.mp hall n (mem_intRangeList h1 h2)
  obtain ⟨c, hc, hkey⟩ := membersContainKey_mem hmem
  exact ⟨c, hc, (constantKey_int hkey) ▸ constDenote_int n w⟩

/-! ## Integer bounds of an extension -/

theorem intBoundsAux_sound : ∀ (n : Int) (l : List Constant) (lo hi : Int),
    intBoundsAux n l = some (lo, hi) →
      (lo ≤ n ∧ n ≤ hi) ∧ ∀ c ∈ l, ∃ k, constInt c = some k ∧ lo ≤ k ∧ k ≤ hi := by
  intro n l
  induction l generalizing n with
  | nil =>
    intro lo hi h
    simp only [intBoundsAux, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨by omega, by omega⟩, by simp⟩
  | cons c rest ih =>
    intro lo hi h
    cases hk : constInt c with
    | none => simp [intBoundsAux, hk] at h
    | some k =>
      cases hrest : intBoundsAux k rest with
      | none => simp [intBoundsAux, hk, hrest] at h
      | some p =>
        obtain ⟨lo', hi'⟩ := p
        simp only [intBoundsAux, hk, hrest, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hlo, hhi⟩ := h
        subst lo
        subst hi
        obtain ⟨⟨hlo', hhi'⟩, hrestBounds⟩ := ih k lo' hi' hrest
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd'
        · exact ⟨k, hk, by omega, by omega⟩
        · obtain ⟨kd, hkd, hlo, hhi⟩ := hrestBounds d hd'
          exact ⟨kd, hkd, by omega, by omega⟩

theorem intBoundsOf_sound {l : List Constant} {lo hi : Int} (h : intBoundsOf l = some (lo, hi)) :
    ∀ c ∈ l, ∃ k, constInt c = some k ∧ lo ≤ k ∧ k ≤ hi := by
  cases l with
  | nil => exact absurd h (by simp [intBoundsOf])
  | cons c rest =>
    simp only [intBoundsOf] at h
    cases hk : constInt c with
    | none => rw [hk] at h; exact absurd h (by simp)
    | some n =>
      rw [hk] at h
      obtain ⟨⟨hlo, hhi⟩, hrest⟩ := intBoundsAux_sound n rest lo hi h
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd'
      · exact ⟨n, hk, hlo, hhi⟩
      · exact hrest d hd'

/-- An integer constant's denotation pins the value. -/
theorem constInt_denote {c : Constant} {k : Int} (hk : constInt c = some k)
    {v : Value} (hv : constDenote m c v) : ∃ w, v = .int w k := by
  cases c <;> simp only [constInt] at hk <;> try contradiction
  case int n => cases hk; exact hv

theorem membersIntBounds_sound {items : List Constant} {lo hi : Int}
    (h : membersIntBounds items = some (lo, hi)) {v : Value}
    (hv : ∃ c ∈ items, constDenote m c v) : ∃ w n, v = .int w n ∧ lo ≤ n ∧ n ≤ hi := by
  obtain ⟨c, hc, hcv⟩ := hv
  unfold membersIntBounds at h
  split at h
  · obtain ⟨k, hk, hlo, hhi⟩ := intBoundsOf_sound h c hc
    obtain ⟨w, rfl⟩ := constInt_denote hk hcv
    exact ⟨w, k, rfl, hlo, hhi⟩
  · exact absurd h (by simp)

/-! ## Universes -/

theorem Universe.integerBounds_sound {u : Universe} {lo hi : Int}
    (h : u.integerBounds = some (lo, hi)) {v : Value} (hv : Universe.contains m u v) :
    ∃ w n, v = .int w n ∧ lo ≤ n ∧ n ≤ hi := by
  cases u with
  | IntRange ulo uhi =>
    simp only [Universe.integerBounds] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hv
    · exact absurd h (by simp)
  | Members items =>
    simp only [Universe.integerBounds] at h
    exact membersIntBounds_sound h hv

/-- Membership is monotone in the universe: `U ⊆ V ⇒ (self ∈ U) ⇒ (self ∈ V)`.
    This is the ONLY monotonicity the convention rule uses on the `Member`
    side — and note it never crosses over to the `Index` side. -/
theorem Universe.isSubsetOf_sound {ua ub : Universe} (h : ua.isSubsetOf ub = true)
    {v : Value} (hv : Universe.contains m ua v) : Universe.contains m ub v := by
  cases ua with
  | IntRange lo hi =>
    obtain ⟨w, n, rfl, hn1, hn2⟩ := hv
    cases ub with
    | IntRange olo ohi =>
      simp only [Universe.isSubsetOf, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨w, n, rfl, by omega, by omega⟩
    | Members items =>
      simp only [Universe.isSubsetOf, Bool.and_eq_true, decide_eq_true_eq] at h
      exact membersContainInterval_sound h.2 hn1 hn2
  | Members items =>
    obtain ⟨c, hc, hcv⟩ := hv
    cases ub with
    | IntRange lo hi =>
      simp only [Universe.isSubsetOf, Bool.and_eq_true, decide_eq_true_eq] at h
      have hall := List.all_eq_true.mp h.2 c hc
      cases hk : constInt c with
      | none => rw [hk] at hall; exact absurd hall (by simp)
      | some k =>
        rw [hk] at hall
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
        obtain ⟨w, rfl⟩ := constInt_denote hk hcv
        exact ⟨w, k, rfl, hall.1, hall.2⟩
    | Members target =>
      simp only [Universe.isSubsetOf] at h
      exact membersSubset_sound h ⟨c, hc, hcv⟩

/-! ## Bound arithmetic -/

theorem intersectBounds_sound : ∀ (bs : List (Int × Int)) (lo hi n : Int),
    intersectBounds bs = some (lo, hi) → (∀ b ∈ bs, b.1 ≤ n ∧ n ≤ b.2) → lo ≤ n ∧ n ≤ hi := by
  intro bs
  induction bs with
  | nil => intro lo hi n h; exact absurd h (by simp [intersectBounds])
  | cons b rest ih =>
    obtain ⟨blo, bhi⟩ := b
    intro lo hi n h hall
    cases rest with
    | nil =>
      simp only [intersectBounds, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hall (blo, bhi) ((trustIrListMemConsSelf _ _))
    | cons c rest' =>
      simp only [intersectBounds] at h
      cases hr : intersectBounds (c :: rest') with
      | none => rw [hr] at h; exact absurd h (by simp)
      | some p =>
        obtain ⟨lo', hi'⟩ := p
        rw [hr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hb := hall (blo, bhi) ((trustIrListMemConsSelf _ _))
        have hrest := ih lo' hi' n hr (fun x hx => hall x (List.mem_cons_of_mem _ hx))
        exact ⟨by omega, by omega⟩

theorem hullBounds_sound : ∀ (bs : List (Int × Int)) (lo hi n : Int),
    hullBounds bs = some (lo, hi) → (∃ b ∈ bs, b.1 ≤ n ∧ n ≤ b.2) → lo ≤ n ∧ n ≤ hi := by
  intro bs
  induction bs with
  | nil => intro lo hi n h; exact absurd h (by simp [hullBounds])
  | cons b rest ih =>
    obtain ⟨blo, bhi⟩ := b
    intro lo hi n h hex
    cases rest with
    | nil =>
      simp only [hullBounds, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨x, hx, hx1, hx2⟩ := hex
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨hx1, hx2⟩
      · exact absurd hx' (by simp)
    | cons c rest' =>
      simp only [hullBounds] at h
      cases hr : hullBounds (c :: rest') with
      | none => rw [hr] at h; exact absurd h (by simp)
      | some p =>
        obtain ⟨lo', hi'⟩ := p
        rw [hr] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨x, hx, hx1, hx2⟩ := hex
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨by omega, by omega⟩
        · have := ih lo' hi' n hr ⟨x, hx', hx1, hx2⟩
          exact ⟨by omega, by omega⟩

theorem filterSomeBounds_mem_inv (f : Pred → Option (Int × Int)) :
    ∀ (cs : List Pred) (b : Int × Int),
      b ∈ filterSomeBounds (cs.map f) → ∃ p ∈ cs, f p = some b := by
  intro cs
  induction cs with
  | nil => intro b hb; exact absurd hb (by simp [filterSomeBounds])
  | cons p rest ih =>
    intro b hb
    simp only [List.map_cons] at hb
    cases hf : f p with
    | none =>
      rw [hf] at hb
      simp only [filterSomeBounds] at hb
      obtain ⟨q, hq, hqf⟩ := ih b hb
      exact ⟨q, List.mem_cons_of_mem _ hq, hqf⟩
    | some x =>
      rw [hf] at hb
      simp only [filterSomeBounds, List.mem_cons] at hb
      rcases hb with rfl | hb'
      · exact ⟨p, (trustIrListMemConsSelf _ _), hf⟩
      · obtain ⟨q, hq, hqf⟩ := ih b hb'
        exact ⟨q, List.mem_cons_of_mem _ hq, hqf⟩

theorem filterSomeBounds_nonempty (f : Pred → Option (Int × Int)) {cs : List Pred}
    {lo hi : Int} (h : intersectBounds (filterSomeBounds (cs.map f)) = some (lo, hi)) :
    ∃ p ∈ cs, ∃ b, f p = some b := by
  cases hl : filterSomeBounds (cs.map f) with
  | nil => rw [hl] at h; exact absurd h (by simp [intersectBounds])
  | cons b rest =>
    have : b ∈ filterSomeBounds (cs.map f) := by rw [hl]; exact (trustIrListMemConsSelf _ _)
    obtain ⟨p, hp, hpf⟩ := filterSomeBounds_mem_inv f cs b this
    exact ⟨p, hp, b, hpf⟩

theorem sequenceBounds_mem (f : Pred → Option (Int × Int)) :
    ∀ (cs : List Pred) (bs : List (Int × Int)),
      sequenceBounds (cs.map f) = some bs → ∀ p ∈ cs, ∃ b ∈ bs, f p = some b := by
  intro cs
  induction cs with
  | nil => intro bs _ p hp; exact absurd hp (by simp)
  | cons p rest ih =>
    intro bs h q hq
    simp only [List.map_cons] at h
    cases hf : f p with
    | none => rw [hf] at h; exact absurd h (by simp [sequenceBounds])
    | some x =>
      rw [hf] at h
      first
      | simp only [sequenceBounds, Option.map_eq_some'] at h
      | simp only [sequenceBounds, Option.map_eq_some_iff] at h
      obtain ⟨bs', hbs', rfl⟩ := h
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact ⟨x, (trustIrListMemConsSelf _ _), hf⟩
      · obtain ⟨b, hb, hbf⟩ := ih bs' hbs' q hq'
        exact ⟨b, List.mem_cons_of_mem _ hb, hbf⟩

/-! ## Canonicalization preserves what an extension admits

    The join's finite-set arm returns the CANONICALIZED union, so the upper
    bound property needs: sorting and deduplicating by key never drops a
    value the input admitted. -/

theorem mem_insertByKey (x : Constant) : ∀ {l : List Constant} {c : Constant},
    c ∈ l → c ∈ insertByKey x l := by
  intro l
  induction l with
  | nil => intro c hc; exact absurd hc (by simp)
  | cons d rest ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · unfold insertByKey
      split
      · split
        · exact (trustIrListMemConsSelf _ _)
        · split
          · exact List.mem_cons_of_mem _ ((trustIrListMemConsSelf _ _))
          · exact (trustIrListMemConsSelf _ _)
      · exact List.mem_cons_of_mem _ ((trustIrListMemConsSelf _ _))
    · unfold insertByKey
      split
      · split
        · exact List.mem_cons_of_mem _ hc'
        · split
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc')
          · exact List.mem_cons_of_mem _ (ih hc')
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc')

theorem key_mem_insertByKey (x : Constant) : ∀ (l : List Constant),
    ∃ d ∈ insertByKey x l, constantKey d = constantKey x := by
  intro l
  induction l with
  | nil => exact ⟨x, by simp [insertByKey], rfl⟩
  | cons d rest ih =>
    cases hkx : constantKey x with
    | none =>
      refine ⟨x, ?_, hkx⟩
      simp only [insertByKey, hkx]
      exact (trustIrListMemConsSelf _ _)
    | some kx =>
      cases hkd : constantKey d with
      | none =>
        refine ⟨x, ?_, hkx⟩
        simp only [insertByKey, hkx, hkd]
        exact (trustIrListMemConsSelf _ _)
      | some kd =>
        simp only [insertByKey, hkx, hkd]
        by_cases hEq : kx = kd
        · rw [if_pos (by simp [hEq])]
          exact ⟨d, (trustIrListMemConsSelf _ _), by simpa [hkd, hkx] using congrArg some hEq.symm⟩
        · rw [if_neg (by simp [hEq])]
          by_cases hlt : keyLt kx kd = true
          · rw [if_pos hlt]; exact ⟨x, (trustIrListMemConsSelf _ _), hkx⟩
          · rw [if_neg hlt]
            obtain ⟨e, he, hek⟩ := ih
            exact ⟨e, List.mem_cons_of_mem _ he, hek.trans hkx⟩

theorem mem_foldr_insertByKey : ∀ (l acc : List Constant) (c : Constant), c ∈ l →
    ∃ d ∈ l.foldr insertByKey acc, constantKey d = constantKey c := by
  intro l
  induction l with
  | nil => intro acc c hc; exact absurd hc (by simp)
  | cons x rest ih =>
    intro acc c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · rw [List.foldr_cons]
      exact key_mem_insertByKey c _
    · obtain ⟨d, hd, hdk⟩ := ih acc c hc'
      rw [List.foldr_cons]
      exact ⟨d, mem_insertByKey x hd, hdk⟩

theorem mem_append_left {xs ys : List Constant} {c : Constant} (hc : c ∈ xs) :
    c ∈ xs ++ ys := by
  induction xs with
  | nil => exact absurd hc (by simp)
  | cons x rest ih =>
    change c ∈ x :: (rest ++ ys)
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact (trustIrListMemConsSelf _ _)
    · exact List.mem_cons_of_mem _ (ih hc')

theorem mem_append_right {xs ys : List Constant} {c : Constant} (hc : c ∈ ys) :
    c ∈ xs ++ ys := by
  induction xs with
  | nil => exact hc
  | cons x rest ih =>
    change c ∈ x :: (rest ++ ys)
    exact List.mem_cons_of_mem _ ih

/-- Canonicalizing an extension keeps every value it admitted. -/
theorem canonicalizeMembers_preserves {items out : List Constant}
    (h : canonicalizeMembers items = some out) {c : Constant} (hc : c ∈ items)
    {v : Value} (hv : constDenote m c v) : ∃ d ∈ out, constDenote m d v := by
  unfold canonicalizeMembers at h
  split at h
  next hall =>
    simp only at h
    split at h
    · exact absurd h (by simp)
    · simp only [Option.some.injEq] at h
      subst h
      obtain ⟨d, hd, hdk⟩ := mem_foldr_insertByKey items [] c hc
      have hsome : (constantKey c).isSome = true := List.all_eq_true.mp hall c hc
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hsome
      exact ⟨d, hd, (constantKey_inj (hdk.trans hk) hk) ▸ hv⟩
  next _ => exact absurd h (by simp)

/-! ## Connective denotations -/

theorem denoteAll_iff (U : UnivTable) (m : Constant → Value → Prop) (cs : List Pred) (v : Value) :
    Pred.denoteAll U m cs v ↔ ∀ p ∈ cs, Pred.denote U m p v := by
  induction cs with
  | nil => rw [Pred.denoteAll.eq_1]; simp
  | cons p rest ih =>
    rw [Pred.denoteAll.eq_2]
    constructor
    · rintro ⟨hp, hrest⟩ q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact hp
      · exact ih.mp hrest q hq'
    · intro h
      exact ⟨h p ((trustIrListMemConsSelf _ _)),
             ih.mpr fun q hq => h q (List.mem_cons_of_mem _ hq)⟩

theorem denoteAny_iff (U : UnivTable) (m : Constant → Value → Prop) (cs : List Pred) (v : Value) :
    Pred.denoteAny U m cs v ↔ ∃ p ∈ cs, Pred.denote U m p v := by
  induction cs with
  | nil => rw [Pred.denoteAny.eq_1]; simp
  | cons p rest ih =>
    rw [Pred.denoteAny.eq_2]
    constructor
    · rintro (hp | hrest)
      · exact ⟨p, (trustIrListMemConsSelf _ _), hp⟩
      · obtain ⟨q, hq, hqv⟩ := ih.mp hrest
        exact ⟨q, List.mem_cons_of_mem _ hq, hqv⟩
    · rintro ⟨q, hq, hqv⟩
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact Or.inl hqv
      · exact Or.inr (ih.mpr ⟨q, hq', hqv⟩)

/-! ## Structural equality is denotational equality -/

theorem constBeq_eq {c d : Constant} (h : constBeq c d = true) : c = d := by
  unfold constBeq at h
  cases hc : constantKey c with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some k1 =>
    cases hd : constantKey d with
    | none => rw [hc, hd] at h; exact absurd h (by simp)
    | some k2 =>
      rw [hc, hd] at h
      have : k1 = k2 := by simpa using h
      exact constantKey_inj hc (this ▸ hd)

theorem constListBeq_eq : ∀ {x y : List Constant}, constListBeq x y = true → x = y := by
  intro x
  induction x with
  | nil => intro y h; cases y with
    | nil => rfl
    | cons _ _ => exact absurd h (by simp [constListBeq])
  | cons c cs ih =>
    intro y h
    cases y with
    | nil => exact absurd h (by simp [constListBeq])
    | cons d ds =>
      simp only [constListBeq, Bool.and_eq_true] at h
      have hcd := constBeq_eq h.1
      have hcs := ih h.2
      subst d
      subst ds
      rfl

mutual

private theorem univId_eq_of_index_eq {u v : UnivId} (h : u.index = v.index) : u = v := by
  cases u
  cases v
  simp_all

/-- `Pred.beq` certifies only genuine equality (on every extension the
    validator admits — see the fidelity note in TrustIr/Pred.lean). -/
theorem Pred.beq_eq : ∀ {a b : Pred}, Pred.beq a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;>
    simp only [Pred.beq, Bool.and_eq_true, decide_eq_true_eq] at h <;>
    first
      | rfl
      | (obtain ⟨hu, hs⟩ := h; have huv := univId_eq_of_index_eq hu;
         cases huv; cases hs; rfl)
      | (solve | simp_all [univId_eq_of_index_eq])
      | (rename_i x y; exact congrArg Pred.FiniteSet (constListBeq_eq h))
      | (rename_i x y; exact congrArg Pred.Conj (Pred.listBeq_eq h))
      | (rename_i x y; exact congrArg Pred.Disj (Pred.listBeq_eq h))
      | exact absurd h (by simp)

/-- Pointwise version, for the connective children. -/
theorem Pred.listBeq_eq : ∀ {as bs : List Pred}, Pred.listBeq as bs = true → as = bs := by
  intro as bs h
  cases as with
  | nil => cases bs with
    | nil => rfl
    | cons _ _ => exact absurd h (by simp [Pred.listBeq])
  | cons p ps =>
    cases bs with
    | nil => exact absurd h (by simp [Pred.listBeq])
    | cons q qs =>
      simp only [Pred.listBeq, Bool.and_eq_true] at h
      have hpq := Pred.beq_eq h.1
      have hps := Pred.listBeq_eq h.2
      subst q
      subst qs
      rfl

end

/-- Universe content equality is genuine equality on every extension the
    validator admits. -/
theorem Universe.beq_eq {a b : Universe} (h : Universe.beq a b = true) : a = b := by
  cases a with
  | IntRange alo ahi =>
    cases b with
    | IntRange blo bhi =>
      simp only [Universe.beq, Bool.and_eq_true] at h
      have hlo : alo = blo := by simpa using h.1
      have hhi : ahi = bhi := by simpa using h.2
      subst blo
      subst bhi
      rfl
    | Members _ => exact absurd h (by simp [Universe.beq])
  | Members x =>
    cases b with
    | IntRange _ _ => exact absurd h (by simp [Universe.beq])
    | Members y => exact congrArg Universe.Members (constListBeq_eq (by simpa [Universe.beq] using h))

/-! ## `Top` is the weakest fact -/

/-- `⟦top⟧ v` for EVERY `v`. This is the formal content of "a MISSING
    predicate is `Top`": a dropped fact constrains nothing at all. -/
@[simp] theorem denote_Top (U : UnivTable) (m : Constant → Value → Prop) (v : Value) :
    Pred.denote U m .Top v := trivial

/-- `⟦bottom⟧` is empty. -/
@[simp] theorem denote_Bottom (U : UnivTable) (m : Constant → Value → Prop) (v : Value) :
    ¬ Pred.denote U m .Bottom v := id

/-! ## The interval-bound helper is sound -/

/-- `intervalBoundFuel p = some (lo, hi)` really does mean `p` entails
    `lo ≤ self ≤ hi` — and, in particular, that `self` is an INTEGER. -/
theorem intervalBoundFuel_sound (U : UnivTable) (m : Constant → Value → Prop) :
    ∀ (fuel : Nat) (p : Pred) (lo hi : Int),
      Pred.intervalBoundFuel U fuel p = some (lo, hi) →
        ∀ v : Value, Pred.denote U m p v → ∃ w n, v = .int w n ∧ lo ≤ n ∧ n ≤ hi := by
  intro fuel
  induction fuel with
  | zero => intro p lo hi h; exact absurd h (by simp [Pred.intervalBoundFuel])
  | succ fuel ih =>
    intro p lo hi h v hv
    cases p with
    | Interval a b =>
      simp only [Pred.intervalBoundFuel] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [Pred.denote.eq_1] at hv
        exact hv
      · exact absurd h (by simp)
    | FiniteSet items =>
      simp only [Pred.intervalBoundFuel] at h
      rw [Pred.denote.eq_2] at hv
      exact membersIntBounds_sound h hv
    | InUniverse u s =>
      cases s with
      | Member =>
        simp only [Pred.intervalBoundFuel] at h
        cases hu : UnivTable.get? U u with
        | none => rw [hu] at h; exact absurd h (by simp)
        | some univ =>
          rw [hu] at h
          simp only at h
          simp only [Pred.denote.eq_3, hu] at hv
          exact Universe.integerBounds_sound h hv
      | Index =>
        simp only [Pred.intervalBoundFuel] at h
        cases hu : UnivTable.get? U u with
        | none => rw [hu] at h; exact absurd h (by simp)
        | some univ =>
          rw [hu] at h
          simp only at h
          simp only [Pred.denote.eq_3, hu] at hv
          cases hc : univ.cardinality with
          | none => rw [hc] at h; exact absurd h (by simp)
          | some k =>
            rw [hc] at h
            simp only at h
            simp only [hc] at hv
            obtain ⟨w, n, rfl, hn0, hnk⟩ := hv
            split at h
            next hk => exact absurd h (by simp [hk])
            next hk =>
              have hp : some (0, (k : Int) - 1) = some (lo, hi) := by simpa [hk] using h
              have hp' : (0, (k : Int) - 1) = (lo, hi) := Option.some.inj hp
              have hlo := congrArg Prod.fst hp'
              have hhi := congrArg Prod.snd hp'
              exact ⟨w, n, rfl, by omega, by omega⟩
    | NonZero => exact absurd h (by simp [Pred.intervalBoundFuel])
    | NonNull => exact absurd h (by simp [Pred.intervalBoundFuel])
    | Top => exact absurd h (by simp [Pred.intervalBoundFuel])
    | Bottom =>
      rw [Pred.denote.eq_9] at hv
      exact False.elim hv
    | Conj cs =>
      -- Every conjunct that HAS a bound constrains `v`; the accumulated
      -- intersection therefore does too.
      simp only [Pred.intervalBoundFuel] at h
      rw [Pred.denote.eq_6] at hv
      cases hi' : intersectBounds (filterSomeBounds
          (cs.map (fun q => Pred.intervalBoundFuel U fuel q))) with
      | none => rw [hi'] at h; exact absurd h (by simp)
      | some p' =>
        obtain ⟨lo', hi''⟩ := p'
        rw [hi'] at h
        simp only at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hall := (denoteAll_iff U m cs v).mp hv
          -- Some conjunct has a bound, so `v` is an integer.
          obtain ⟨q, hq, b, hqb⟩ :=
            filterSomeBounds_nonempty (fun q => Pred.intervalBoundFuel U fuel q) hi'
          obtain ⟨w, n, rfl, _, _⟩ := ih q b.1 b.2 (by simpa using hqb) v (hall q hq)
          refine ⟨w, n, rfl, ?_, ?_⟩ <;>
            · have hbounds : ∀ x ∈ filterSomeBounds
                  (cs.map (fun q => Pred.intervalBoundFuel U fuel q)), x.1 ≤ n ∧ n ≤ x.2 := by
                intro x hx
                obtain ⟨r, hr, hrx⟩ :=
                  filterSomeBounds_mem_inv (fun q => Pred.intervalBoundFuel U fuel q) cs x hx
                obtain ⟨w', n', hval, h1, h2⟩ :=
                  ih r x.1 x.2 (by simpa using hrx) (.int w n) (hall r hr)
                cases hval
                exact ⟨h1, h2⟩
              have := intersectBounds_sound _ lo' hi'' n hi' hbounds
              omega
        · exact absurd h (by simp)
    | Disj cs =>
      -- The hull is taken only when EVERY arm has a bound, and `v` satisfies
      -- at least one arm.
      simp only [Pred.intervalBoundFuel] at h
      rw [Pred.denote.eq_7] at hv
      cases hs : sequenceBounds (cs.map (fun q => Pred.intervalBoundFuel U fuel q)) with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some bs =>
        rw [hs] at h
        obtain ⟨q, hq, hqv⟩ := (denoteAny_iff U m cs v).mp hv
        obtain ⟨b, hb, hqb⟩ :=
          sequenceBounds_mem (fun q => Pred.intervalBoundFuel U fuel q) cs bs hs q hq
        obtain ⟨w, n, rfl, h1, h2⟩ := ih q b.1 b.2 (by simpa using hqb) v hqv
        have := hullBounds_sound bs lo hi n h ⟨b, hb, h1, h2⟩
        exact ⟨w, n, rfl, this.1, this.2⟩

/-! ## THE THEOREM

`implies` never certifies an implication that does not hold. Everything the
consumption rule does rests on exactly this: if it were false, a convention
mismatch would pass validation silently, which is the miscompile class the
typed value model exists to close. -/

-- Name the existing Boolean conditions outside the proof context, so their
-- generated matchers do not capture branch-dependent proof hypotheses.
private abbrev impliesLeftConj (U : UnivTable) (fuel : Nat) (a b : Pred) : Bool :=
  match a with
  | .Conj cs => cs.any (fun c => Pred.impliesFuel U fuel c b)
  | _ => false

private abbrev impliesRightDisj (U : UnivTable) (fuel : Nat) (a b : Pred) : Bool :=
  match b with
  | .Disj cs => cs.any (fun c => Pred.impliesFuel U fuel a c)
  | _ => false

theorem impliesFuel_sound (U : UnivTable) (m : Constant → Value → Prop) :
    ∀ (fuel : Nat) (a b : Pred), Pred.impliesFuel U fuel a b = true →
      ∀ v : Value, Pred.denote U m a v → Pred.denote U m b v := by
  intro fuel
  induction fuel with
  | zero => intro a b h; change false = true at h; cases h
  | succ fuel ih =>
    intro srcPred dstPred h v hav
    unfold Pred.impliesFuel at h
    -- The outer `match a, b` decides four trivial arms before anything else.
    split at h
    -- a = Bottom: ⟦Bottom⟧ is empty, so the hypothesis is absurd.
    case _ =>
      rw [Pred.denote.eq_9] at hav
      exact False.elim hav
    -- b = Bottom: `implies` answered `false`.
    case _ => exact absurd h (by simp)
    -- b = Top: everything denotes Top.
    case _ => rw [Pred.denote.eq_8]; trivial
    -- a = Top: `implies` answered `false`.
    case _ => exact absurd h (by simp)
    case _ =>
      -- The general case, in `impliesFuel`'s own order.
      -- Split the semantic condition itself, without asking `split` to
      -- choose a reducible matcher inside the Boolean equality implementation.
      by_cases heq : Pred.beq srcPred dstPred = true
      · exact (Pred.beq_eq heq) ▸ hav
      · rw [if_neg heq] at h
        by_cases hconj : impliesLeftConj U fuel srcPred dstPred = true
        -- 2. Conjunction on the LEFT: some conjunct already entails the target.
        ·
          cases srcPred with
          | Conj cs =>
            rw [Pred.denote.eq_6] at hav
            obtain ⟨c, hc, hcb⟩ := List.any_eq_true.mp (by simpa only [impliesLeftConj] using hconj)
            exact ih c dstPred hcb v ((denoteAll_iff U m cs v).mp hav c hc)
          | _ => exact absurd hconj (by simp [impliesLeftConj])
        · erw [if_neg hconj] at h
          by_cases hdisj : impliesRightDisj U fuel srcPred dstPred = true
          -- 3. Disjunction on the RIGHT: one arm suffices.
          ·
            cases dstPred with
            | Disj cs =>
              rw [Pred.denote.eq_7]
              obtain ⟨c, hc, hac⟩ := List.any_eq_true.mp (by simpa only [impliesRightDisj] using hdisj)
              exact (denoteAny_iff U m cs v).mpr ⟨c, hc, ih srcPred c hac v hav⟩
            | _ => exact absurd hdisj (by simp [impliesRightDisj])
          · erw [if_neg hdisj] at h
            split at h
            -- 4. Conjunction on the RIGHT: every conjunct is entailed.
            next =>
              rw [Pred.denote.eq_6]
              refine (denoteAll_iff U m _ v).mpr fun c hc => ?_
              exact ih srcPred c (List.all_eq_true.mp h c hc) v hav
            next =>
              split at h
              -- 5. Disjunction on the LEFT: every arm entails the target.
              next =>
                rw [Pred.denote.eq_7] at hav
                obtain ⟨c, hc, hcv⟩ := (denoteAny_iff U m _ v).mp hav
                exact ih c dstPred (List.all_eq_true.mp h c hc) v hcv
              next =>
                -- 6. The shape-directed arms, on `b`.
                cases dstPred with
                -- 6a. THE CONVENTION RULE.
                | InUniverse ub sb =>
                  simp only at h
                  cases srcPred with
                  | InUniverse ua sa =>
                    simp only at h
                    split at h
                    -- Different SPACE is never an implication — the miscompile class.
                    · exact absurd h (by simp)
                    · rename_i hsp
                      have hspace : sa = sb := by
                        by_cases heq : sa = sb
                        · exact heq
                        · exact False.elim (hsp heq)
                      subst sb
                      cases hua : UnivTable.get? U ua with
                      | none => rw [hua] at h; exact absurd h (by simp)
                      | some ua' =>
                        cases hub : UnivTable.get? U ub with
                        | none => rw [hua, hub] at h; exact absurd h (by simp)
                        | some ub' =>
                          rw [hua, hub] at h
                          simp only at h
                          simp only [Pred.denote.eq_3, hua] at hav
                          simp only [Pred.denote.eq_3, hub]
                          cases sa with
                          | Member => exact Universe.isSubsetOf_sound h hav
                          | Index =>
                            have hu : ua' = ub' := Universe.beq_eq h
                            cases hu
                            exact hav
                  | _ => exact absurd h (by simp)
                -- 6b. Numeric containment in an interval.
                | Interval lo hi =>
                  simp only at h
                  cases hb : Pred.intervalBoundFuel U fuel srcPred with
                  | none => rw [hb] at h; exact absurd h (by simp)
                  | some p =>
                    obtain ⟨alo, ahi⟩ := p
                    rw [hb] at h
                    simp only at h
                    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
                    obtain ⟨w, n, rfl, h1, h2⟩ :=
                      intervalBoundFuel_sound U m fuel srcPred alo ahi hb v hav
                    rw [Pred.denote.eq_1]
                    exact ⟨w, n, rfl, by omega, by omega⟩
                -- 6c. Containment in a finite set.
                | FiniteSet target =>
                  simp only at h
                  rw [Pred.denote.eq_2]
                  cases srcPred with
                  | FiniteSet src =>
                    simp only at h
                    rw [Pred.denote.eq_2] at hav
                    exact membersSubset_sound h hav
                  | Interval lo hi =>
                    simp only at h
                    rw [Pred.denote.eq_1] at hav
                    obtain ⟨w, n, rfl, h1, h2⟩ := hav
                    exact membersContainInterval_sound h h1 h2
                  | InUniverse u s =>
                    simp only at h
                    cases hu : UnivTable.get? U u with
                    | none => rw [hu] at h; exact absurd h (by simp)
                    | some univ =>
                      rw [hu] at h
                      simp only at h
                      simp only [Pred.denote.eq_3, hu] at hav
                      cases s with
                      | Member =>
                        cases univ with
                        | Members src => exact membersSubset_sound h hav
                        | IntRange lo hi =>
                          obtain ⟨w, n, rfl, h1, h2⟩ := hav
                          exact membersContainInterval_sound h h1 h2
                      | Index =>
                        cases hc : univ.cardinality with
                        | none => rw [hc] at h; exact absurd h (by simp)
                        | some k =>
                          rw [hc] at h
                          simp only at h
                          simp only [hc] at hav
                          obtain ⟨w, n, rfl, hn0, hnk⟩ := hav
                          split at h
                          · exact absurd h (by simp)
                          · exact membersContainInterval_sound h hn0 (by omega)
                  | _ => exact absurd h (by simp)
                -- 6d. NonZero: 0 lies outside the entailed bounds.
                | NonZero =>
                  simp only at h
                  cases hb : Pred.intervalBoundFuel U fuel srcPred with
                  | none => rw [hb] at h; exact absurd h (by simp)
                  | some p =>
                    obtain ⟨lo, hi⟩ := p
                    rw [hb] at h
                    simp only at h
                    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
                    obtain ⟨w, n, rfl, h1, h2⟩ :=
                      intervalBoundFuel_sound U m fuel srcPred lo hi hb v hav
                    rw [Pred.denote.eq_4]
                    exact ⟨w, n, rfl, by rcases h with h | h <;> omega⟩
                -- 6e. NonNull / Top / Bottom / Conj / Disj on the right: `false`.
                | NonNull => exact absurd h (by simp)
                | Top => exact absurd h (by simp)
                | Bottom => exact absurd h (by simp)
                | Conj _ => exact absurd h (by simp)
                | Disj _ => exact absurd h (by simp)

/-- **Soundness of `implies` at the shipped budget.** The consumption rule
    (`check_refinement_consumption`) accepts a dataflow edge exactly when this
    answers `true`; the theorem says every acceptance is semantically
    justified. -/
theorem implies_sound (U : UnivTable) (m : Constant → Value → Prop) (a b : Pred)
    (h : Pred.implies U a b = true) :
    ∀ v : Value, Pred.denote U m a v → Pred.denote U m b v :=
  impliesFuel_sound U m (maxPredDepth + 1) a b h

/-- A `Top` carrier certifies only facts that hold of EVERYTHING. Contrapositive
    reading: any consumption site demanding a non-trivial fact REJECTS a
    dropped predicate instead of reinterpreting the carrier — which is the
    entire design. -/
theorem top_certifies_only_trivia (U : UnivTable) (m : Constant → Value → Prop) (b : Pred)
    (h : Pred.implies U .Top b = true) : ∀ v : Value, Pred.denote U m b v :=
  fun v => implies_sound U m .Top b h v (denote_Top U m v)

/-- **The miscompile class, as a theorem.** An INDEX into a universe never
    certifies MEMBERSHIP of it, and vice versa — over the same universe or any
    other, at any fuel. This is the implication whose silent acceptance shipped
    a union-key row off by one. -/
theorem index_never_implies_member (U : UnivTable) (fuel : Nat) (ua ub : UnivId) :
    Pred.impliesFuel U fuel (.InUniverse ua .Index) (.InUniverse ub .Member) = false ∧
    Pred.impliesFuel U fuel (.InUniverse ua .Member) (.InUniverse ub .Index) = false := by
  cases fuel with
  | zero => exact ⟨rfl, rfl⟩
  | succ n =>
    constructor <;> unfold Pred.impliesFuel <;> simp [Pred.beq]

/-! ## The join is an upper bound -/

theorem join_upper_bound_left (U : UnivTable) (m : Constant → Value → Prop)
    (srcPred dstPred : Pred) (v : Value) (hv : Pred.denote U m srcPred v) :
    Pred.denote U m (Pred.join U srcPred dstPred) v := by
  unfold Pred.join
  split
  next _ => exact hv
  next _ =>
    split
    -- srcPred entails dstPred: the join is dstPred.
    next hab => exact implies_sound U m srcPred dstPred hab v hv
    next _ =>
      split
      -- dstPred entails srcPred: the join is srcPred.
      next _ => exact hv
      next _ =>
        split
        -- Two intervals: the hull.
        case h_1 alo ahi blo bhi =>
          rw [Pred.denote.eq_1] at hv ⊢
          obtain ⟨w, n, rfl, h1, h2⟩ := hv
          exact ⟨w, n, rfl, by omega, by omega⟩
        -- Two finite sets: the union, when it canonicalizes.
        case h_2 x y =>
          split
          case h_1 items hcan =>
            rw [Pred.denote.eq_2] at hv ⊢
            obtain ⟨c, hc, hcv⟩ := hv
            exact canonicalizeMembers_preserves hcan (mem_append_left hc) hcv
          case h_2 _ => exact denote_Top U m v
        -- Incomparable universes: Top.
        case h_3 _ _ _ _ => exact denote_Top U m v
        -- Anything else: the explicit disjunction.
        case h_4 _ _ =>
          rw [Pred.denote.eq_7]
          exact (denoteAny_iff U m [srcPred, dstPred] v).mpr ⟨srcPred, by simp, hv⟩

theorem join_upper_bound_right (U : UnivTable) (m : Constant → Value → Prop)
    (srcPred dstPred : Pred) (v : Value) (hv : Pred.denote U m dstPred v) :
    Pred.denote U m (Pred.join U srcPred dstPred) v := by
  unfold Pred.join
  split
  -- a and b are structurally equal, so `a`'s denotation IS `b`'s.
  next heq => exact (Pred.beq_eq heq) ▸ hv
  next _ =>
    split
    next _ => exact hv
    next _ =>
      split
      next hba => exact implies_sound U m dstPred srcPred hba v hv
      next _ =>
        split
        case h_1 alo ahi blo bhi =>
          rw [Pred.denote.eq_1] at hv ⊢
          obtain ⟨w, n, rfl, h1, h2⟩ := hv
          exact ⟨w, n, rfl, by omega, by omega⟩
        case h_2 x y =>
          split
          case h_1 items hcan =>
            rw [Pred.denote.eq_2] at hv ⊢
            obtain ⟨c, hc, hcv⟩ := hv
            exact canonicalizeMembers_preserves hcan (mem_append_right hc) hcv
          case h_2 _ => exact denote_Top U m v
        case h_3 _ _ _ _ => exact denote_Top U m v
        case h_4 _ _ =>
          rw [Pred.denote.eq_7]
          exact (denoteAny_iff U m [srcPred, dstPred] v).mpr ⟨dstPred, by simp, hv⟩

end TrustIr
