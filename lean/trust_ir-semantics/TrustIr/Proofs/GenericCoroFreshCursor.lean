-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroFreshIds

namespace TrustIr.GenericCoroFreshCursor
open GenericCoroFreshIds

/-- Conventional pairwise distinctness, without a separate finite-set model. -/
inductive Distinct : List Nat → Prop where
  | nil : Distinct []
  | cons (head : Nat) (tail : List Nat) (absent : head ∉ tail)
      (rest : Distinct tail) : Distinct (head :: tail)

/-- One prepared index is retained across reservations. The list is the
    reverse reservation history; source membership and all proof fields are
    erased. Every candidate below `next` is already occupied. -/
structure Cursor (domain : Nat) (used : List Nat) where
  index : NatIndex Unit
  next : Nat
  reserved : List Nat
  correct : CorrectIndex (reserved ++ used) index
  below : ∀ candidate, candidate < next → candidate ∈ reserved ++ used
  bound : next ≤ domain
  distinct : Distinct reserved
  reservedBound : ∀ candidate ∈ reserved, candidate < domain
  reservedUnused : ∀ candidate ∈ reserved, candidate ∉ used
  reservedBefore : ∀ candidate ∈ reserved, candidate < next

def prepare (domain : Nat) (used : List Nat) : Cursor domain used :=
  { index := occupied used
    next := 0
    reserved := []
    correct := occupied_correct used
    below := by intro candidate lower; omega
    bound := Nat.zero_le _
    distinct := .nil
    reservedBound := by intro candidate member; cases member
    reservedUnused := by intro candidate member; cases member
    reservedBefore := by intro candidate member; cases member }

theorem Cursor.member_of_contains {domain : Nat} {used : List Nat}
    (state : Cursor domain used) (candidate : Nat)
    (present : state.index.contains candidate = true) : candidate ∈ state.reserved ++ used :=
  of_decide_eq_true ((state.correct candidate).symm.trans present)

theorem Cursor.contains_of_member {domain : Nat} {used : List Nat}
    (state : Cursor domain used) (candidate : Nat)
    (member : candidate ∈ state.reserved ++ used) : state.index.contains candidate = true :=
  (state.correct candidate).trans (decide_eq_true member)

structure Search where
  key : Option Nat
  next : Nat
  visits : Nat

/-- Tail-recursive search over the exact remaining finite domain. This is
    not an evaluator budget: the only bound is the caller's actual domain.
    Each `contains` query increments the executable visit counter once. -/
def seek (index : NatIndex Unit) : Nat → Nat → Nat → Search
  | 0, candidate, visits => ⟨none, candidate, visits⟩
  | remaining + 1, candidate, visits =>
    if index.contains candidate then seek index remaining (candidate + 1) (visits + 1)
    else ⟨some candidate, candidate + 1, visits + 1⟩

theorem seek_key (index : NatIndex Unit) (remaining start visits : Nat) :
    (seek index remaining start visits).key = scanGap index remaining start := by
  induction remaining generalizing start visits with
  | zero => rfl
  | succ remaining ih =>
    cases present : index.contains start with
    | false => simp only [seek, scanGap, present, Bool.false_eq_true, if_false]
    | true => simpa only [seek, scanGap, present, if_true] using ih (start + 1) (visits + 1)

theorem seek_work (index : NatIndex Unit) (remaining start visits : Nat) :
    start + (seek index remaining start visits).visits =
      visits + (seek index remaining start visits).next := by
  induction remaining generalizing start visits with
  | zero => simp only [seek, Nat.add_comm]
  | succ remaining ih =>
    cases present : index.contains start with
    | false => simp only [seek, present, Bool.false_eq_true, if_false]; omega
    | true =>
      simp only [seek, present, if_true]
      have tail := ih (start + 1) (visits + 1)
      omega

theorem seek_next_some (index : NatIndex Unit) (remaining start visits key : Nat)
    (found : (seek index remaining start visits).key = some key) :
    (seek index remaining start visits).next = key + 1 := by
  induction remaining generalizing start visits with
  | zero => cases found
  | succ remaining ih =>
    cases present : index.contains start with
    | false =>
      simp only [seek, present, Bool.false_eq_true, if_false] at found ⊢
      exact congrArg (· + 1) (Option.some.inj found)
    | true =>
      simp only [seek, present, if_true] at found ⊢
      exact ih (start + 1) (visits + 1) found

theorem seek_next_none (index : NatIndex Unit) (remaining start visits : Nat)
    (missing : (seek index remaining start visits).key = none) :
    (seek index remaining start visits).next = start + remaining := by
  induction remaining generalizing start visits with
  | zero => rfl
  | succ remaining ih =>
    cases present : index.contains start with
    | false => simp only [seek, present, Bool.false_eq_true, if_false] at missing <;> cases missing
    | true =>
      simp only [seek, present, if_true] at missing ⊢
      have tail := ih (start + 1) (visits + 1) missing
      omega

theorem seek_before (index : NatIndex Unit) (remaining start visits key : Nat)
    (found : (seek index remaining start visits).key = some key) :
    ∀ candidate, start ≤ candidate → candidate < key → index.contains candidate = true := by
  induction remaining generalizing start visits with
  | zero => cases found
  | succ remaining ih =>
    cases present : index.contains start with
    | false =>
      simp only [seek, present, Bool.false_eq_true, if_false] at found
      have same := Option.some.inj found
      intro candidate lower upper
      omega
    | true =>
      simp only [seek, present, if_true] at found
      intro candidate lower upper
      by_cases same : candidate = start
      · subst candidate; exact present
      · exact ih (start + 1) (visits + 1) found candidate (by omega) upper

/-- A reservation exposes its actual updated cursor and measured candidate
    visits. Failure certifies the whole finite domain, including the prefix
    skipped by the cursor invariant. -/
structure Reservation {domain : Nat} {used : List Nat} (before : Cursor domain used) where
  after : Cursor domain used
  key : Option Nat
  visits : Nat
  work : before.next + visits = after.next
  history : after.reserved = key.toList ++ before.reserved
  fresh : ∀ candidate, key = some candidate → candidate ∉ before.reserved ++ used
  inRange : ∀ candidate, key = some candidate → candidate < domain
  keyCursor : ∀ candidate, key = some candidate → after.next = candidate + 1
  exhausted : key = none → ∀ candidate, candidate < domain → candidate ∈ after.reserved ++ used
  fullCursor : key = none → after.next = domain

/-- No index is rebuilt and no already-covered prefix is scanned. All list
    census reasoning below is proof-only; execution consults the retained
    sparse index, inserts at most one key, and advances monotonically. -/
def reserve {domain : Nat} {used : List Nat} (before : Cursor domain used) : Reservation before := by
  let search := seek before.index (domain - before.next) before.next 0
  have work : before.next + search.visits = search.next := by
    simpa only [Nat.zero_add] using seek_work before.index (domain - before.next) before.next 0
  cases found : search.key with
  | some key =>
    have scanned : scanGap before.index (domain - before.next) before.next = some key :=
      (seek_key before.index (domain - before.next) before.next 0).symm.trans found
    have info := scanGap_some before.index (domain - before.next) before.next key scanned
    have inRange : key < domain := by have bounded := before.bound; omega
    have fresh : key ∉ before.reserved ++ used := by
      intro member
      have present := before.contains_of_member key member
      rw [present] at info
      cases info.2.2
    have stopped : search.next = key + 1 :=
      seek_next_some before.index (domain - before.next) before.next 0 key found
    let after : Cursor domain used :=
      { index := before.index.insert key ()
        next := key + 1
        reserved := key :: before.reserved
        correct := correct_insert (before.reserved ++ used) before.index before.correct key
        below := by
          intro candidate lower
          by_cases same : candidate = key
          · subst candidate; exact (trustIrListMemConsSelf _ _)
          · apply List.mem_cons_of_mem
            by_cases earlier : candidate < before.next
            · exact before.below candidate earlier
            · exact before.member_of_contains candidate
                (seek_before before.index (domain - before.next) before.next 0 key found
                  candidate (by omega) (by omega))
        bound := by omega
        distinct := .cons key before.reserved
          (fun member => fresh ((by first | exact List.mem_append_of_mem_left used member | exact List.mem_append.mpr (Or.inl member)))) before.distinct
        reservedBound := by
          intro candidate member
          rcases List.mem_cons.mp member with same | old
          · subst candidate; exact inRange
          · exact before.reservedBound candidate old
        reservedUnused := by
          intro candidate member
          rcases List.mem_cons.mp member with same | old
          · subst candidate
            exact fun member => fresh ((by first | exact List.mem_append_of_mem_right before.reserved member | exact List.mem_append.mpr (Or.inr member)))
          · exact before.reservedUnused candidate old
        reservedBefore := by
          intro candidate member
          rcases List.mem_cons.mp member with same | old
          · subst candidate; omega
          · have prior := before.reservedBefore candidate old; omega }
    exact
      { after := after
        key := some key
        visits := search.visits
        work := by change before.next + search.visits = key + 1; omega
        history := rfl
        fresh := by intro candidate equal; cases equal; exact fresh
        inRange := by intro candidate equal; cases equal; exact inRange
        keyCursor := by intro candidate equal; cases equal; rfl
        exhausted := by intro impossible; cases impossible
        fullCursor := by intro impossible; cases impossible }
  | none =>
    have scanned : scanGap before.index (domain - before.next) before.next = none :=
      (seek_key before.index (domain - before.next) before.next 0).symm.trans found
    have occupiedTail := scanGap_none before.index (domain - before.next) before.next scanned
    have covers : ∀ candidate, candidate < domain → candidate ∈ before.reserved ++ used := by
      intro candidate bounded
      by_cases earlier : candidate < before.next
      · exact before.below candidate earlier
      · apply before.member_of_contains
        exact occupiedTail candidate (by omega) (by have bound := before.bound; omega)
    have stopped : search.next = domain := by
      have tail := seek_next_none before.index (domain - before.next) before.next 0 found
      change search.next = before.next + (domain - before.next) at tail
      have bound := before.bound
      omega
    let after : Cursor domain used :=
      { before with
        next := domain
        below := covers
        bound := Nat.le_refl _
        reservedBefore := before.reservedBound }
    exact
      { after := after
        key := none
        visits := search.visits
        work := by change before.next + search.visits = domain; omega
        history := rfl
        fresh := by intro candidate impossible; cases impossible
        inRange := by intro candidate impossible; cases impossible
        keyCursor := by intro candidate impossible; cases impossible
        exhausted := by intro _; exact covers
        fullCursor := by intro _; rfl }

theorem Reservation.monotone {domain : Nat} {used : List Nat}
    {before : Cursor domain used} (result : Reservation before) :
    before.next ≤ result.after.next := by
  have exactWork := result.work
  omega

theorem Reservation.length {domain : Nat} {used : List Nat}
    {before : Cursor domain used} (result : Reservation before) :
    result.after.reserved.length ≤ before.reserved.length + 1 := by
  have history := congrArg List.length result.history
  cases key : result.key <;>
    simp only [key, Option.toList, List.length_append, List.length_cons, List.length_nil] at history <;>
    omega

/-- A refusal covers the original occupied index, not a list to which an
    unchecked name was added during failure. -/
theorem Reservation.full_before {domain : Nat} {used : List Nat}
    {before : Cursor domain used} (result : Reservation before) (full : result.key = none) :
    ∀ candidate, candidate < domain → candidate ∈ before.reserved ++ used := by
  have history := result.history
  rw [full] at history
  change result.after.reserved = before.reserved at history
  intro candidate bounded
  rw [← history]
  exact result.exhausted full candidate bounded

theorem Reservation.member_preserved {domain : Nat} {used : List Nat}
    {before : Cursor domain used} (result : Reservation before) (candidate : Nat)
    (member : candidate ∈ before.reserved ++ used) :
    candidate ∈ result.after.reserved ++ used := by
  rw [result.history, List.append_assoc]
  first
  | exact trustIrListMemAppendRight _ member
  | exact List.mem_append.mpr (Or.inr member)

/-- The all-below-cursor invariant bounds even a duplicate-containing input
    by its real census. This proof is never used as a runtime scan limit. -/
theorem Cursor.next_le_census {domain : Nat} {used : List Nat}
    (state : Cursor domain used) : state.next ≤ state.reserved.length + used.length := by
  obtain ⟨gap, bounded, absent⟩ := unused_le_length (state.reserved ++ used)
  simp only [List.length_append] at bounded
  by_cases fits : state.next ≤ state.reserved.length + used.length
  · exact fits
  · exact False.elim (absent (state.below gap (by omega)))

/-- Repeated requests retain the same index and cursor. After exhaustion,
    subsequent requests inspect no candidates. `count` is the number of
    requested reservations, not an evaluator resource or admission bound. -/
def reserveManyLoop {domain : Nat} {used : List Nat} :
    Nat → Cursor domain used → Nat → Cursor domain used × Nat
  | 0, state, visits => (state, visits)
  | count + 1, state, visits =>
    let first := reserve state
    reserveManyLoop count first.after (visits + first.visits)

/-- Diagnostic fold of requests. Per-site consumers inspect `reserve.key`
    and its explicit capacity certificate; this fold promises no implicit
    successful count. Its accumulated history and work remain certified. -/
def reserveMany {domain : Nat} {used : List Nat} (count : Nat)
    (state : Cursor domain used) : Cursor domain used × Nat := reserveManyLoop count state 0

theorem reserveManyLoop_work {domain : Nat} {used : List Nat} (count : Nat)
    (state : Cursor domain used) (visits : Nat) :
    state.next + (reserveManyLoop count state visits).2 =
      visits + (reserveManyLoop count state visits).1.next := by
  induction count generalizing state visits with
  | zero => simp only [reserveManyLoop, Nat.add_comm]
  | succ count ih =>
    simp only [reserveManyLoop]
    have tail := ih (reserve state).after (visits + (reserve state).visits)
    have first := (reserve state).work
    omega

theorem reserveManyLoop_length {domain : Nat} {used : List Nat} (count : Nat)
    (state : Cursor domain used) (visits : Nat) :
    (reserveManyLoop count state visits).1.reserved.length ≤ state.reserved.length + count := by
  induction count generalizing state visits with
  | zero => simp only [reserveManyLoop, Nat.add_zero, Nat.le_refl]
  | succ count ih =>
    simp only [reserveManyLoop]
    have tail := ih (reserve state).after (visits + (reserve state).visits)
    have first := (reserve state).length
    omega

theorem reserveManyLoop_member_preserved {domain : Nat} {used : List Nat} (count : Nat)
    (state : Cursor domain used) (visits candidate : Nat)
    (member : candidate ∈ state.reserved ++ used) :
    candidate ∈ (reserveManyLoop count state visits).1.reserved ++ used := by
  induction count generalizing state visits with
  | zero => exact member
  | succ _ ih =>
    exact ih (reserve state).after (visits + (reserve state).visits)
      ((reserve state).member_preserved candidate member)

theorem reserveManyLoop_capacity {domain : Nat} {used : List Nat} (count : Nat)
    (state : Cursor domain used) (visits : Nat)
    (short : (reserveManyLoop count state visits).1.reserved.length <
      state.reserved.length + count) :
    ∀ candidate, candidate < domain →
      candidate ∈ (reserveManyLoop count state visits).1.reserved ++ used := by
  induction count generalizing state visits with
  | zero => simp only [reserveManyLoop, Nat.add_zero] at short; omega
  | succ count ih =>
    simp only [reserveManyLoop] at short ⊢
    cases key : (reserve state).key with
    | none =>
      intro candidate bounded
      exact reserveManyLoop_member_preserved count (reserve state).after
        (visits + (reserve state).visits) candidate
        ((reserve state).exhausted key candidate bounded)
    | some candidate =>
      have history := congrArg List.length (reserve state).history
      rw [key] at history
      change (reserve state).after.reserved.length = state.reserved.length + 1 at history
      exact ih (reserve state).after (visits + (reserve state).visits) (by omega)

/-- The actual candidate counter telescopes exactly across any number of
    reservations; no prefix can be charged twice. -/
theorem reserveMany_work {domain : Nat} {used : List Nat} (count : Nat)
    (state : Cursor domain used) :
    state.next + (reserveMany count state).2 = (reserveMany count state).1.next := by
  simpa only [reserveMany, Nat.zero_add] using reserveManyLoop_work count state 0

/-- Reserving names in separate block-sized groups charges the same forward
    cursor interval. A group never rebuilds the index or restarts at zero. -/
theorem grouped_work {domain : Nat} {used : List Nat} (first second : Nat)
    (state : Cursor domain used) :
    state.next + ((reserveMany first state).2 +
      (reserveMany second (reserveMany first state).1).2) =
        (reserveMany second (reserveMany first state).1).1.next := by
  have firstWork := reserveMany_work first state
  have secondWork := reserveMany_work second (reserveMany first state).1
  omega

theorem reserveMany_visit_domain_bound {domain : Nat} {used : List Nat} (count : Nat)
    (state : Cursor domain used) :
    (reserveMany count state).2 ≤ domain - state.next := by
  have work := reserveMany_work count state
  have bounded := (reserveMany count state).1.bound
  omega

/-- A short batch has a genuine full-domain certificate, rather than a
    search-budget refusal or a successful-looking truncated name list. -/
theorem reserveMany_capacity {domain : Nat} {used : List Nat} (count : Nat)
    (state : Cursor domain used)
    (short : (reserveMany count state).1.reserved.length < state.reserved.length + count) :
    ∀ candidate, candidate < domain → candidate ∈ (reserveMany count state).1.reserved ++ used :=
  reserveManyLoop_capacity count state 0 short

/-- Starting from the one prepared source index, total candidate queries
    are linear in the source reservation census plus requests, irrespective
    of the finite domain, duplicate IDs, high keys or block grouping. -/
theorem prepare_many_visit_census_bound (domain : Nat) (used : List Nat) (count : Nat) :
    (reserveMany count (prepare domain used)).2 ≤ used.length + count := by
  have work := reserveMany_work count (prepare domain used)
  have census := (reserveMany count (prepare domain used)).1.next_le_census
  have length := reserveManyLoop_length count (prepare domain used) 0
  change 0 + (reserveMany count (prepare domain used)).2 =
    (reserveMany count (prepare domain used)).1.next at work
  change (reserveMany count (prepare domain used)).1.reserved.length ≤ 0 + count at length
  omega

theorem reserveMany_distinct {domain : Nat} {used : List Nat} (count : Nat)
    (state : Cursor domain used) : Distinct (reserveMany count state).1.reserved :=
  (reserveMany count state).1.distinct

theorem reserveMany_in_range {domain : Nat} {used : List Nat} (count : Nat)
    (state : Cursor domain used) (candidate : Nat)
    (member : candidate ∈ (reserveMany count state).1.reserved) : candidate < domain :=
  (reserveMany count state).1.reservedBound candidate member

theorem reserveMany_source_unused {domain : Nat} {used : List Nat} (count : Nat)
    (state : Cursor domain used) (candidate : Nat)
    (member : candidate ∈ (reserveMany count state).1.reserved) : candidate ∉ used :=
  (reserveMany count state).1.reservedUnused candidate member

def prepareU32 (used : List Nat) : Cursor u32Domain used := prepare u32Domain used

def observe {domain : Nat} {used : List Nat} (state : Cursor domain used) :
    Option Nat × Nat × Nat :=
  let result := reserve state
  (result.key, result.after.next, result.visits)

theorem first_hole : observe (prepare 7 [0, 2, 2]) = (some 1, 2, 2) := rfl

theorem next_hole_skips_no_old_prefix :
    observe (reserve (prepare 7 [0, 2, 2])).after = (some 3, 4, 2) := rfl

theorem duplicates_do_not_add_candidate_visits :
    observe (prepare 7 [0, 0, 0, 0, 0]) = (some 1, 2, 2) := rfl

theorem high_keys_do_not_force_a_high_cursor :
    observe (prepareU32 [2^32 - 1, 2^128]) = (some 0, 1, 1) := rfl

theorem exact_capacity : observe (prepare 3 [0, 1, 2]) = (none, 3, 3) := rfl

theorem zero_domain_needs_no_candidate_visit :
    observe (prepare 0 [17, 17, 2^32 - 1]) = (none, 0, 0) := rfl

theorem exhausted_cursor_needs_no_repeat_visit :
    observe (reserve (prepare 2 [0])).after = (none, 2, 0) := rfl

theorem grouped_work_control :
    let result := reserveMany 4 (prepare 9 [0, 2, 4])
    (result.1.reserved, result.1.next, result.2) = ([6, 5, 3, 1], 7, 7) := rfl

theorem requests_after_capacity_add_no_candidate_visits :
    let result := reserveMany 20 (prepare 4 [1, 3])
    (result.1.reserved, result.1.next, result.2) = ([2, 0], 4, 4) := rfl

private theorem member_split (candidate : Nat) (items : List Nat)
    (member : candidate ∈ items) :
    ∃ before after, items = before ++ candidate :: after := by
  induction items with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with same | old
    · subst head; exact ⟨[], rest, rfl⟩
    · obtain ⟨before, after, shape⟩ := ih old
      exact ⟨head :: before, after, by rw [shape]; rfl⟩

private theorem member_remove_selected (before after : List Nat) (removed candidate : Nat)
    (different : candidate ≠ removed) (member : candidate ∈ before ++ removed :: after) :
    candidate ∈ before ++ after := by
  induction before with
  | nil =>
    rcases List.mem_cons.mp member with same | old
    · exact False.elim (different same)
    · exact old
  | cons head rest ih =>
    rcases List.mem_cons.mp member with same | old
    · subst candidate; exact (trustIrListMemConsSelf _ _)
    · exact List.mem_cons_of_mem head (ih old)

/-- Pure finite pigeonhole reasoning. The containing list need not itself
    be distinct; no runtime enumeration of the identifier domain is built. -/
theorem Distinct.length_le_of_subset {items : List Nat} (distinct : Distinct items)
    (containing : List Nat) (included : ∀ candidate ∈ items, candidate ∈ containing) :
    items.length ≤ containing.length := by
  induction distinct generalizing containing with
  | nil => exact Nat.zero_le _
  | cons head rest absent distinct ih =>
    obtain ⟨before, after, shape⟩ :=
      member_split head containing (included head ((trustIrListMemConsSelf _ _)))
    subst containing
    have smaller : ∀ candidate ∈ rest, candidate ∈ before ++ after := by
      intro candidate member
      apply member_remove_selected before after head candidate
      · intro same; subst candidate; exact absent member
      · exact included candidate (List.mem_cons_of_mem head member)
    have bounded := ih (before ++ after) smaller
    simp only [List.length_cons, List.length_append] at bounded ⊢
    omega

/-- A short occupied history covering the whole domain rules out ANY
    requested-size fresh schedule for the original source. With an already
    advanced cursor this applies only when the TOTAL history is short; a
    relative shortfall is not silently called original-source capacity. -/
theorem capacity_excludes_schedule (domain : Nat) (history source : List Nat) (requested : Nat)
    (covers : ∀ candidate, candidate < domain → candidate ∈ history ++ source)
    (short : history.length < requested) (candidates : List Nat)
    (census : candidates.length = requested) (distinct : Distinct candidates)
    (inRange : ∀ candidate ∈ candidates, candidate < domain)
    (unused : ∀ candidate ∈ candidates, candidate ∉ source) : False := by
  have included : ∀ candidate ∈ candidates, candidate ∈ history := by
    intro candidate member
    exact left_member_of_append_not_right history source candidate
      (covers candidate (inRange candidate member)) (unused candidate member)
  have bounded := distinct.length_le_of_subset history included
  omega

/-- The real allocator's partial history supplies the general capacity
    contradiction; this control does not assume an arbitrary full table. -/
theorem two_free_ids_exclude_three :
    ¬ ∃ candidates : List Nat, candidates.length = 3 ∧ Distinct candidates ∧
      (∀ candidate ∈ candidates, candidate < 5) ∧
      (∀ candidate ∈ candidates, candidate ∉ [0, 2, 4]) := by
  intro proposed
  obtain ⟨candidates, census, distinct, inRange, unused⟩ := proposed
  let result := reserveMany 3 (prepare 5 [0, 2, 4])
  have short : result.1.reserved.length < 3 := by decide
  have covers : ∀ candidate, candidate < 5 → candidate ∈ result.1.reserved ++ [0, 2, 4] :=
    reserveMany_capacity 3 (prepare 5 [0, 2, 4]) (by exact short)
  exact capacity_excludes_schedule 5 result.1.reserved [0, 2, 4] 3 covers short
    candidates census distinct inRange unused

end TrustIr.GenericCoroFreshCursor
