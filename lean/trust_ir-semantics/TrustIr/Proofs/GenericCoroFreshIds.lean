-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.NatIndex

namespace TrustIr.GenericCoroFreshIds

theorem map_member {α β : Type} (f : α → β) (list : List α) (item : α)
    (member : item ∈ list) : f item ∈ list.map f := by
  induction list with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with same | old
    · subst item; exact (trustIrListMemConsSelf _ _)
    · exact List.mem_cons_of_mem (f head) (ih old)

/-- A finite reservation list always leaves a gap within its own census.
    The proof's key compression is erased; runtime search uses the sparse
    index and never constructs these mapped lists. -/
theorem unused_le_length (used : List Nat) :
    ∃ candidate, candidate ≤ used.length ∧ candidate ∉ used := by
  generalize sizeEq : used.length = size
  induction size using trustIrNatStrongInduction generalizing used with
  | ind size ih =>
    cases used with
    | nil => exact ⟨0, Nat.zero_le _, by intro member; cases member⟩
    | cons head rest =>
      let squeeze : Nat → Nat := fun key => if key < head then key else key - 1
      have shorter : (rest.map squeeze).length < size := by
        simp only [List.length_map]
        simp only [List.length_cons] at sizeEq
        omega
      obtain ⟨candidate, bound, absent⟩ := ih _ shorter (rest.map squeeze) rfl
      have boundRest : candidate ≤ rest.length := by simpa only [List.length_map] using bound
      by_cases before : candidate < head
      · refine ⟨candidate, ?_, ?_⟩
        · simp only [List.length_cons] at sizeEq
          omega
        · intro member
          rcases List.mem_cons.mp member with same | old
          · omega
          · have mapped := map_member squeeze rest candidate old
            have unchanged : squeeze candidate = candidate := by simp only [squeeze, before, if_true]
            rw [unchanged] at mapped
            exact absent mapped
      · refine ⟨candidate + 1, ?_, ?_⟩
        · simp only [List.length_cons] at sizeEq
          omega
        · intro member
          rcases List.mem_cons.mp member with same | old
          · omega
          · have mapped := map_member squeeze rest (candidate + 1) old
            have after : ¬ candidate + 1 < head := by omega
            have unchanged : squeeze (candidate + 1) = candidate := by
              simp only [squeeze, after, if_false, Nat.add_sub_cancel]
            rw [unchanged] at mapped
            exact absent mapped

def occupied (used : List Nat) : NatIndex Unit :=
  used.foldl (fun index key => index.insert key ()) NatIndex.empty

theorem fold_find (used : List Nat) (index : NatIndex Unit) (query : Nat) :
    (used.foldl (fun table key => table.insert key ()) index).find? query =
      if query ∈ used then some () else index.find? query := by
  induction used generalizing index with
  | nil => rfl
  | cons head rest ih =>
    rw [List.foldl_cons, ih, NatIndex.find?_insert]
    by_cases inRest : query ∈ rest <;> by_cases same : query = head <;>
      simp [List.mem_cons, inRest, same]

theorem occupied_find (used : List Nat) (query : Nat) :
    (occupied used).find? query = if query ∈ used then some () else none := by
  exact fold_find used NatIndex.empty query

def CorrectIndex (used : List Nat) (index : NatIndex Unit) : Prop :=
  ∀ query, index.contains query = decide (query ∈ used)

theorem occupied_correct (used : List Nat) : CorrectIndex used (occupied used) := by
  intro query
  by_cases member : query ∈ used <;> simp [NatIndex.contains, occupied_find, member]

def scanGap (index : NatIndex Unit) : Nat → Nat → Option Nat
  | 0, _ => none
  | remaining + 1, candidate =>
    if index.contains candidate then scanGap index remaining (candidate + 1)
    else some candidate

theorem scanGap_some (index : NatIndex Unit) (remaining start candidate : Nat)
    (found : scanGap index remaining start = some candidate) :
    start ≤ candidate ∧ candidate < start + remaining ∧ index.contains candidate = false := by
  induction remaining generalizing start with
  | zero => cases found
  | succ remaining ih =>
    cases present : index.contains start with
    | false =>
      simp only [scanGap, present, Bool.false_eq_true, if_false] at found
      have same := Option.some.inj found
      subst candidate
      exact ⟨Nat.le_refl _, by omega, present⟩
    | true =>
      simp only [scanGap, present, if_true] at found
      have result := ih (start + 1) found
      exact ⟨by omega, by omega, result.2.2⟩

theorem scanGap_none (index : NatIndex Unit) (remaining start : Nat)
    (missing : scanGap index remaining start = none) :
    ∀ candidate, start ≤ candidate → candidate < start + remaining → index.contains candidate = true := by
  induction remaining generalizing start with
  | zero => intro candidate lower upper; omega
  | succ remaining ih =>
    cases present : index.contains start with
    | false => simp only [scanGap, present, Bool.false_eq_true, if_false] at missing <;> cases missing
    | true =>
      simp only [scanGap, present, if_true] at missing
      intro candidate lower upper
      by_cases same : candidate = start
      · subst candidate; exact present
      · exact ih (start + 1) missing candidate (by omega) (by omega)

def nextGap (domain : Nat) (used : List Nat) (index : NatIndex Unit) : Option Nat :=
  scanGap index (min (used.length + 1) domain) 0

theorem nextGap_some (domain : Nat) (used : List Nat) (index : NatIndex Unit)
    (correct : CorrectIndex used index) (candidate : Nat)
    (found : nextGap domain used index = some candidate) :
    candidate < domain ∧ candidate ∉ used := by
  have result := scanGap_some index _ 0 candidate found
  have bounded : min (used.length + 1) domain ≤ domain := Nat.min_le_right _ _
  refine ⟨by omega, ?_⟩
  intro member
  have present : index.contains candidate = true :=
    (correct candidate).trans (decide_eq_true member)
  rw [present] at result
  cases result.2.2

/-- Search exhaustion is a genuine finite-domain capacity certificate. The
    input-derived census suffices; no execution budget is imposed. -/
theorem nextGap_none (domain : Nat) (used : List Nat) (index : NatIndex Unit)
    (correct : CorrectIndex used index) (missing : nextGap domain used index = none) :
    ∀ candidate, candidate < domain → candidate ∈ used := by
  have allBelow := scanGap_none index (min (used.length + 1) domain) 0 missing
  have fullBound : domain ≤ used.length + 1 := by
    by_cases full : domain ≤ used.length + 1
    · exact full
    · have small : used.length + 1 < domain := by omega
      obtain ⟨gap, bound, absent⟩ := unused_le_length used
      have occupiedGap := allBelow gap (Nat.zero_le _) (by
        rw [Nat.min_eq_left (Nat.le_of_lt small)]
        omega)
      have notOccupied : index.contains gap = false :=
        (correct gap).trans (decide_eq_false absent)
      rw [notOccupied] at occupiedGap
      cases occupiedGap
  intro candidate bounded
  have present := allBelow candidate (Nat.zero_le _) (by
    rw [Nat.min_eq_right fullBound]
    simpa only [Nat.zero_add] using bounded)
  have decision : decide (candidate ∈ used) = true := (correct candidate).symm.trans present
  exact of_decide_eq_true decision

theorem contains_insert (index : NatIndex Unit) (key query : Nat) :
    (index.insert key ()).contains query = if query = key then true else index.contains query := by
  by_cases same : query = key <;> simp [NatIndex.contains, NatIndex.find?_insert, same]

theorem correct_insert (used : List Nat) (index : NatIndex Unit)
    (correct : CorrectIndex used index) (key : Nat) :
    CorrectIndex (key :: used) (index.insert key ()) := by
  intro query
  rw [contains_insert, correct query]
  by_cases same : query = key <;> by_cases old : query ∈ used <;>
    simp [List.mem_cons, same, old]

inductive GapResult (domain : Nat) (used : List Nat) where
  | gap (candidate : Nat) (bounded : candidate < domain) (unused : candidate ∉ used)
  | full (covers : ∀ candidate, candidate < domain → candidate ∈ used)

def reserveOne (domain : Nat) (used : List Nat) (index : NatIndex Unit)
    (correct : CorrectIndex used index) : GapResult domain used :=
  match found : nextGap domain used index with
  | some candidate =>
    let proof := nextGap_some domain used index correct candidate found
    .gap candidate proof.1 proof.2
  | none => .full (nextGap_none domain used index correct found)

structure Triple (domain : Nat) (used : List Nat) where
  first : Nat
  second : Nat
  third : Nat
  firstBound : first < domain
  secondBound : second < domain
  thirdBound : third < domain
  firstUnused : first ∉ used
  secondUnused : second ∉ used
  thirdUnused : third ∉ used
  firstSecond : first ≠ second
  firstThird : first ≠ third
  secondThird : second ≠ third

/-- Exhaustion after zero, one or two successful reservations proves that
    fewer than three fresh identifiers fit the actual finite domain. -/
structure Capacity (domain : Nat) (used : List Nat) where
  reserved : List Nat
  atMostTwo : reserved.length ≤ 2
  covers : ∀ candidate, candidate < domain → candidate ∈ reserved ++ used

inductive Reservation (domain : Nat) (used : List Nat) where
  | ready (names : Triple domain used)
  | capacity (proof : Capacity domain used)

def reserveThree (domain : Nat) (used : List Nat) : Reservation domain used :=
  let index := occupied used
  let correct := occupied_correct used
  match reserveOne domain used index correct with
  | .full covers => .capacity ⟨[], by decide, covers⟩
  | .gap first firstBound firstUnused =>
    let secondIndex := index.insert first ()
    let secondCorrect := correct_insert used index correct first
    match reserveOne domain (first :: used) secondIndex secondCorrect with
    | .full covers => .capacity ⟨[first], Nat.le_succ 1, covers⟩
    | .gap second secondBound secondUnused =>
      let thirdIndex := secondIndex.insert second ()
      let thirdCorrect := correct_insert (first :: used) secondIndex secondCorrect second
      match reserveOne domain (second :: first :: used) thirdIndex thirdCorrect with
      | .full covers => .capacity ⟨[second, first], Nat.le_refl 2, covers⟩
      | .gap third thirdBound thirdUnused =>
        .ready {
          first := first
          second := second
          third := third
          firstBound := firstBound
          secondBound := secondBound
          thirdBound := thirdBound
          firstUnused := firstUnused
          secondUnused := fun member => secondUnused (List.mem_cons_of_mem first member)
          thirdUnused := fun member => thirdUnused
            (List.mem_cons_of_mem second (List.mem_cons_of_mem first member))
          firstSecond := by
            intro same; subst second
            exact secondUnused ((trustIrListMemConsSelf _ _))
          firstThird := by
            intro same; subst third
            exact thirdUnused (List.mem_cons_of_mem second ((trustIrListMemConsSelf _ _)))
          secondThird := by
            intro same; subst third
            exact thirdUnused ((trustIrListMemConsSelf _ _)) }

def u32Domain : Nat := 2^32

def u32Names (used : List Nat) : Reservation u32Domain used := reserveThree u32Domain used

def observable {domain : Nat} {used : List Nat} : Reservation domain used → Option (List Nat)
  | .ready names => some [names.first, names.second, names.third]
  | .capacity _ => none

theorem max_u32_does_not_force_overflow :
    observable (u32Names [2^32 - 1]) = some [0, 1, 2] := rfl

theorem original_undefined_uses_stay_reserved :
    observable (u32Names [0, 2, 2^32 - 1]) = some [1, 3, 4] := rfl

theorem two_remaining_ids_are_capacity :
    observable (reserveThree 5 [0, 2, 4]) = none := rfl

theorem duplicates_do_not_create_false_capacity :
    observable (reserveThree 5 [0, 0, 0, 0, 0]) = some [1, 2, 3] := rfl

theorem left_member_of_append_not_right {α : Type} (left right : List α) (item : α)
    (member : item ∈ left ++ right) (notRight : item ∉ right) : item ∈ left := by
  induction left with
  | nil => exact False.elim (notRight member)
  | cons head rest ih =>
    rcases List.mem_cons.mp member with same | old
    · exact List.mem_cons.mpr (Or.inl same)
    · exact List.mem_cons_of_mem head (ih old)

theorem capacity_excludes_triple {domain : Nat} {used : List Nat}
    (capacity : Capacity domain used) (names : Triple domain used) : False := by
  rcases capacity with ⟨reserved, atMostTwo, covers⟩
  have firstIn := left_member_of_append_not_right reserved used names.first
    (covers names.first names.firstBound) names.firstUnused
  have secondIn := left_member_of_append_not_right reserved used names.second
    (covers names.second names.secondBound) names.secondUnused
  have thirdIn := left_member_of_append_not_right reserved used names.third
    (covers names.third names.thirdBound) names.thirdUnused
  cases reserved with
  | nil => cases firstIn
  | cons first rest =>
    cases rest with
    | nil =>
      rcases List.mem_cons.mp firstIn with firstEq | empty
      · rcases List.mem_cons.mp secondIn with secondEq | empty
        · exact names.firstSecond (firstEq.trans secondEq.symm)
        · cases empty
      · cases empty
    | cons second rest =>
      cases rest with
      | nil =>
        have twoCases (item : Nat) (member : item ∈ [first, second]) : item = first ∨ item = second := by
          rcases List.mem_cons.mp member with same | old
          · exact Or.inl same
          · rcases List.mem_cons.mp old with same | empty
            · exact Or.inr same
            · cases empty
        rcases twoCases names.first firstIn with firstEq | firstEq <;>
          rcases twoCases names.second secondIn with secondEq | secondEq <;>
          rcases twoCases names.third thirdIn with thirdEq | thirdEq <;>
          first
          | exact names.firstSecond (firstEq.trans secondEq.symm)
          | exact names.firstThird (firstEq.trans thirdEq.symm)
          | exact names.secondThird (secondEq.trans thirdEq.symm)
      | cons third rest =>
        simp only [List.length_cons] at atMostTwo
        omega

end TrustIr.GenericCoroFreshIds
