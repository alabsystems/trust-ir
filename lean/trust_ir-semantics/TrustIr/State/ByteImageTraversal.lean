-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.State.ByteImage
import TrustIr.State.CompactArray

namespace TrustIr.ByteImage

private def scanWhere (test : Option UInt8 → Bool) (read : Nat → Option UInt8)
    (offset : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | remaining + 1, index =>
    if test (read (offset + index)) then some index
    else scanWhere test read offset remaining (index + 1)

private theorem scanWhere_sound (test : Option UInt8 → Bool) (read : Nat → Option UInt8)
    (offset remaining start hit : Nat)
    (found : scanWhere test read offset remaining start = some hit) :
    start ≤ hit ∧ hit < start + remaining ∧ test (read (offset + hit)) = true := by
  induction remaining generalizing start with
  | zero => simp [scanWhere] at found
  | succ remaining ih =>
    simp only [scanWhere] at found
    split at found
    · rename_i accepted
      cases found
      exact ⟨Nat.le_refl _, by omega, accepted⟩
    · obtain ⟨lower, upper, accepted⟩ := ih (start + 1) found
      exact ⟨by omega, by omega, accepted⟩

private theorem scanWhere_none (test : Option UInt8 → Bool) (read : Nat → Option UInt8)
    (offset remaining start index : Nat)
    (absent : scanWhere test read offset remaining start = none)
    (lower : start ≤ index) (upper : index < start + remaining) :
    test (read (offset + index)) = false := by
  induction remaining generalizing start with
  | zero => omega
  | succ remaining ih =>
    simp only [scanWhere] at absent
    split at absent
    · contradiction
    · rename_i rejected
      by_cases first : index = start
      · subst index
        cases value : test (read (offset + start)) <;> simp_all
      · exact ih (start + 1) absent (by omega) (by omega)

private theorem scanWhere_before (test : Option UInt8 → Bool) (read : Nat → Option UInt8)
    (offset remaining start hit index : Nat)
    (found : scanWhere test read offset remaining start = some hit)
    (lower : start ≤ index) (earlier : index < hit) :
    test (read (offset + index)) = false := by
  induction remaining generalizing start with
  | zero => simp [scanWhere] at found
  | succ remaining ih =>
    simp only [scanWhere] at found
    split at found
    · cases found; omega
    · rename_i rejected
      by_cases first : index = start
      · subst index
        cases value : test (read (offset + start)) <;> simp_all
      · exact ih (start + 1) found (by omega)

/-- Search actual image structure. Arbitrary external sources are inspected
    pointwise; only constructors carrying repetition justify skipping cycles. -/
def Tree.firstWhere {size : Nat} (test : Option UInt8 → Bool)
    (tree : Tree size) (offset count : Nat) : Option Nat :=
  let count := min count (size - offset)
  if count == 0 then none else
  match tree with
  | .fill _ byte => if test byte then some 0 else none
  | .literal data => scanWhere test (fun index => (data[index]?).getD none) offset count 0
  | .source _ read => scanWhere test read offset count 0
  | .view original start _ _ => original.firstWhere test (start + offset) count
  | .append (leftSize := leftSize) left right =>
    let before := min count (leftSize - offset)
    match left.firstWhere test offset before with
    | some index => some index
    | none => (right.firstWhere test (offset + before - leftSize) (count - before)).map (before + ·)
  | .periodic (period := period) unit _ phase _ =>
    let start := (phase + offset) % period
    let before := min count (period - start)
    match unit.firstWhere test start before with
    | some index => some index
    | none => (unit.firstWhere test 0 (min period (count - before))).map (before + ·)

/-- Every reported hit names an actual matching byte in the clipped visible
    range. Retained bytes outside that range cannot justify a result. This is
    a law of the safe traversal, not a refinement proof of its unsafe cache. -/
theorem Tree.firstWhere_sound {size : Nat} (tree : Tree size)
    (test : Option UInt8 → Bool) (offset count hit : Nat)
    (found : tree.firstWhere test offset count = some hit) :
    hit < min count (size - offset) ∧ test (tree.get (offset + hit)) = true := by
  induction tree generalizing offset count hit with
  | fill size byte =>
    simp only [Tree.firstWhere] at found
    split at found
    · contradiction
    · rename_i nonempty
      split at found
      · rename_i accepted
        cases found
        have visible : 0 < min count (size - offset) := by
          have nonzero : min count (size - offset) ≠ 0 := by
            intro zero
            simp [zero] at nonempty
          omega
        refine ⟨visible, ?_⟩
        change test (if offset < size then byte else none) = true
        rw [if_pos (by omega)]
        exact accepted
      · contradiction
  | literal data =>
    simp only [Tree.firstWhere] at found
    split at found
    · contradiction
    · obtain ⟨_, bound, accepted⟩ := scanWhere_sound test _ offset _ 0 hit found
      exact ⟨by omega, by simpa [Tree.get, show offset + hit < data.size by omega] using accepted⟩
  | source size read =>
    simp only [Tree.firstWhere] at found
    split at found
    · contradiction
    · obtain ⟨_, bound, accepted⟩ := scanWhere_sound test read offset _ 0 hit found
      exact ⟨by omega, by simpa [Tree.get, show offset + hit < size by omega] using accepted⟩
  | view original start size inside ih =>
    simp only [Tree.firstWhere] at found
    split at found
    · contradiction
    · obtain ⟨bound, accepted⟩ := ih (start + offset) _ hit found
      have visible : hit < min count (size - offset) := by omega
      refine ⟨visible, ?_⟩
      simpa only [Tree.get, if_pos (show offset + hit < size by omega), Nat.add_assoc] using accepted
  | @append leftSize rightSize left right ihl ihr =>
    simp only [Tree.firstWhere] at found
    split at found
    · contradiction
    · cases first : left.firstWhere test offset
          (min (min count (leftSize + rightSize - offset)) (leftSize - offset)) with
      | some index =>
        simp only [first, Option.some.injEq] at found
        subst hit
        obtain ⟨bound, accepted⟩ := ihl _ _ index first
        refine ⟨by omega, ?_⟩
        simpa only [Tree.get, if_pos (show offset + index < leftSize + rightSize by omega),
          if_pos (show offset + index < leftSize by omega)] using accepted
      | none =>
        simp only [first] at found
        cases later : right.firstWhere test
            (offset + min (min count (leftSize + rightSize - offset)) (leftSize - offset) - leftSize)
            (min count (leftSize + rightSize - offset) -
              min (min count (leftSize + rightSize - offset)) (leftSize - offset)) with
        | none => rw [later] at found; cases found
        | some index =>
          simp only [later, Option.map, Option.some.injEq] at found
          subst hit
          obtain ⟨bound, accepted⟩ := ihr _ _ index later
          have visibleHit : min (min count (leftSize + rightSize - offset)) (leftSize - offset) + index <
              min count (leftSize + rightSize - offset) := by omega
          have crosses : leftSize ≤ offset +
              min (min count (leftSize + rightSize - offset)) (leftSize - offset) := by omega
          have totalHit : offset +
              (min (min count (leftSize + rightSize - offset)) (leftSize - offset) + index) <
              leftSize + rightSize := by
            have := Nat.min_le_right count (leftSize + rightSize - offset)
            omega
          have notLeft : ¬ offset +
              (min (min count (leftSize + rightSize - offset)) (leftSize - offset) + index) < leftSize := by omega
          refine ⟨by omega, ?_⟩
          rw [Tree.get, if_pos totalHit, if_neg notLeft]
          have arithmetic : offset +
              (min (min count (leftSize + rightSize - offset)) (leftSize - offset) + index) - leftSize =
              (offset + min (min count (leftSize + rightSize - offset)) (leftSize - offset) - leftSize) + index := by omega
          rw [arithmetic]
          exact accepted
  | @periodic period unit positive phase size ih =>
    simp only [Tree.firstWhere] at found
    split at found
    · contradiction
    · let start := (phase + offset) % period
      let visible := min count (size - offset)
      let before := min visible (period - start)
      have startBound : start < period := Nat.mod_lt _ positive
      change (match unit.firstWhere test start before with
        | some index => some index
        | none => (unit.firstWhere test 0 (min period (visible - before))).map (before + ·)) = some hit at found
      cases first : unit.firstWhere test start before with
      | some index =>
        simp only [first, Option.some.injEq] at found
        subst hit
        obtain ⟨bound, accepted⟩ := ih start before index first
        have visibleHit : index < visible := by dsimp [before] at bound; omega
        have periodHit : start + index < period := by dsimp [before] at bound; omega
        refine ⟨visibleHit, ?_⟩
        rw [Tree.get, if_pos (by dsimp [visible] at visibleHit; omega)]
        have arithmetic : (phase + (offset + index)) % period = start + index := by
          rw [← Nat.add_assoc, ← Nat.mod_add_mod (phase + offset) period index]
          exact Nat.mod_eq_of_lt periodHit
        rw [arithmetic]
        exact accepted
      | none =>
        simp only [first] at found
        cases later : unit.firstWhere test 0 (min period (visible - before)) with
        | none => rw [later] at found; cases found
        | some index =>
          simp only [later, Option.map, Option.some.injEq] at found
          subst hit
          obtain ⟨bound, accepted⟩ := ih 0 _ index later
          have visibleHit : before + index < visible := by omega
          have full : before = period - start := by dsimp [before] at *; omega
          have periodHit : index < period := by omega
          refine ⟨visibleHit, ?_⟩
          rw [Tree.get, if_pos (by dsimp [visible] at visibleHit; omega)]
          have arithmetic : (phase + (offset + (before + index))) % period = index := by
            rw [← Nat.add_assoc, ← Nat.mod_add_mod (phase + offset) period (before + index)]
            change (start + (before + index)) % period = index
            have wrap : start + (period - start) = period := by omega
            rw [← Nat.add_assoc, full, wrap]
            simp [Nat.add_mod, Nat.mod_eq_of_lt periodHit]
          rw [arithmetic]
          simpa only [Nat.zero_add] using accepted

/-- Returning no hit excludes a match at every byte of the clipped visible
    range, including repetitions beyond the two physically inspected pieces. -/
theorem Tree.firstWhere_none {size : Nat} (tree : Tree size)
    (test : Option UInt8 → Bool) (offset count index : Nat)
    (absent : tree.firstWhere test offset count = none)
    (inside : index < min count (size - offset)) :
    test (tree.get (offset + index)) = false := by
  induction tree generalizing offset count index with
  | fill size byte =>
    simp only [Tree.firstWhere, beq_iff_eq,
      if_neg (show min count (size - offset) ≠ 0 by omega)] at absent
    have rejected : test byte = false := by
      cases value : test byte <;> simp_all
    simpa [Tree.get, show offset + index < size by omega] using rejected
  | literal data =>
    simp only [Tree.firstWhere, beq_iff_eq,
      if_neg (show min count (data.size - offset) ≠ 0 by omega)] at absent
    have rejected := scanWhere_none test _ offset _ 0 index absent (by omega) (by omega)
    simpa [Tree.get, show offset + index < data.size by omega] using rejected
  | source size read =>
    simp only [Tree.firstWhere, beq_iff_eq,
      if_neg (show min count (size - offset) ≠ 0 by omega)] at absent
    have rejected := scanWhere_none test read offset _ 0 index absent (by omega) (by omega)
    simpa [Tree.get, show offset + index < size by omega] using rejected
  | view original start size within ih =>
    simp only [Tree.firstWhere, beq_iff_eq,
      if_neg (show min count (size - offset) ≠ 0 by omega)] at absent
    have rejected := ih (start + offset) _ index absent (by omega)
    simpa only [Tree.get, if_pos (show offset + index < size by omega), Nat.add_assoc] using rejected
  | @append leftSize rightSize left right ihl ihr =>
    let visible := min count (leftSize + rightSize - offset)
    let before := min visible (leftSize - offset)
    have visibleBound : visible ≤ leftSize + rightSize - offset := Nat.min_le_right _ _
    have beforeBound : before ≤ leftSize - offset := Nat.min_le_right _ _
    have beforeVisible : before ≤ visible := Nat.min_le_left _ _
    simp only [Tree.firstWhere, beq_iff_eq,
      if_neg (show min count (leftSize + rightSize - offset) ≠ 0 by omega)] at absent
    change (match left.firstWhere test offset before with
      | some hit => some hit
      | none => (right.firstWhere test (offset + before - leftSize) (visible - before)).map (before + ·)) = none at absent
    cases first : left.firstWhere test offset before with
    | some hit => simp [first] at absent
    | none =>
      have later : right.firstWhere test (offset + before - leftSize) (visible - before) = none := by
        cases result : right.firstWhere test (offset + before - leftSize) (visible - before) with
        | none => rfl
        | some hit => simp [first, result] at absent
      by_cases early : index < before
      · have rejected := ihl offset before index first (by omega)
        simpa only [Tree.get, if_pos (show offset + index < leftSize + rightSize by omega),
          if_pos (show offset + index < leftSize by omega)] using rejected
      · have full : before = leftSize - offset := by dsimp [before] at *; omega
        have crosses : leftSize ≤ offset + before := by omega
        have rejected := ihr (offset + before - leftSize) (visible - before) (index - before) later (by omega)
        rw [Tree.get, if_pos (show offset + index < leftSize + rightSize by omega),
          if_neg (show ¬ offset + index < leftSize by omega)]
        have arithmetic : offset + index - leftSize = offset + before - leftSize + (index - before) := by omega
        rw [arithmetic]
        exact rejected
  | @periodic period unit positive phase size ih =>
    let start := (phase + offset) % period
    let visible := min count (size - offset)
    let before := min visible (period - start)
    have startBound : start < period := Nat.mod_lt _ positive
    have beforeBound : before ≤ period - start := Nat.min_le_right _ _
    simp only [Tree.firstWhere, beq_iff_eq,
      if_neg (show min count (size - offset) ≠ 0 by omega)] at absent
    change (match unit.firstWhere test start before with
      | some hit => some hit
      | none => (unit.firstWhere test 0 (min period (visible - before))).map (before + ·)) = none at absent
    cases first : unit.firstWhere test start before with
    | some hit => simp [first] at absent
    | none =>
      have later : unit.firstWhere test 0 (min period (visible - before)) = none := by
        cases result : unit.firstWhere test 0 (min period (visible - before)) with
        | none => rfl
        | some hit => simp [first, result] at absent
      by_cases early : index < before
      · have rejected := ih start before index first (by omega)
        rw [Tree.get, if_pos (show offset + index < size by omega)]
        have arithmetic : (phase + (offset + index)) % period = start + index := by
          rw [← Nat.add_assoc, ← Nat.mod_add_mod (phase + offset) period index]
          exact Nat.mod_eq_of_lt (by omega)
        rw [arithmetic]
        exact rejected
      · have full : before = period - start := by dsimp [before] at *; omega
        have modBound : (index - before) % period < period := Nat.mod_lt _ positive
        have modLe : (index - before) % period ≤ index - before := Nat.mod_le _ _
        have rejected := ih 0 (min period (visible - before)) ((index - before) % period) later (by omega)
        rw [Tree.get, if_pos (show offset + index < size by omega)]
        have arithmetic : (phase + (offset + index)) % period = (index - before) % period := by
          rw [← Nat.add_assoc, ← Nat.mod_add_mod (phase + offset) period index]
          change (start + index) % period = (index - before) % period
          have wrap : start + index = period + (index - before) := by omega
          rw [wrap]
          simp [Nat.add_mod]
        rw [arithmetic]
        simpa only [Nat.zero_add] using rejected

theorem Tree.firstWhere_eq_none_iff {size : Nat} (tree : Tree size)
    (test : Option UInt8 → Bool) (offset count : Nat) :
    tree.firstWhere test offset count = none ↔
      ∀ index, index < min count (size - offset) → test (tree.get (offset + index)) = false := by
  constructor
  · intro absent index inside
    exact tree.firstWhere_none test offset count index absent inside
  · intro rejected
    cases result : tree.firstWhere test offset count with
    | none => rfl
    | some hit =>
      obtain ⟨inside, accepted⟩ := tree.firstWhere_sound test offset count hit result
      rw [rejected hit inside] at accepted
      contradiction

/-- Every visible byte before a reported hit fails the predicate. Together
    with hit soundness and no-hit completeness this fixes the search result. -/
theorem Tree.firstWhere_before {size : Nat} (tree : Tree size)
    (test : Option UInt8 → Bool) (offset count hit index : Nat)
    (found : tree.firstWhere test offset count = some hit) (earlier : index < hit) :
    test (tree.get (offset + index)) = false := by
  induction tree generalizing offset count hit index with
  | fill size byte =>
    simp only [Tree.firstWhere] at found
    split at found
    · contradiction
    · split at found
      · cases found; omega
      · contradiction
  | literal data =>
    have ⟨bound, _⟩ := (Tree.literal data).firstWhere_sound test offset count hit found
    simp only [Tree.firstWhere] at found
    split at found
    · contradiction
    · have rejected := scanWhere_before test _ offset _ 0 hit index found (by omega) earlier
      simpa [Tree.get, show offset + index < data.size by omega] using rejected
  | source size read =>
    have ⟨bound, _⟩ := (Tree.source size read).firstWhere_sound test offset count hit found
    simp only [Tree.firstWhere] at found
    split at found
    · contradiction
    · have rejected := scanWhere_before test read offset _ 0 hit index found (by omega) earlier
      simpa [Tree.get, show offset + index < size by omega] using rejected
  | view original start size within ih =>
    have ⟨bound, _⟩ := (Tree.view original start size within).firstWhere_sound test offset count hit found
    simp only [Tree.firstWhere] at found
    split at found
    · contradiction
    · have rejected := ih (start + offset) _ hit index found earlier
      simpa only [Tree.get, if_pos (show offset + index < size by omega), Nat.add_assoc] using rejected
  | @append leftSize rightSize left right ihl ihr =>
    let visible := min count (leftSize + rightSize - offset)
    let before := min visible (leftSize - offset)
    have beforeBound : before ≤ leftSize - offset := Nat.min_le_right _ _
    have beforeVisible : before ≤ visible := Nat.min_le_left _ _
    simp only [Tree.firstWhere] at found
    split at found
    · contradiction
    · change (match left.firstWhere test offset before with
        | some hit => some hit
        | none => (right.firstWhere test (offset + before - leftSize) (visible - before)).map (before + ·)) = some hit at found
      cases first : left.firstWhere test offset before with
      | some childHit =>
        simp only [first, Option.some.injEq] at found
        subst hit
        have ⟨bound, _⟩ := left.firstWhere_sound test offset before childHit first
        have rejected := ihl offset before childHit index first earlier
        simpa only [Tree.get, if_pos (show offset + index < leftSize + rightSize by omega),
          if_pos (show offset + index < leftSize by omega)] using rejected
      | none =>
        simp only [first] at found
        cases later : right.firstWhere test (offset + before - leftSize) (visible - before) with
        | none => rw [later] at found; cases found
        | some childHit =>
          simp only [later, Option.map, Option.some.injEq] at found
          subst hit
          have ⟨bound, _⟩ := right.firstWhere_sound test (offset + before - leftSize) (visible - before) childHit later
          have full : before = leftSize - offset := by dsimp [before] at *; omega
          have crosses : leftSize ≤ offset + before := by omega
          have totalHit : offset + index < leftSize + rightSize := by omega
          by_cases early : index < before
          · have rejected := left.firstWhere_none test offset before index first (by omega)
            simpa only [Tree.get, if_pos totalHit,
              if_pos (show offset + index < leftSize by omega)] using rejected
          · have rejected := ihr (offset + before - leftSize) (visible - before) childHit (index - before) later (by omega)
            rw [Tree.get, if_pos totalHit, if_neg (show ¬ offset + index < leftSize by omega)]
            have arithmetic : offset + index - leftSize = offset + before - leftSize + (index - before) := by omega
            rw [arithmetic]
            exact rejected
  | @periodic period unit positive phase size ih =>
    let start := (phase + offset) % period
    let visible := min count (size - offset)
    let before := min visible (period - start)
    have startBound : start < period := Nat.mod_lt _ positive
    have beforeBound : before ≤ period - start := Nat.min_le_right _ _
    have beforeVisible : before ≤ visible := Nat.min_le_left _ _
    have visibleBound : visible ≤ size - offset := Nat.min_le_right _ _
    simp only [Tree.firstWhere] at found
    split at found
    · contradiction
    · change (match unit.firstWhere test start before with
        | some hit => some hit
        | none => (unit.firstWhere test 0 (min period (visible - before))).map (before + ·)) = some hit at found
      cases first : unit.firstWhere test start before with
      | some childHit =>
        simp only [first, Option.some.injEq] at found
        subst hit
        have ⟨bound, _⟩ := unit.firstWhere_sound test start before childHit first
        have rejected := ih start before childHit index first earlier
        rw [Tree.get, if_pos (show offset + index < size by omega)]
        have arithmetic : (phase + (offset + index)) % period = start + index := by
          rw [← Nat.add_assoc, ← Nat.mod_add_mod (phase + offset) period index]
          exact Nat.mod_eq_of_lt (by omega)
        rw [arithmetic]
        exact rejected
      | none =>
        simp only [first] at found
        cases later : unit.firstWhere test 0 (min period (visible - before)) with
        | none => rw [later] at found; cases found
        | some childHit =>
          simp only [later, Option.map, Option.some.injEq] at found
          subst hit
          have ⟨bound, _⟩ := unit.firstWhere_sound test 0 (min period (visible - before)) childHit later
          have full : before = period - start := by dsimp [before] at *; omega
          have totalHit : offset + index < size := by omega
          rw [Tree.get, if_pos totalHit]
          by_cases early : index < before
          · have rejected := unit.firstWhere_none test start before index first (by omega)
            have arithmetic : (phase + (offset + index)) % period = start + index := by
              rw [← Nat.add_assoc, ← Nat.mod_add_mod (phase + offset) period index]
              exact Nat.mod_eq_of_lt (by omega)
            rw [arithmetic]
            exact rejected
          · have rejected := ih 0 (min period (visible - before)) childHit (index - before) later (by omega)
            have arithmetic : (phase + (offset + index)) % period = index - before := by
              rw [← Nat.add_assoc, ← Nat.mod_add_mod (phase + offset) period index]
              change (start + index) % period = index - before
              have wrap : start + index = period + (index - before) := by omega
              rw [wrap]
              simp [Nat.add_mod, Nat.mod_eq_of_lt (show index - before < period by omega)]
            rw [arithmetic]
            simpa only [Nat.zero_add] using rejected

theorem Tree.firstWhere_eq_some_iff {size : Nat} (tree : Tree size)
    (test : Option UInt8 → Bool) (offset count hit : Nat) :
    tree.firstWhere test offset count = some hit ↔
      hit < min count (size - offset) ∧ test (tree.get (offset + hit)) = true ∧
        ∀ index, index < hit → test (tree.get (offset + index)) = false := by
  constructor
  · intro found
    obtain ⟨inside, accepted⟩ := tree.firstWhere_sound test offset count hit found
    exact ⟨inside, accepted, fun index earlier =>
      tree.firstWhere_before test offset count hit index found earlier⟩
  · rintro ⟨inside, accepted, prior⟩
    cases result : tree.firstWhere test offset count with
    | none =>
      have rejected := tree.firstWhere_none test offset count hit result inside
      rw [rejected] at accepted
      contradiction
    | some first =>
      obtain ⟨_, firstAccepted⟩ := tree.firstWhere_sound test offset count first result
      have same : first = hit := by
        by_cases lower : first < hit
        · rw [prior first lower] at firstAccepted
          contradiction
        · by_cases greater : hit < first
          · have rejected := tree.firstWhere_before test offset count first hit result greater
            rw [rejected] at accepted
            contradiction
          · omega
      cases same
      rfl

/-- Equal extent and complete byte observations give identical scalar
    materialization, without identifying compact storage constructors. -/
theorem toList_eq_of_observations (left right : ByteImage)
    (extent : left.size = right.size) (bytes : ∀ index, left.get index = right.get index) :
    left.toList = right.toList := by
  unfold toList
  rw [extent]
  apply congrArg (fun read => List.map read (List.range right.size))
  funext index
  exact bytes index

/-- Equal observations survive arbitrary clipping, including empty slices
    beyond the source end. -/
theorem slice_get_eq_of_observations (left right : ByteImage)
    (extent : left.size = right.size) (bytes : ∀ index, left.get index = right.get index)
    (offset count index : Nat) :
    (left.slice offset count).get index = (right.slice offset count).get index := by
  by_cases inside : index < min count (right.size - offset)
  · rw [get_slice left offset count index (by omega) (by rw [extent]; omega),
      get_slice right offset count index (by omega) (by omega)]
    exact bytes (offset + index)
  · rw [get_outside _ index (by rw [size_slice,extent]; omega),
      get_outside _ index (by rw [size_slice]; omega)]

/-- Scalar reads of equal observed slices retain the exact same bytes. -/
theorem slice_toList_eq_of_observations (left right : ByteImage)
    (extent : left.size = right.size) (bytes : ∀ index, left.get index = right.get index)
    (offset count : Nat) :
    (left.slice offset count).toList = (right.slice offset count).toList :=
  toList_eq_of_observations _ _ (by rw [size_slice,size_slice,extent])
    (slice_get_eq_of_observations left right extent bytes offset count)

namespace WindowRuntime

private structure Window where
  original : ByteImage
  offset : Nat
  count : Nat

/-- Drop view wrappers and descend concatenations only when the complete
    bounded window belongs to one child. No observed bytes justify a period. -/
private def normalize {size : Nat} (tree : Tree size) (offset count : Nat) : Window :=
  let count := min count (size - offset)
  if count == 0 then ⟨⟨_, tree⟩, offset, count⟩ else
  match tree with
  | .view original start _ _ => normalize original (start + offset) count
  | .append (leftSize := leftSize) left right =>
    if offset + count ≤ leftSize then normalize left offset count
    else if leftSize ≤ offset then normalize right (offset - leftSize) count
    else ⟨⟨_, tree⟩, offset, count⟩
  | _ => ⟨⟨_, tree⟩, offset, count⟩

private def Window.image (window : Window) : ByteImage :=
  window.original.slice window.offset window.count

/-- The callback representation is part of the logical operation: strip
    enclosing views and wholly containing append branches, then retain exactly
    one bounded view. Constructor-observing callbacks receive this same
    canonical window in the specification and compiled traversal. -/
private def canonicalImage (image : ByteImage) : ByteImage :=
  (normalize image.tree 0 image.size).image
private theorem normalize_eq {size : Nat} (tree : Tree size) (offset count : Nat) :
    normalize tree offset count =
      let count := min count (size - offset)
      if count == 0 then ⟨⟨_, tree⟩, offset, count⟩ else
      match tree with
      | .view original start _ _ => normalize original (start + offset) count
      | .append (leftSize := leftSize) left right =>
        if offset + count ≤ leftSize then normalize left offset count
        else if leftSize ≤ offset then normalize right (offset - leftSize) count
        else ⟨⟨_, tree⟩, offset, count⟩
      | _ => ⟨⟨_, tree⟩, offset, count⟩ := by
  cases tree <;> rfl

private theorem normalize_empty {size : Nat} (tree : Tree size) (offset count : Nat)
    (empty : min count (size - offset) = 0) :
    normalize tree offset count = ⟨⟨size,tree⟩,offset,min count (size - offset)⟩ := by
  rw [normalize_eq]
  dsimp only
  rw [if_pos (by simp only [empty,beq_self_eq_true])]

private theorem own_window_observation {size : Nat} (tree : Tree size) (offset count : Nat) :
    (Window.image ⟨⟨size,tree⟩,offset,min count (size - offset)⟩).size = min count (size - offset) ∧
    ∀ index, index < min count (size - offset) →
      (Window.image ⟨⟨size,tree⟩,offset,min count (size - offset)⟩).get index = tree.get (offset + index) := by
  have bound := Nat.min_le_right count (size - offset)
  refine ⟨?_,?_⟩
  · rw [Window.image,size_slice]
    exact Nat.min_eq_left bound
  · intro index inside
    exact get_slice ⟨size,tree⟩ offset _ index inside (by change offset + index < size; omega)

private theorem normalize_observation {size : Nat} (tree : Tree size) (offset count : Nat) :
    (normalize tree offset count).image.size = min count (size - offset) ∧
    ∀ index, index < min count (size - offset) →
      (normalize tree offset count).image.get index = tree.get (offset + index) := by
  induction tree generalizing offset count with
  | fill size byte =>
    simpa only [normalize_eq,ite_self] using own_window_observation (.fill size byte) offset count
  | literal data =>
    simpa only [normalize_eq,ite_self] using own_window_observation (.literal data) offset count
  | source size read =>
    simpa only [normalize_eq,ite_self] using own_window_observation (.source size read) offset count
  | periodic unit positive phase size _ =>
    simpa only [normalize_eq,ite_self] using own_window_observation (.periodic unit positive phase size) offset count
  | @view sourceSize original start size sourceBound ih =>
    let clipped := min count (size - offset)
    have clippedBound : clipped ≤ size - offset := Nat.min_le_right _ _
    by_cases zero : clipped = 0
    · rw [normalize_empty _ offset count zero]
      exact own_window_observation (.view original start size sourceBound) offset count
    have originalBound : clipped ≤ sourceSize - (start + offset) := by omega
    have result := ih (start + offset) clipped
    rw [Nat.min_eq_left originalBound] at result
    have normalized : normalize (.view original start size sourceBound) offset count =
        normalize original (start + offset) clipped := by
      rw [normalize_eq]
      change (if clipped == 0 then _ else normalize original (start + offset) clipped) = _
      simp [zero]
    rw [normalized]
    refine ⟨result.1,?_⟩
    intro index inside
    rw [result.2 index inside]
    have inView : offset + index < size := by omega
    simp only [Tree.get,if_pos inView,Nat.add_assoc]
  | @append leftSize rightSize left right ihl ihr =>
    let clipped := min count (leftSize + rightSize - offset)
    have clippedBound : clipped ≤ leftSize + rightSize - offset := Nat.min_le_right _ _
    by_cases zero : clipped = 0
    · rw [normalize_empty _ offset count zero]
      exact own_window_observation (.append left right) offset count
    by_cases inLeft : offset + clipped ≤ leftSize
    · have leftBound : clipped ≤ leftSize - offset := by omega
      have result := ihl offset clipped
      rw [Nat.min_eq_left leftBound] at result
      have normalized : normalize (.append left right) offset count = normalize left offset clipped := by
        rw [normalize_eq]
        change (if clipped == 0 then _ else if offset + clipped ≤ leftSize then _ else _) = _
        simp [zero,inLeft] <;> rfl
      rw [normalized]
      refine ⟨result.1,?_⟩
      intro index inside
      rw [result.2 index inside]
      have insideAll : offset + index < leftSize + rightSize := by omega
      have insideLeft : offset + index < leftSize := by omega
      simp only [Tree.get,if_pos insideAll,if_pos insideLeft]
    · by_cases inRight : leftSize ≤ offset
      · have rightBound : clipped ≤ rightSize - (offset - leftSize) := by omega
        have result := ihr (offset - leftSize) clipped
        rw [Nat.min_eq_left rightBound] at result
        have normalized : normalize (.append left right) offset count = normalize right (offset - leftSize) clipped := by
          rw [normalize_eq]
          change (if clipped == 0 then _ else if offset + clipped ≤ leftSize then _ else if leftSize ≤ offset then _ else _) = _
          simp [zero,inLeft,inRight] <;> rfl
        rw [normalized]
        refine ⟨result.1,?_⟩
        intro index inside
        rw [result.2 index inside]
        have insideAll : offset + index < leftSize + rightSize := by omega
        have notLeft : ¬ offset + index < leftSize := by omega
        simp only [Tree.get,if_pos insideAll,if_neg notLeft]
        congr 1
        omega
      · have normalized : normalize (.append left right) offset count =
            ⟨⟨leftSize + rightSize,.append left right⟩,offset,clipped⟩ := by
          rw [normalize_eq]
          change (if clipped == 0 then _ else if offset + clipped ≤ leftSize then _ else if leftSize ≤ offset then _ else _) = _
          simp [zero,inLeft,inRight] <;> rfl
        rw [normalized]
        exact own_window_observation (.append left right) offset count

/-- Canonicalization preserves the complete logical byte extent, including
    empty images and externally supplied sources. -/
theorem canonicalImage_size (image : ByteImage) : (canonicalImage image).size = image.size := by
  have result := (normalize_observation image.tree 0 image.size).1
  simpa only [canonicalImage,Nat.sub_zero,Nat.min_self] using result

/-- Every observed byte is preserved, including absent padding and every
    out-of-range lookup. This is not structural image equality. -/
theorem canonicalImage_get (image : ByteImage) (index : Nat) :
    (canonicalImage image).get index = image.get index := by
  by_cases inside : index < image.size
  · have result := (normalize_observation image.tree 0 image.size).2 index
    simpa only [Nat.sub_zero,Nat.min_self,Nat.zero_add] using result (by simpa only [Nat.sub_zero,Nat.min_self] using inside)
  · rw [get_outside _ index (by rw [canonicalImage_size]; omega),get_outside image index (by omega)]

/-- Scalar materialization sees exactly the original bytes after callback
    window canonicalization; no callback extensionality premise is introduced. -/
theorem canonicalImage_toList (image : ByteImage) : (canonicalImage image).toList = image.toList := by
  unfold toList
  rw [canonicalImage_size]
  apply congrArg (fun read => List.map read (List.range image.size))
  funext index
  exact canonicalImage_get image index

/-- Cropping after canonicalization preserves every requested observation,
    including requests clipped by either endpoint of the image. -/
theorem canonicalImage_slice_get (image : ByteImage) (offset count index : Nat) :
    ((canonicalImage image).slice offset count).get index = (image.slice offset count).get index := by
  by_cases inside : index < min count (image.size - offset)
  · have inCount : index < count := by omega
    have inSource : offset + index < image.size := by omega
    rw [get_slice _ offset count index inCount (by rw [canonicalImage_size]; exact inSource),
      get_slice image offset count index inCount inSource,canonicalImage_get]
  · rw [get_outside _ index (by rw [size_slice,canonicalImage_size]; omega),
      get_outside _ index (by rw [size_slice]; omega)]

/-- Scalar callbacks on recursively cropped canonical windows receive exactly
    the materialized source slice, without equating image constructors. -/
theorem canonicalImage_slice_toList (image : ByteImage) (offset count : Nat) :
    ((canonicalImage image).slice offset count).toList = (image.slice offset count).toList := by
  simp only [toList,size_slice,canonicalImage_size]
  apply congrArg (fun read => List.map read (List.range (min count (image.size - offset))))
  funext index
  exact canonicalImage_slice_get image offset count index

private abbrev Key := Nat × USize × Nat × Nat
structure Stats where
  visits : Nat := 0
  hits : Nat := 0
  deriving Repr
private structure SearchCache where
  memo : trustIrHashMap Key (Option Nat × Window) := ∅
  stats : Stats := {}


end WindowRuntime

@[nospecialize, trustIrExtern 2 "l_TrustIr_ByteImage_firstWhere(#1, #2)"]
def firstWhere (test : Option UInt8 → Bool) (image : ByteImage) : Option Nat :=
  image.tree.firstWhere test 0 image.size

theorem firstWhere_sound (test : Option UInt8 → Bool) (image : ByteImage) (hit : Nat)
    (found : image.firstWhere test = some hit) :
    hit < image.size ∧ test (image.get hit) = true := by
  simpa only [Nat.sub_zero, Nat.min_self, Nat.zero_add] using
    image.tree.firstWhere_sound test 0 image.size hit found

theorem firstWhere_eq_none_iff (test : Option UInt8 → Bool) (image : ByteImage) :
    image.firstWhere test = none ↔
      ∀ index, index < image.size → test (image.get index) = false := by
  simpa only [Nat.sub_zero, Nat.min_self, Nat.zero_add] using
    image.tree.firstWhere_eq_none_iff test 0 image.size

theorem firstWhere_eq_some_iff (test : Option UInt8 → Bool) (image : ByteImage) (hit : Nat) :
    image.firstWhere test = some hit ↔
      hit < image.size ∧ test (image.get hit) = true ∧
        ∀ index, index < hit → test (image.get index) = false := by
  simpa only [Nat.sub_zero, Nat.min_self, Nat.zero_add] using
    image.tree.firstWhere_eq_some_iff test 0 image.size hit

/-- An exact periodic window derived solely from the retained constructors.
    Source functions and literals supply no repetition certificate. -/
def Tree.periodicWindow {size : Nat} (tree : Tree size) (offset count : Nat) :
    Option (ByteImage × Nat) :=
  if offset + count > size then none else
  match tree with
  | .fill _ byte => some (ByteImage.fill 1 byte, 0)
  | .periodic (period := period) unit _ phase _ => some (⟨period, unit⟩, (phase + offset) % period)
  | .view original start _ _ => original.periodicWindow (start + offset) count
  | .append (leftSize := leftSize) left right =>
    if offset + count ≤ leftSize then left.periodicWindow offset count
    else if leftSize ≤ offset then right.periodicWindow (offset - leftSize) count
    else none
  | .literal _ | .source _ _ => none

def periodicWindow (image : ByteImage) : Option (ByteImage × Nat) :=
  image.tree.periodicWindow 0 image.size

private structure BlockEntry (α : Type) where
  phase : Nat
  values : CompactArray.Packed α

private def cachedBlocks {α : Type} (phase count : Nat) :
    List (BlockEntry α) → Option (CompactArray.Tree α count)
  | [] => none
  | entry :: rest =>
    if entry.phase == phase then
      if h : entry.values.size = count then some (h ▸ entry.values.tree)
      else cachedBlocks phase count rest
    else cachedBlocks phase count rest

/-- The cache belongs to one immutable template, block width and callback.
    Keys identify exact byte phase and output extent, never pointer identity.
    Left-to-right evaluation preserves the first error of the logical map. -/
private def periodicBlocks {α ε : Type} (decode : ByteImage → Except ε α)
    (unit : ByteImage) (positive : 0 < unit.size) (width phase count : Nat) :
    StateT (List (BlockEntry α)) (Except ε) (CompactArray.Tree α count) := do
  if let some tree := cachedBlocks phase count (← getThe (List (BlockEntry α))) then return tree
  let tree ←
    if width % unit.size = 0 then do
      if hzero : count = 0 then pure (hzero ▸ CompactArray.Tree.dense (by omega) .nil)
      else
        let value ← liftM (decode ⟨width, .periodic unit.tree positive phase width⟩)
        pure (.uniform count value)
    else if hzero : count = 0 then pure (hzero ▸ CompactArray.Tree.dense (by omega) .nil)
    else if shorter : unit.size / Nat.gcd unit.size width < count then do
      let period := unit.size / Nat.gcd unit.size width
      let values ← periodicBlocks decode unit positive width phase period
      pure (.periodic values (Nat.div_gcd_pos_of_pos_left width positive) 0 count)
    else if hone : count = 1 then do
      let value ← liftM (decode ⟨width, .periodic unit.tree positive phase width⟩)
      pure (hone ▸ CompactArray.Tree.uniform 1 value)
    else do
      let left ← periodicBlocks decode unit positive width phase (count / 2)
      let right ← periodicBlocks decode unit positive width
        ((phase + (count / 2) * width) % unit.size) (count - count / 2)
      pure (.split (by omega) left right)
  modify (fun entries => { phase, values := ⟨count, tree⟩ } :: entries)
  return tree
termination_by count

/-- A callback's result predicate and permitted error set, propagated through
compressed traversal without imposing successful decoding. -/
def BlockResult {α ε : Type} (valid : α → Prop) (error : ε → Prop) : Except ε α → Prop
  | .ok value => valid value
  | .error failure => error failure

theorem BlockResult.bind {α β ε : Type} (valid : α → Prop) (nextValid : β → Prop) (error : ε → Prop)
    (action : Except ε α) (next : α → Except ε β) (first : BlockResult valid error action)
    (rest : ∀ value, valid value → BlockResult nextValid error (next value)) :
    BlockResult nextValid error (action >>= next) := by
  cases action with
  | ok value => exact rest value first
  | error failure => exact first

theorem BlockResult.error_of_eq {α ε : Type} (valid : α → Prop) (error : ε → Prop)
    (result : Except ε α) (failure : ε) (held : BlockResult valid error result)
    (same : result = .error failure) : error failure := by
  rw [same] at held
  exact held

/-- Logical lookup validity includes every retained compact-array shape. -/
def BlockTreeValid {α : Type} (valid : α → Prop) {size : Nat} (tree : CompactArray.Tree α size) : Prop :=
  ∀ index value, tree.get? index = some value → valid value

theorem BlockTreeValid.uniform {α : Type} (valid : α → Prop) (count : Nat) (value : α) (held : valid value) :
    BlockTreeValid valid (.uniform count value) := by
  intro index child found
  simp only [CompactArray.Tree.get?] at found
  split at found
  · cases found; exact held
  · cases found

theorem BlockTreeValid.empty {α : Type} (valid : α → Prop) :
    BlockTreeValid valid (CompactArray.Tree.dense (by omega) (.nil : CompactArray.Leaf α 0)) := by
  intro index value found
  cases found

theorem BlockTreeValid.split {α : Type} (valid : α → Prop) {size : Nat} (large : 2 ≤ size)
    (left : CompactArray.Tree α (size / 2)) (right : CompactArray.Tree α (size - size / 2))
    (first : BlockTreeValid valid left) (second : BlockTreeValid valid right) :
    BlockTreeValid valid (.split large left right) := by
  intro index value found
  simp only [CompactArray.Tree.get?] at found
  split at found
  · exact first _ _ found
  · exact second _ _ found

theorem BlockTreeValid.periodic {α : Type} (valid : α → Prop) {period : Nat}
    (unit : CompactArray.Tree α period) (positive : 0 < period) (phase count : Nat)
    (held : BlockTreeValid valid unit) : BlockTreeValid valid (.periodic unit positive phase count) := by
  intro index value found
  simp only [CompactArray.Tree.get?] at found
  split at found
  · exact held _ _ found
  · cases found

private def BlockCacheValid {α : Type} (valid : α → Prop) (entries : List (BlockEntry α)) : Prop :=
  ∀ entry ∈ entries, BlockTreeValid valid entry.values.tree

private theorem cachedBlocks_valid {α : Type} (valid : α → Prop) (phase count : Nat)
    (entries : List (BlockEntry α)) (safe : BlockCacheValid valid entries)
    (tree : CompactArray.Tree α count) (found : cachedBlocks phase count entries = some tree) :
    BlockTreeValid valid tree := by
  induction entries with
  | nil => cases found
  | cons entry rest ih =>
    have first := safe entry (by simp)
    have later : BlockCacheValid valid rest := fun held member => safe held (List.mem_cons_of_mem _ member)
    simp only [cachedBlocks] at found
    split at found
    · split at found
      · rename_i same
        cases same
        cases found
        exact first
      · exact ih later found
    · exact ih later found

private def BlockStateResult {σ α ε : Type} (stateValid : σ → Prop) (valid : α → Prop)
    (error : ε → Prop) (action : StateT σ (Except ε) α) : Prop :=
  ∀ state, stateValid state → BlockResult (fun pair => valid pair.1 ∧ stateValid pair.2) error (action.run state)

private theorem BlockStateResult.bind {σ α β ε : Type} (stateValid : σ → Prop)
    (valid : α → Prop) (nextValid : β → Prop) (error : ε → Prop)
    (action : StateT σ (Except ε) α) (next : α → StateT σ (Except ε) β)
    (first : BlockStateResult stateValid valid error action)
    (rest : ∀ value, valid value → BlockStateResult stateValid nextValid error (next value)) :
    BlockStateResult stateValid nextValid error (action >>= next) := by
  intro state safe
  change BlockResult (fun pair => nextValid pair.1 ∧ stateValid pair.2) error
    (action.run state >>= fun pair => (next pair.1).run pair.2)
  apply BlockResult.bind (fun pair : α × σ => valid pair.1 ∧ stateValid pair.2)
    (fun pair : β × σ => nextValid pair.1 ∧ stateValid pair.2) error
    (action.run state) (fun pair => (next pair.1).run pair.2) (first state safe)
  intro pair held
  exact rest pair.1 held.1 pair.2 held.2

private theorem BlockStateResult.lift {σ α ε : Type} (stateValid : σ → Prop) (valid : α → Prop)
    (error : ε → Prop) (result : Except ε α) (held : BlockResult valid error result) :
    BlockStateResult stateValid valid error (liftM result) := by
  intro state safe
  cases result with
  | error failure => exact held
  | ok value => exact ⟨held,safe⟩

private theorem BlockStateResult.pure {σ α ε : Type} (stateValid : σ → Prop) (valid : α → Prop)
    (error : ε → Prop) (value : α) (held : valid value) :
    BlockStateResult stateValid valid error (pure value) := by
  intro state safe
  exact ⟨held,safe⟩

private theorem block_state_pure_bind {σ α β ε : Type} (value : α) (next : α → StateT σ (Except ε) β) :
    StateT.bind (StateT.pure value) next = next value := by
  funext state
  rfl

private theorem block_state_bind_assoc {σ α β γ ε : Type} (action : StateT σ (Except ε) α)
    (next : α → StateT σ (Except ε) β) (last : β → StateT σ (Except ε) γ) :
    StateT.bind (StateT.bind action next) last = StateT.bind action (fun value => StateT.bind (next value) last) := by
  funext state
  cases executed : action state <;> simp [StateT.bind,executed,bind,Except.bind]

private theorem block_lift_run {σ α ε : Type} (result : Except ε α) (state : σ) :
    (liftM result : StateT σ (Except ε) α) state = result >>= fun value => .ok (value,state) := rfl

private theorem block_modify_run {σ ε : Type} (update : σ → σ) (state : σ) :
    (modify update : StateT σ (Except ε) Unit) state = .ok ((),update state) := rfl

private theorem block_except_assoc {α β γ ε : Type} (action : Except ε α)
    (next : α → Except ε β) (last : β → Except ε γ) :
    Except.bind (Except.bind action next) last = Except.bind action (fun value => Except.bind (next value) last) := by
  cases action <;> rfl

private theorem block_except_ok_bind {α β ε : Type} (value : α) (next : α → Except ε β) :
    Except.bind (.ok value) next = next value := rfl

private theorem periodicBlocks_valid {α ε : Type} (valid : α → Prop) (error : ε → Prop)
    (decode : ByteImage → Except ε α) (callbacks : ∀ image, BlockResult valid error (decode image))
    (unit : ByteImage) (positive : 0 < unit.size) (width phase count : Nat) :
    BlockStateResult (BlockCacheValid valid) (BlockTreeValid valid) error
      (periodicBlocks decode unit positive width phase count) := by
  induction count using trustIrNatStrongInduction generalizing phase with
  | ind count ih =>
    intro entries safe
    rw [periodicBlocks]
    have getter : (getThe (List (BlockEntry α)) : StateT (List (BlockEntry α)) (Except ε) (List (BlockEntry α))) entries = .ok (entries,entries) := rfl
    simp only [StateT.bind,StateT.get,StateT.pure,StateT.run,getter,bind,pure,Except.bind,Except.pure]
    cases cached : cachedBlocks phase count entries with
    | some tree =>
      exact ⟨cachedBlocks_valid valid phase count entries safe tree cached,safe⟩
    | none =>
      let building : StateT (List (BlockEntry α)) (Except ε) (CompactArray.Tree α count) := (do
          if width % unit.size = 0 then do
            if hzero : count = 0 then pure (hzero ▸ CompactArray.Tree.dense (by omega) .nil)
            else
              let value ← liftM (decode ⟨width, .periodic unit.tree positive phase width⟩)
              pure (.uniform count value)
          else if hzero : count = 0 then pure (hzero ▸ CompactArray.Tree.dense (by omega) .nil)
          else if _shorter : unit.size / Nat.gcd unit.size width < count then do
            let period := unit.size / Nat.gcd unit.size width
            let values ← periodicBlocks decode unit positive width phase period
            pure (.periodic values (Nat.div_gcd_pos_of_pos_left width positive) 0 count)
          else if hone : count = 1 then do
            let value ← liftM (decode ⟨width, .periodic unit.tree positive phase width⟩)
            pure (hone ▸ CompactArray.Tree.uniform 1 value)
          else do
            let left ← periodicBlocks decode unit positive width phase (count / 2)
            let right ← periodicBlocks decode unit positive width
              ((phase + (count / 2) * width) % unit.size) (count - count / 2)
            pure (.split (by omega) left right))
      have body : BlockStateResult (BlockCacheValid valid) (BlockTreeValid valid) error building := by
        dsimp only [building]
        split
        · split
          · rename_i zero; subst count
            exact BlockStateResult.pure _ _ _ _ (BlockTreeValid.empty valid)
          · apply BlockStateResult.bind _ valid _ _ _ _ (BlockStateResult.lift _ _ _ _ (callbacks _))
            intro value held
            exact BlockStateResult.pure _ _ _ _ (BlockTreeValid.uniform valid count value held)
        · split
          · rename_i zero; subst count
            exact BlockStateResult.pure _ _ _ _ (BlockTreeValid.empty valid)
          · split
            · rename_i shorter
              apply BlockStateResult.bind _ (BlockTreeValid valid) _ _ _ _ (ih _ shorter phase)
              intro values held
              exact BlockStateResult.pure _ _ _ _ (BlockTreeValid.periodic valid _ _ _ _ held)
            · split
              · rename_i one; subst count
                apply BlockStateResult.bind _ valid _ _ _ _ (BlockStateResult.lift _ _ _ _ (callbacks _))
                intro value held
                exact BlockStateResult.pure _ _ _ _ (BlockTreeValid.uniform valid 1 value held)
              · apply BlockStateResult.bind _ (BlockTreeValid valid) _ _ _ _ (ih _ (by omega) phase)
                intro left first
                apply BlockStateResult.bind _ (BlockTreeValid valid) _ _ _ _ (ih _ (by omega) _)
                intro right second
                exact BlockStateResult.pure _ _ _ _ (BlockTreeValid.split valid _ _ _ first second)
      have finish_state (tree : CompactArray.Tree α count) (held : BlockTreeValid valid tree) :
          BlockStateResult (BlockCacheValid valid) (BlockTreeValid valid) error (do
            modify (fun entries => { phase, values := ⟨count,tree⟩ } :: entries)
            pure tree) := by
        intro cache cacheValid
        change BlockTreeValid valid tree ∧ BlockCacheValid valid ({ phase,values := ⟨count,tree⟩ } :: cache)
        refine ⟨held,?_⟩
        intro entry member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact held
        · exact cacheValid entry member
      have finished := (BlockStateResult.bind (BlockCacheValid valid) (BlockTreeValid valid)
        (BlockTreeValid valid) error building _ body finish_state) entries safe
      cases decoding : decode ⟨width, .periodic unit.tree positive phase width⟩ <;>
        by_cases divided : width % unit.size = 0 <;>
          by_cases zero : count = 0 <;>
            by_cases shorter : unit.size / Nat.gcd unit.size width < count <;>
              by_cases one : count = 1 <;>
                simp_all [building,block_state_pure_bind,block_state_bind_assoc,pure_bind,bind_assoc,
                  StateT.bind,StateT.pure,StateT.run,StateT.lift,block_lift_run,block_modify_run,
                  bind,pure,Except.bind,Except.pure,block_except_assoc] <;>
                  (simp only [← Except.bind.eq_def,block_except_assoc,block_except_ok_bind] at finished ⊢
                   first
                   | exact finished
                   | (split <;> try omega
                      all_goals simp_all [StateT.bind,StateT.pure,StateT.run,block_lift_run,block_modify_run,
                       bind,pure,Except.bind,Except.pure] <;>
                       (simp only [← Except.bind.eq_def,block_except_assoc,block_except_ok_bind] at finished ⊢; exact finished)))


/-- An actual successful callback, together with the complete observations of
    the image it received. Callback constructor sensitivity is unrestricted. -/
def BlockDecoded {α ε : Type} (decode : ByteImage → Except ε α) (width : Nat)
    (read : Nat → Option UInt8) (value : α) : Prop :=
  ∃ image, image.size = width ∧ (∀ index, index < width → image.get index = read index) ∧
    decode image = .ok value

private abbrev PhaseDecoded {α ε : Type} (decode : ByteImage → Except ε α)
    (unit : ByteImage) (width phase : Nat) (value : α) : Prop :=
  BlockDecoded decode width (fun index => unit.get ((phase + index) % unit.size)) value

private def PhaseSlots {α ε : Type} (decode : ByteImage → Except ε α)
    (unit : ByteImage) (width phase : Nat) {count : Nat} (tree : CompactArray.Tree α count) : Prop :=
  ∀ index value, index < count → tree.get? index = some value →
    PhaseDecoded decode unit width (phase + index * width) value

private theorem phase_decoded_congr {α ε : Type} (decode : ByteImage → Except ε α)
    (unit : ByteImage) (width first second : Nat) (value : α)
    (same : first % unit.size = second % unit.size)
    (held : PhaseDecoded decode unit width first value) : PhaseDecoded decode unit width second value := by
  obtain ⟨image,extent,bytes,run⟩ := held
  refine ⟨image,extent,?_,run⟩
  intro index inside
  rw [bytes index inside]
  change unit.get ((first + index) % unit.size) = unit.get ((second + index) % unit.size)
  apply congrArg unit.get
  rw [Nat.add_mod first index,Nat.add_mod second index,same]

private theorem phase_slots_empty {α ε : Type} (decode : ByteImage → Except ε α)
    (unit : ByteImage) (width phase : Nat) (tree : CompactArray.Tree α 0) :
    PhaseSlots decode unit width phase tree := by
  intro index value inside
  omega

private theorem phase_slots_uniform {α ε : Type} (decode : ByteImage → Except ε α)
    (unit : ByteImage) (width phase count : Nat) (value : α)
    (divided : width % unit.size = 0) (held : PhaseDecoded decode unit width phase value) :
    PhaseSlots decode unit width phase (.uniform count value) := by
  intro index selected inside found
  simp only [CompactArray.Tree.get?,if_pos inside,Option.some.injEq] at found
  subst selected
  apply phase_decoded_congr decode unit width phase (phase + index * width) value _ held
  rw [Nat.add_mod,Nat.mul_mod,divided,Nat.mul_zero,Nat.zero_mod,Nat.add_zero,Nat.mod_mod]

private theorem phase_slots_single {α ε : Type} (decode : ByteImage → Except ε α)
    (unit : ByteImage) (width phase : Nat) (value : α)
    (held : PhaseDecoded decode unit width phase value) :
    PhaseSlots decode unit width phase (.uniform 1 value) := by
  intro index selected inside found
  have zero : index = 0 := by omega
  subst index
  simp only [CompactArray.Tree.get?,if_pos inside,Option.some.injEq] at found
  subst selected
  simpa only [Nat.zero_mul,Nat.add_zero] using held

private theorem phase_slots_periodic
    (cycleLaw : ∀ period width phase index : Nat,
      (phase + (index % (period / Nat.gcd period width)) * width) % period =
        (phase + index * width) % period)
    {α ε : Type} (decode : ByteImage → Except ε α) (unit : ByteImage) (positive : 0 < unit.size)
    (width phase count : Nat)
    (values : CompactArray.Tree α (unit.size / Nat.gcd unit.size width))
    (held : PhaseSlots decode unit width phase values) :
    PhaseSlots decode unit width phase
      (.periodic values (Nat.div_gcd_pos_of_pos_left width positive) 0 count) := by
  intro index value inside found
  simp only [CompactArray.Tree.get?,if_pos inside,Nat.zero_add] at found
  have cyclePositive := Nat.div_gcd_pos_of_pos_left width positive
  have selected := held (index % (unit.size / Nat.gcd unit.size width)) value
    (Nat.mod_lt _ cyclePositive) found
  exact phase_decoded_congr decode unit width _ _ value (cycleLaw unit.size width phase index) selected

private theorem phase_slots_split {α ε : Type} (decode : ByteImage → Except ε α)
    (unit : ByteImage) (width phase count : Nat) (large : 2 ≤ count)
    (left : CompactArray.Tree α (count / 2)) (right : CompactArray.Tree α (count - count / 2))
    (first : PhaseSlots decode unit width phase left)
    (second : PhaseSlots decode unit width ((phase + (count / 2) * width) % unit.size) right) :
    PhaseSlots decode unit width phase (.split large left right) := by
  intro index value inside found
  by_cases before : index < count / 2
  · simp only [CompactArray.Tree.get?,if_pos before] at found
    exact first index value before found
  · simp only [CompactArray.Tree.get?,if_neg before] at found
    have selected := second (index - count / 2) value (by omega) found
    apply phase_decoded_congr decode unit width _ _ value _ selected
    rw [Nat.mod_add_mod]
    have position : phase + count / 2 * width + (index - count / 2) * width = phase + index * width := by
      have sum : count / 2 + (index - count / 2) = index := by omega
      rw [Nat.add_assoc,← Nat.add_mul,sum]
    rw [position]

private def PhaseCache {α ε : Type} (decode : ByteImage → Except ε α)
    (unit : ByteImage) (width : Nat) (entries : List (BlockEntry α)) : Prop :=
  ∀ entry ∈ entries, PhaseSlots decode unit width entry.phase entry.values.tree

private theorem cachedBlocks_phase {α ε : Type} (decode : ByteImage → Except ε α)
    (unit : ByteImage) (width phase count : Nat) (entries : List (BlockEntry α))
    (safe : PhaseCache decode unit width entries) (tree : CompactArray.Tree α count)
    (found : cachedBlocks phase count entries = some tree) : PhaseSlots decode unit width phase tree := by
  induction entries with
  | nil => cases found
  | cons entry rest ih =>
    have first := safe entry (by simp)
    have later : PhaseCache decode unit width rest := fun held member => safe held (List.mem_cons_of_mem _ member)
    simp only [cachedBlocks] at found
    split at found
    · rename_i phaseMatches
      have samePhase : entry.phase = phase := by simpa only [beq_iff_eq] using phaseMatches
      split at found
      · rename_i sameSize
        cases sameSize
        cases found
        simpa only [samePhase] using first
      · exact ih later found
    · exact ih later found

private theorem periodic_callback_witness {α ε : Type} (decode : ByteImage → Except ε α)
    (unit : ByteImage) (positive : 0 < unit.size) (width phase : Nat) :
    BlockResult (PhaseDecoded decode unit width phase) (fun _ : ε => True)
      (decode ⟨width,.periodic unit.tree positive phase width⟩) := by
  cases run : decode ⟨width,.periodic unit.tree positive phase width⟩ with
  | error failure => exact True.intro
  | ok value =>
    refine ⟨⟨width,.periodic unit.tree positive phase width⟩,rfl,?_,run⟩
    intro index inside
    simp only [get,Tree.get,if_pos inside]

private theorem periodicBlocks_phase
    (cycleLaw : ∀ period width phase index : Nat,
      (phase + (index % (period / Nat.gcd period width)) * width) % period =
        (phase + index * width) % period)
    {α ε : Type} (decode : ByteImage → Except ε α)
    (unit : ByteImage) (positive : 0 < unit.size) (width phase count : Nat) :
    BlockStateResult (PhaseCache decode unit width) (PhaseSlots decode unit width phase) (fun _ : ε => True)
      (periodicBlocks decode unit positive width phase count) := by
  induction count using trustIrNatStrongInduction generalizing phase with
  | ind count ih =>
    intro entries safe
    rw [periodicBlocks]
    have getter : (getThe (List (BlockEntry α)) : StateT (List (BlockEntry α)) (Except ε) (List (BlockEntry α))) entries = .ok (entries,entries) := rfl
    simp only [StateT.bind,StateT.get,StateT.pure,StateT.run,getter,bind,pure,Except.bind,Except.pure]
    cases cached : cachedBlocks phase count entries with
    | some tree =>
      exact ⟨cachedBlocks_phase decode unit width phase count entries safe tree cached,safe⟩
    | none =>
      let building : StateT (List (BlockEntry α)) (Except ε) (CompactArray.Tree α count) := (do
          if width % unit.size = 0 then do
            if hzero : count = 0 then pure (hzero ▸ CompactArray.Tree.dense (by omega) .nil)
            else
              let value ← liftM (decode ⟨width, .periodic unit.tree positive phase width⟩)
              pure (.uniform count value)
          else if hzero : count = 0 then pure (hzero ▸ CompactArray.Tree.dense (by omega) .nil)
          else if _shorter : unit.size / Nat.gcd unit.size width < count then do
            let period := unit.size / Nat.gcd unit.size width
            let values ← periodicBlocks decode unit positive width phase period
            pure (.periodic values (Nat.div_gcd_pos_of_pos_left width positive) 0 count)
          else if hone : count = 1 then do
            let value ← liftM (decode ⟨width, .periodic unit.tree positive phase width⟩)
            pure (hone ▸ CompactArray.Tree.uniform 1 value)
          else do
            let left ← periodicBlocks decode unit positive width phase (count / 2)
            let right ← periodicBlocks decode unit positive width
              ((phase + (count / 2) * width) % unit.size) (count - count / 2)
            pure (.split (by omega) left right))
      have body : BlockStateResult (PhaseCache decode unit width) (PhaseSlots decode unit width phase) (fun _ : ε => True) building := by
        dsimp only [building]
        split
        · split
          · rename_i zero; subst count
            exact BlockStateResult.pure _ _ _ _ (phase_slots_empty decode unit width phase _)
          · apply BlockStateResult.bind _ (PhaseDecoded decode unit width phase) _ _ _ _
              (BlockStateResult.lift _ _ _ _ (periodic_callback_witness decode unit positive width phase))
            intro value held
            exact BlockStateResult.pure _ _ _ _ (phase_slots_uniform decode unit width phase count value (by assumption) held)
        · split
          · rename_i zero; subst count
            exact BlockStateResult.pure _ _ _ _ (phase_slots_empty decode unit width phase _)
          · split
            · rename_i shorter
              apply BlockStateResult.bind _ (PhaseSlots decode unit width phase) _ _ _ _ (ih _ shorter phase)
              intro values held
              exact BlockStateResult.pure _ _ _ _ (phase_slots_periodic cycleLaw decode unit positive width phase count values held)
            · split
              · rename_i one; subst count
                apply BlockStateResult.bind _ (PhaseDecoded decode unit width phase) _ _ _ _
                  (BlockStateResult.lift _ _ _ _ (periodic_callback_witness decode unit positive width phase))
                intro value held
                exact BlockStateResult.pure _ _ _ _ (phase_slots_single decode unit width phase value held)
              · apply BlockStateResult.bind _ (PhaseSlots decode unit width phase) _ _ _ _ (ih _ (by omega) phase)
                intro left first
                apply BlockStateResult.bind _ (PhaseSlots decode unit width ((phase + (count / 2) * width) % unit.size)) _ _ _ _ (ih _ (by omega) _)
                intro right second
                exact BlockStateResult.pure _ _ _ _ (phase_slots_split decode unit width phase count _ left right first second)
      have finish_state (tree : CompactArray.Tree α count) (held : PhaseSlots decode unit width phase tree) :
          BlockStateResult (PhaseCache decode unit width) (PhaseSlots decode unit width phase) (fun _ : ε => True) (do
            modify (fun entries => { phase, values := ⟨count,tree⟩ } :: entries)
            pure tree) := by
        intro cache cacheValid
        change PhaseSlots decode unit width phase tree ∧ PhaseCache decode unit width ({ phase,values := ⟨count,tree⟩ } :: cache)
        refine ⟨held,?_⟩
        intro entry member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact held
        · exact cacheValid entry member
      have finished := (BlockStateResult.bind (PhaseCache decode unit width) (PhaseSlots decode unit width phase)
        (PhaseSlots decode unit width phase) (fun _ : ε => True) building _ body finish_state) entries safe
      cases decoding : decode ⟨width, .periodic unit.tree positive phase width⟩ <;>
        by_cases divided : width % unit.size = 0 <;>
          by_cases zero : count = 0 <;>
            by_cases shorter : unit.size / Nat.gcd unit.size width < count <;>
              by_cases one : count = 1 <;>
                simp_all [building,block_state_pure_bind,block_state_bind_assoc,pure_bind,bind_assoc,
                  StateT.bind,StateT.pure,StateT.run,StateT.lift,block_lift_run,block_modify_run,
                  bind,pure,Except.bind,Except.pure,block_except_assoc] <;>
                  (simp only [← Except.bind.eq_def,block_except_assoc,block_except_ok_bind] at finished ⊢
                   first
                   | exact finished
                   | (split <;> try omega
                      all_goals simp_all [StateT.bind,StateT.pure,StateT.run,block_lift_run,block_modify_run,
                       bind,pure,Except.bind,Except.pure] <;>
                       (simp only [← Except.bind.eq_def,block_except_assoc,block_except_ok_bind] at finished ⊢; exact finished)))

/-- Each in-range output slot retains its actual callback and the input bytes
    at the corresponding source offset. Compact tree shape is immaterial. -/
def DecodedSlots {α ε : Type} (decode : ByteImage → Except ε α) (source : ByteImage)
    (width : Nat) {count : Nat} (tree : CompactArray.Tree α count) : Prop :=
  ∀ slot value, slot < count → tree.get? slot = some value →
    BlockDecoded decode width (fun index => source.get (slot * width + index)) value

private theorem slot_byte_bound (width count slot index : Nat) (inside : slot < count)
    (inByte : index < width) : slot * width + index < width * count := by
  have bound := Nat.mul_le_mul_right width (show slot + 1 ≤ count by omega)
  rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm count width] at bound
  omega

private theorem decoded_slots_congr {α ε : Type} (decode : ByteImage → Except ε α)
    (first second : ByteImage) (width : Nat) {count : Nat} (tree : CompactArray.Tree α count)
    (same : ∀ index, first.get index = second.get index)
    (held : DecodedSlots decode first width tree) : DecodedSlots decode second width tree := by
  intro slot value inside found
  obtain ⟨image,extent,bytes,run⟩ := held slot value inside found
  exact ⟨image,extent,fun index inByte => (bytes index inByte).trans (same _),run⟩

private theorem decoded_slots_empty {α ε : Type} (decode : ByteImage → Except ε α)
    (source : ByteImage) (width : Nat) (tree : CompactArray.Tree α 0) : DecodedSlots decode source width tree := by
  intro slot value inside
  omega

private theorem decoded_slots_zero {α ε : Type} (decode : ByteImage → Except ε α)
    (source : ByteImage) (width count : Nat) (zero : width = 0) (value : α)
    (run : decode empty = .ok value) : DecodedSlots decode source width (.uniform count value) := by
  intro slot selected inside found
  simp only [CompactArray.Tree.get?,if_pos inside,Option.some.injEq] at found
  subst selected
  refine ⟨empty,by simp only [zero,ByteImage.empty],?_,run⟩
  intro index inByte
  omega

private theorem decoded_slots_single {α ε : Type} (decode : ByteImage → Except ε α)
    (source : ByteImage) (width : Nat) (extent : source.size = width) (value : α)
    (run : decode (source.slice 0 width) = .ok value) :
    DecodedSlots decode source width (.uniform 1 value) := by
  intro slot selected inside found
  have zero : slot = 0 := by omega
  subst slot
  simp only [CompactArray.Tree.get?,if_pos inside,Option.some.injEq] at found
  subst selected
  refine ⟨source.slice 0 width,?_,?_,run⟩
  · rw [size_slice,extent,Nat.sub_zero,Nat.min_self]
  · intro index inByte
    rw [get_slice source 0 width index inByte (by omega)]
    simp only [Nat.zero_add,Nat.zero_mul]

private theorem decoded_slots_split {α ε : Type} (decode : ByteImage → Except ε α)
    (source : ByteImage) (width count : Nat) (extent : source.size = width * count) (large : 2 ≤ count)
    (left : CompactArray.Tree α (count / 2)) (right : CompactArray.Tree α (count - count / 2))
    (first : DecodedSlots decode (source.slice 0 ((count / 2) * width)) width left)
    (second : DecodedSlots decode (source.slice ((count / 2) * width) ((count - count / 2) * width)) width right) :
    DecodedSlots decode source width (.split large left right) := by
  intro slot value inside found
  by_cases before : slot < count / 2
  · simp only [CompactArray.Tree.get?,if_pos before] at found
    obtain ⟨image,imageSize,bytes,run⟩ := first slot value before found
    refine ⟨image,imageSize,?_,run⟩
    intro index inByte
    rw [bytes index inByte]
    change (source.slice 0 (count / 2 * width)).get (slot * width + index) = source.get (slot * width + index)
    have inCount : slot * width + index < count / 2 * width := by
      rw [Nat.mul_comm (count / 2) width]
      exact slot_byte_bound width (count / 2) slot index before inByte
    have inSource : 0 + (slot * width + index) < source.size := by
      rw [Nat.zero_add,extent]
      exact slot_byte_bound width count slot index inside inByte
    rw [get_slice source 0 _ _ inCount inSource]
    simp only [Nat.zero_add]
  · simp only [CompactArray.Tree.get?,if_neg before] at found
    obtain ⟨image,imageSize,bytes,run⟩ := second (slot - count / 2) value (by omega) found
    refine ⟨image,imageSize,?_,run⟩
    intro index inByte
    have position : count / 2 * width + ((slot - count / 2) * width + index) = slot * width + index := by
      rw [← Nat.add_assoc,← Nat.add_mul]
      have sum : count / 2 + (slot - count / 2) = slot := by omega
      rw [sum]
    rw [bytes index inByte]
    change (source.slice (count / 2 * width) ((count - count / 2) * width)).get
      ((slot - count / 2) * width + index) = source.get (slot * width + index)
    have inCount : (slot - count / 2) * width + index < (count - count / 2) * width := by
      rw [Nat.mul_comm (count - count / 2) width]
      exact slot_byte_bound width (count - count / 2) (slot - count / 2) index (by omega) inByte
    have inSource : count / 2 * width + ((slot - count / 2) * width + index) < source.size := by
      rw [position,extent]
      exact slot_byte_bound width count slot index inside inByte
    rw [get_slice source _ _ _ inCount inSource,position]

private theorem phase_slots_source {α ε : Type} (decode : ByteImage → Except ε α)
    (unit source : ByteImage) (width phase count : Nat) (extent : source.size = width * count)
    (sourceBytes : ∀ index, index < source.size → source.get index = unit.get ((phase + index) % unit.size))
    (tree : CompactArray.Tree α count) (held : PhaseSlots decode unit width phase tree) :
    DecodedSlots decode source width tree := by
  intro slot value inside found
  obtain ⟨image,imageSize,bytes,run⟩ := held slot value inside found
  refine ⟨image,imageSize,?_,run⟩
  intro index inByte
  rw [bytes index inByte]
  change unit.get ((phase + slot * width + index) % unit.size) = source.get (slot * width + index)
  rw [sourceBytes _ (by rw [extent]; exact slot_byte_bound width count slot index inside inByte)]
  simp only [Nat.add_assoc]

/-- An actual failing callback and the complete bytes of its input window. -/
def BlockFailed {α ε : Type} (decode : ByteImage → Except ε α) (width : Nat)
    (read : Nat → Option UInt8) (failure : ε) : Prop :=
  ∃ image, image.size = width ∧ (∀ index, index < width → image.get index = read index) ∧ decode image = .error failure

/-- A mapper failure belongs to an actual callback on a visible logical slot. -/
def FailedSlots {α ε : Type} (decode : ByteImage → Except ε α) (source : ByteImage)
    (width count : Nat) (failure : ε) : Prop :=
  ∃ slot, slot < count ∧ BlockFailed decode width (fun index => source.get (slot * width + index)) failure

/-- Actual callback success for every complete observed window at a visible
    source slot. Constructor-sensitive callbacks must establish this premise
    for those windows; byte equality alone is not callback extensionality. -/
def BlockWindowsSucceed {α ε : Type} (decode : ByteImage → Except ε α) (source : ByteImage)
    (width count : Nat) : Prop :=
  ∀ slot, slot < count → ∀ image, image.size = width →
    (∀ index, index < width → image.get index = source.get (slot * width + index)) →
    ∃ value, decode image = .ok value

private abbrev PhaseFailed {α ε : Type} (decode : ByteImage → Except ε α)
    (unit : ByteImage) (width phase : Nat) (failure : ε) : Prop :=
  BlockFailed decode width (fun index => unit.get ((phase + index) % unit.size)) failure

private def PhaseFailure {α ε : Type} (decode : ByteImage → Except ε α)
    (unit : ByteImage) (width phase count : Nat) (failure : ε) : Prop :=
  ∃ slot, slot < count ∧ PhaseFailed decode unit width (phase + slot * width) failure

private theorem phase_failed_congr {α ε : Type} (decode : ByteImage → Except ε α)
    (unit : ByteImage) (width first second : Nat) (failure : ε)
    (same : first % unit.size = second % unit.size)
    (held : PhaseFailed decode unit width first failure) : PhaseFailed decode unit width second failure := by
  obtain ⟨image,extent,bytes,run⟩ := held
  refine ⟨image,extent,?_,run⟩
  intro index inside
  rw [bytes index inside]
  change unit.get ((first + index) % unit.size) = unit.get ((second + index) % unit.size)
  apply congrArg unit.get
  rw [Nat.add_mod first index,Nat.add_mod second index,same]

private theorem phase_failure_prefix {α ε : Type} (decode : ByteImage → Except ε α)
    (unit : ByteImage) (width phase first count : Nat) (bound : first ≤ count) (failure : ε)
    (held : PhaseFailure decode unit width phase first failure) : PhaseFailure decode unit width phase count failure := by
  obtain ⟨slot,inside,failed⟩ := held
  exact ⟨slot,by omega,failed⟩

private theorem phase_failure_right {α ε : Type} (decode : ByteImage → Except ε α)
    (unit : ByteImage) (width phase count : Nat) (failure : ε)
    (held : PhaseFailure decode unit width ((phase + (count / 2) * width) % unit.size) (count - count / 2) failure) :
    PhaseFailure decode unit width phase count failure := by
  obtain ⟨slot,inside,failed⟩ := held
  refine ⟨count / 2 + slot,by have bound := Nat.div_le_self count 2; omega,?_⟩
  apply phase_failed_congr decode unit width _ _ failure _ failed
  rw [Nat.mod_add_mod,Nat.add_mul,Nat.add_assoc]

private theorem BlockStateResult.map_error {σ α ε : Type} {stateValid : σ → Prop} {valid : α → Prop}
    {error other : ε → Prop} {action : StateT σ (Except ε) α}
    (held : BlockStateResult stateValid valid error action) (implies : ∀ failure, error failure → other failure) :
    BlockStateResult stateValid valid other action := by
  intro state safe
  have result := held state safe
  cases run : action.run state with
  | error failure => rw [run] at result; exact implies failure result
  | ok pair => rw [run] at result; exact result

private theorem periodic_callback_failed {α ε : Type} (decode : ByteImage → Except ε α)
    (unit : ByteImage) (positive : 0 < unit.size) (width phase count : Nat) (nonempty : count ≠ 0) :
    BlockResult (fun _ => True) (PhaseFailure decode unit width phase count)
      (decode ⟨width,.periodic unit.tree positive phase width⟩) := by
  cases run : decode ⟨width,.periodic unit.tree positive phase width⟩ with
  | ok value => exact True.intro
  | error failure =>
    refine ⟨0,by omega,⟨width,.periodic unit.tree positive phase width⟩,rfl,?_,run⟩
    intro index inside
    simp only [Nat.zero_mul,Nat.add_zero,get,Tree.get,if_pos inside]

private theorem periodicBlocks_failure {α ε : Type} (decode : ByteImage → Except ε α)
    (unit : ByteImage) (positive : 0 < unit.size) (width phase count : Nat) :
    BlockStateResult (fun _ => True) (fun _ => True) (PhaseFailure decode unit width phase count)
      (periodicBlocks decode unit positive width phase count) := by
  induction count using trustIrNatStrongInduction generalizing phase with
  | ind count ih =>
    intro entries safe
    rw [periodicBlocks]
    have getter : (getThe (List (BlockEntry α)) : StateT (List (BlockEntry α)) (Except ε) (List (BlockEntry α))) entries = .ok (entries,entries) := rfl
    simp only [StateT.bind,StateT.get,StateT.pure,StateT.run,getter,bind,pure,Except.bind,Except.pure]
    cases cached : cachedBlocks phase count entries with
    | some tree => exact ⟨True.intro,True.intro⟩
    | none =>
      let building : StateT (List (BlockEntry α)) (Except ε) (CompactArray.Tree α count) := (do
          if width % unit.size = 0 then do
            if hzero : count = 0 then pure (hzero ▸ CompactArray.Tree.dense (by omega) .nil)
            else
              let value ← liftM (decode ⟨width, .periodic unit.tree positive phase width⟩)
              pure (.uniform count value)
          else if hzero : count = 0 then pure (hzero ▸ CompactArray.Tree.dense (by omega) .nil)
          else if _shorter : unit.size / Nat.gcd unit.size width < count then do
            let period := unit.size / Nat.gcd unit.size width
            let values ← periodicBlocks decode unit positive width phase period
            pure (.periodic values (Nat.div_gcd_pos_of_pos_left width positive) 0 count)
          else if hone : count = 1 then do
            let value ← liftM (decode ⟨width, .periodic unit.tree positive phase width⟩)
            pure (hone ▸ CompactArray.Tree.uniform 1 value)
          else do
            let left ← periodicBlocks decode unit positive width phase (count / 2)
            let right ← periodicBlocks decode unit positive width
              ((phase + (count / 2) * width) % unit.size) (count - count / 2)
            pure (.split (by omega) left right))
      have body : BlockStateResult (fun _ => True) (fun _ => True) (PhaseFailure decode unit width phase count) building := by
        dsimp only [building]
        split
        · split
          · rename_i zero; subst count
            exact BlockStateResult.pure _ _ _ _ True.intro
          · apply BlockStateResult.bind _ (fun _ => True) _ _ _ _
              (BlockStateResult.lift _ _ _ _ (periodic_callback_failed decode unit positive width phase count (by assumption)))
            intro value held
            exact BlockStateResult.pure _ _ _ _ True.intro
        · split
          · rename_i zero; subst count
            exact BlockStateResult.pure _ _ _ _ True.intro
          · split
            · rename_i shorter
              apply BlockStateResult.bind _ (fun _ => True) _ _ _ _
                ((ih _ shorter phase).map_error (phase_failure_prefix decode unit width phase _ count (by omega)))
              intro values held
              exact BlockStateResult.pure _ _ _ _ True.intro
            · split
              · rename_i one; subst count
                apply BlockStateResult.bind _ (fun _ => True) _ _ _ _
                  (BlockStateResult.lift _ _ _ _ (periodic_callback_failed decode unit positive width phase 1 (by decide)))
                intro value held
                exact BlockStateResult.pure _ _ _ _ True.intro
              · apply BlockStateResult.bind _ (fun _ => True) _ _ _ _
                  ((ih _ (by omega) phase).map_error (phase_failure_prefix decode unit width phase _ count (Nat.div_le_self count 2)))
                intro left first
                apply BlockStateResult.bind _ (fun _ => True) _ _ _ _
                  ((ih _ (by omega) _).map_error (phase_failure_right decode unit width phase count))
                intro right second
                exact BlockStateResult.pure _ _ _ _ True.intro
      have finish_state (tree : CompactArray.Tree α count) (_held : True) :
          BlockStateResult (fun _ => True) (fun _ => True) (PhaseFailure decode unit width phase count) (do
            modify (fun (entries : List (BlockEntry α)) => { phase, values := ⟨count,tree⟩ } :: entries)
            pure tree) := by
        intro cache cacheValid
        exact ⟨True.intro,True.intro⟩
      have finished := (BlockStateResult.bind (fun _ => True) (fun _ => True) (fun _ => True)
        (PhaseFailure decode unit width phase count) building _ body finish_state) entries safe
      cases decoding : decode ⟨width, .periodic unit.tree positive phase width⟩ <;>
        by_cases divided : width % unit.size = 0 <;>
          by_cases zero : count = 0 <;>
            by_cases shorter : unit.size / Nat.gcd unit.size width < count <;>
              by_cases one : count = 1 <;>
                simp_all [building,block_state_pure_bind,block_state_bind_assoc,pure_bind,bind_assoc,
                  StateT.bind,StateT.pure,StateT.run,StateT.lift,block_lift_run,block_modify_run,
                  bind,pure,Except.bind,Except.pure,block_except_assoc] <;>
                  (simp only [← Except.bind.eq_def,block_except_assoc,block_except_ok_bind] at finished ⊢
                   first
                   | exact finished
                   | (split <;> try omega
                      all_goals simp_all [StateT.bind,StateT.pure,StateT.run,block_lift_run,block_modify_run,
                       bind,pure,Except.bind,Except.pure] <;>
                       (simp only [← Except.bind.eq_def,block_except_assoc,block_except_ok_bind] at finished ⊢; exact finished)))


private theorem callback_run {α ε : Type} (decode : ByteImage → Except ε α) (image : ByteImage) :
    BlockResult (fun value => decode image = .ok value) (fun _ : ε => True) (decode image) := by
  cases _run : decode image with
  | error _ => exact True.intro
  | ok _ => rfl


def mapBlocksSpec {α ε : Type} (decode : ByteImage → Except ε α)
    (image : ByteImage) (width count : Nat) : Except ε (CompactArray.Tree α count) := do
  let image := WindowRuntime.canonicalImage image
  if hzero : count = 0 then return hzero ▸ CompactArray.Tree.dense (by omega) .nil
  if width == 0 then return .uniform count (← decode empty)
  if image.size == width * count then
    if let some (unit, phase) := image.periodicWindow then
      if positive : 0 < unit.size then
        return (← (periodicBlocks decode unit positive width phase count).run []).1
  if large : 2 ≤ count then
    let left ← mapBlocksSpec decode (image.slice 0 ((count / 2) * width)) width (count / 2)
    let right ← mapBlocksSpec decode (image.slice ((count / 2) * width)
      ((count - count / 2) * width)) width (count - count / 2)
    return .split large left right
  else if hone : count = 1 then return hone ▸ CompactArray.Tree.uniform 1 (← decode (image.slice 0 width))
  else
    have zero : count = 0 := by omega
    return zero ▸ CompactArray.Tree.dense (by omega) .nil
termination_by count

/-- Indexed callback custody through the production mapper. The lower proof
    receives periodic phase/window laws; the public proof layer discharges them. -/
theorem mapBlocksSpec_decoded_of_periods
    (cycleLaw : ∀ period width phase index : Nat,
      (phase + (index % (period / Nat.gcd period width)) * width) % period =
        (phase + index * width) % period)
    (windowLaw : ∀ (image unit : ByteImage) (phase : Nat), image.periodicWindow = some (unit,phase) →
      0 < unit.size ∧ ∀ index, index < image.size → image.get index = unit.get ((phase + index) % unit.size))
    {α ε : Type} (decode : ByteImage → Except ε α) (image : ByteImage) (width count : Nat)
    (extent : image.size = width * count) :
    BlockResult (DecodedSlots decode image width) (fun _ : ε => True) (mapBlocksSpec decode image width count) := by
  induction count using trustIrNatStrongInduction generalizing image with
  | ind count ih =>
    let source := WindowRuntime.canonicalImage image
    have sourceExtent : source.size = width * count := by rw [WindowRuntime.canonicalImage_size]; exact extent
    have transport (result : Except ε (CompactArray.Tree α count))
        (held : BlockResult (DecodedSlots decode source width) (fun _ : ε => True) result) :
        BlockResult (DecodedSlots decode image width) (fun _ : ε => True) result := by
      cases result with
      | error _ => exact True.intro
      | ok tree =>
        exact decoded_slots_congr decode source image width tree
          (WindowRuntime.canonicalImage_get image) held
    apply transport
    have periodic (unit : ByteImage) (positive : 0 < unit.size) (phase : Nat)
        (cert : source.periodicWindow = some (unit,phase)) :
        BlockResult (fun pair : CompactArray.Tree α count × List (BlockEntry α) =>
          DecodedSlots decode source width pair.1) (fun _ : ε => True)
          ((periodicBlocks decode unit positive width phase count).run []) := by
      have held := periodicBlocks_phase cycleLaw decode unit positive width phase count []
        (fun _ member => by cases member)
      cases executed : (periodicBlocks decode unit positive width phase count).run [] with
      | error _ => exact True.intro
      | ok pair =>
        rw [executed] at held
        exact phase_slots_source decode unit source width phase count sourceExtent
          (windowLaw source unit phase cert).2 pair.1 held.1
    have geometry : count / 2 * width + (count - count / 2) * width = source.size := by
      rw [sourceExtent,Nat.mul_comm width count,← Nat.add_mul]
      apply congrArg (· * width)
      have halfBound := Nat.div_le_self count 2
      omega
    have leftRun (large : 2 ≤ count) :
        BlockResult (DecodedSlots decode (source.slice 0 ((count / 2) * width)) width) (fun _ : ε => True)
          (mapBlocksSpec decode (source.slice 0 ((count / 2) * width)) width (count / 2)) := by
      apply ih _ (by omega)
      rw [size_slice,Nat.sub_zero]
      have ordering : count / 2 * width = width * (count / 2) := Nat.mul_comm _ _
      have fit : count / 2 * width ≤ source.size := by
        rw [← geometry]
        exact Nat.le_add_right _ _
      rw [Nat.min_eq_left fit,ordering]
    have rightRun (large : 2 ≤ count) :
        BlockResult (DecodedSlots decode (source.slice ((count / 2) * width) ((count - count / 2) * width)) width)
          (fun _ : ε => True)
          (mapBlocksSpec decode (source.slice ((count / 2) * width) ((count - count / 2) * width)) width (count - count / 2)) := by
      apply ih _ (by omega)
      rw [size_slice]
      have ordering : (count - count / 2) * width = width * (count - count / 2) := Nat.mul_comm _ _
      omega
    rw [mapBlocksSpec]
    dsimp only
    have exactSize : (WindowRuntime.canonicalImage image).size = width * count := sourceExtent
    simp only [exactSize,beq_self_eq_true,ite_true]
    repeat' first
      | (simp only [pure_bind])
      | subst count
      | (solve | exfalso; omega)
      | (solve | exact decoded_slots_empty decode source width _)
      | (solve | exact decoded_slots_zero decode source width _ (by simpa only [beq_iff_eq] using (by assumption : (width == 0) = true)) _ (by assumption))
      | (solve | exact decoded_slots_single decode source width (by simpa only [Nat.mul_one] using sourceExtent) _ (by assumption))
      | (solve | exact decoded_slots_split decode source width _ sourceExtent _ _ _ (by assumption) (by assumption))
      | (solve | exact (by assumption : DecodedSlots decode source width _))
      | (refine BlockResult.bind (fun value => decode _ = .ok value) (DecodedSlots decode source width) (fun _ : ε => True) _ _ (callback_run decode _) ?_; intro value held)
      | (refine BlockResult.bind (DecodedSlots decode _ width) (DecodedSlots decode source width) (fun _ : ε => True) _ _ (leftRun (by assumption)) ?_; intro left first)
      | (refine BlockResult.bind (DecodedSlots decode _ width) (DecodedSlots decode source width) (fun _ : ε => True) _ _ (rightRun (by assumption)) ?_; intro right second)
      | (refine BlockResult.bind (fun pair : CompactArray.Tree α count × List (BlockEntry α) => DecodedSlots decode source width pair.1) (DecodedSlots decode source width) (fun _ : ε => True) _ _ (periodic _ _ _ (by assumption)) ?_; intro pair held)
      | (solve | have positive := (windowLaw _ _ _ (by assumption)).1; contradiction)
      | split
      | (dsimp only; split)

theorem BlockResult.map_error {α ε : Type} {valid : α → Prop} {error other : ε → Prop} {result : Except ε α}
    (held : BlockResult valid error result) (implies : ∀ failure, error failure → other failure) :
    BlockResult valid other result := by
  cases result with
  | error failure => exact implies failure held
  | ok value => exact held

theorem FailedSlots.congr {α ε : Type} (decode : ByteImage → Except ε α) (left right : ByteImage)
    (width count : Nat) (failure : ε) (bytes : ∀ index, left.get index = right.get index)
    (held : FailedSlots decode left width count failure) : FailedSlots decode right width count failure := by
  obtain ⟨slot,inside,image,extent,observed,run⟩ := held
  refine ⟨slot,inside,image,extent,?_,run⟩
  intro index inByte
  exact (observed index inByte).trans (bytes (slot * width + index))

/-- A failure in a visible block-aligned subwindow belongs to the corresponding
    original logical slot, with its actual callback input retained. -/
theorem FailedSlots.of_window {α ε : Type} (decode : ByteImage → Except ε α) (source : ByteImage)
    (width total start count : Nat) (extent : source.size = width * total) (bounded : start + count ≤ total)
    (failure : ε) (held : FailedSlots decode (source.slice (start * width) (count * width)) width count failure) :
    FailedSlots decode source width total failure := by
  obtain ⟨slot,inside,image,imageSize,bytes,run⟩ := held
  refine ⟨start + slot,by omega,image,imageSize,?_,run⟩
  intro index inByte
  rw [bytes index inByte]
  change (source.slice (start * width) (count * width)).get (slot * width + index) = source.get ((start + slot) * width + index)
  have inCount : slot * width + index < count * width := by
    rw [Nat.mul_comm count width]
    exact slot_byte_bound width count slot index inside inByte
  have position : start * width + (slot * width + index) = (start + slot) * width + index := by
    rw [Nat.add_mul,Nat.add_assoc]
  have inSource : start * width + (slot * width + index) < source.size := by
    rw [position,extent]
    exact slot_byte_bound width total (start + slot) index (by omega) inByte
  rw [get_slice source _ _ _ inCount inSource,position]

private theorem phase_failure_source {α ε : Type} (decode : ByteImage → Except ε α)
    (unit source : ByteImage) (width phase count : Nat) (extent : source.size = width * count)
    (sourceBytes : ∀ index, index < source.size → source.get index = unit.get ((phase + index) % unit.size))
    (failure : ε) (held : PhaseFailure decode unit width phase count failure) :
    FailedSlots decode source width count failure := by
  obtain ⟨slot,inside,image,imageSize,bytes,run⟩ := held
  refine ⟨slot,inside,image,imageSize,?_,run⟩
  intro index inByte
  rw [bytes index inByte]
  change unit.get ((phase + slot * width + index) % unit.size) = source.get (slot * width + index)
  rw [sourceBytes _ (by rw [extent]; exact slot_byte_bound width count slot index inside inByte)]
  simp only [Nat.add_assoc]

private theorem callback_failure_window {α ε : Type} (decode : ByteImage → Except ε α)
    (source image : ByteImage) (width count slot : Nat) (inside : slot < count) (extent : image.size = width)
    (bytes : ∀ index, index < width → image.get index = source.get (slot * width + index)) :
    BlockResult (fun _ => True) (FailedSlots decode source width count) (decode image) := by
  cases run : decode image with
  | ok value => exact True.intro
  | error failure => exact ⟨slot,inside,image,extent,bytes,run⟩

/-- Failure custody for the actual compressed mapper. Every propagated error
    is an actual callback failure on a visible logical slot, including periodic
    cache paths. No callback extensionality or success premise is assumed. -/
theorem mapBlocksSpec_failure_of_periods
    (windowLaw : ∀ (image unit : ByteImage) (phase : Nat), image.periodicWindow = some (unit,phase) →
      0 < unit.size ∧ ∀ index, index < image.size → image.get index = unit.get ((phase + index) % unit.size))
    {α ε : Type} (decode : ByteImage → Except ε α) (image : ByteImage) (width count : Nat)
    (extent : image.size = width * count) :
    BlockResult (fun _ => True) (FailedSlots decode image width count) (mapBlocksSpec decode image width count) := by
  induction count using trustIrNatStrongInduction generalizing image with
  | ind count ih =>
    let source := WindowRuntime.canonicalImage image
    have sourceExtent : source.size = width * count := by rw [WindowRuntime.canonicalImage_size]; exact extent
    have transport (result : Except ε (CompactArray.Tree α count))
        (held : BlockResult (fun _ => True) (FailedSlots decode source width count) result) :
        BlockResult (fun _ => True) (FailedSlots decode image width count) result :=
      held.map_error (fun failure failed => FailedSlots.congr decode source image width count failure
        (WindowRuntime.canonicalImage_get image) failed)
    apply transport
    have periodic (unit : ByteImage) (positive : 0 < unit.size) (phase : Nat)
        (cert : source.periodicWindow = some (unit,phase)) :
        BlockResult (fun _ => True) (FailedSlots decode source width count)
          ((periodicBlocks decode unit positive width phase count).run []) := by
      have held := periodicBlocks_failure decode unit positive width phase count [] True.intro
      cases executed : (periodicBlocks decode unit positive width phase count).run [] with
      | ok pair => exact True.intro
      | error failure =>
        rw [executed] at held
        exact phase_failure_source decode unit source width phase count sourceExtent (windowLaw source unit phase cert).2 failure held
    have geometry : count / 2 * width + (count - count / 2) * width = source.size := by
      rw [sourceExtent,Nat.mul_comm width count,← Nat.add_mul]
      apply congrArg (· * width)
      have halfBound := Nat.div_le_self count 2
      omega
    have leftRun (large : 2 ≤ count) :
        BlockResult (fun _ => True) (FailedSlots decode source width count)
          (mapBlocksSpec decode (source.slice 0 ((count / 2) * width)) width (count / 2)) := by
      have slicedExtent : (source.slice 0 ((count / 2) * width)).size = width * (count / 2) := by
        rw [size_slice,Nat.sub_zero]
        have fit : count / 2 * width ≤ source.size := by rw [← geometry]; exact Nat.le_add_right _ _
        rw [Nat.min_eq_left fit,Nat.mul_comm]
      have held := ih _ (by omega) _ slicedExtent
      apply held.map_error
      intro failure failed
      simpa only [Nat.zero_mul,Nat.zero_add] using
        FailedSlots.of_window decode source width count 0 (count / 2) sourceExtent (by omega) failure (by simpa only [Nat.zero_mul] using failed)
    have rightRun (large : 2 ≤ count) :
        BlockResult (fun _ => True) (FailedSlots decode source width count)
          (mapBlocksSpec decode (source.slice ((count / 2) * width) ((count - count / 2) * width)) width (count - count / 2)) := by
      have slicedExtent : (source.slice ((count / 2) * width) ((count - count / 2) * width)).size = width * (count - count / 2) := by
        rw [size_slice]
        have ordering := Nat.mul_comm (count - count / 2) width
        omega
      exact (ih _ (by omega) _ slicedExtent).map_error
        (FailedSlots.of_window decode source width count (count / 2) (count - count / 2) sourceExtent (by omega))
    have zeroRun (nonempty : count ≠ 0) (zero : width = 0) :
        BlockResult (fun _ => True) (FailedSlots decode source width count) (decode empty) := by
      apply callback_failure_window decode source empty width count 0 (by omega) (by change 0 = width; omega)
      intro index inside
      omega
    have singleRun (one : count = 1) :
        BlockResult (fun _ => True) (FailedSlots decode source width count) (decode (source.slice 0 width)) := by
      apply callback_failure_window decode source (source.slice 0 width) width count 0 (by omega)
      · rw [size_slice,Nat.sub_zero,sourceExtent,one,Nat.mul_one,Nat.min_self]
      · intro index inside
        rw [get_slice source 0 width index inside (by rw [sourceExtent,one,Nat.mul_one]; omega)]
        simp only [Nat.zero_mul,Nat.zero_add]
    rw [mapBlocksSpec]
    dsimp only
    have exactSize : (WindowRuntime.canonicalImage image).size = width * count := sourceExtent
    simp only [exactSize,beq_self_eq_true,ite_true]
    repeat' first
      | exact True.intro
      | (simp only [pure_bind])
      | (solve | exfalso; omega)
      | (refine BlockResult.bind (fun _ => True) (fun _ => True) (FailedSlots decode source width count) _ _
          (zeroRun (by assumption) (by simpa only [beq_iff_eq] using (by assumption : (width == 0) = true))) ?_; intro value held)
      | (refine BlockResult.bind (fun _ => True) (fun _ => True) (FailedSlots decode source width count) _ _
          (singleRun (by omega)) ?_; intro value held)
      | (refine BlockResult.bind (fun _ => True) (fun _ => True) (FailedSlots decode source width count) _ _
          (leftRun (by assumption)) ?_; intro left held)
      | (refine BlockResult.bind (fun _ => True) (fun _ => True) (FailedSlots decode source width count) _ _
          (rightRun (by assumption)) ?_; intro right held)
      | (refine BlockResult.bind (fun _ => True) (fun _ => True) (FailedSlots decode source width count) _ _
          (periodic _ _ _ (by assumption)) ?_; intro pair held)
      | (solve | have positive := (windowLaw _ _ _ (by assumption)).1; contradiction)
      | split
      | (dsimp only; split)

/-- Original compressed block mapping preserves an arbitrary callback value
predicate and error set, including periodic-cache reuse and empty outputs. -/
theorem mapBlocksSpec_valid {α ε : Type} (valid : α → Prop) (error : ε → Prop)
    (decode : ByteImage → Except ε α) (callbacks : ∀ image, BlockResult valid error (decode image))
    (image : ByteImage) (width count : Nat) :
    BlockResult (BlockTreeValid valid) error (mapBlocksSpec decode image width count) := by
  induction count using trustIrNatStrongInduction generalizing image with
  | ind count ih =>
    have periodic (unit : ByteImage) (positive : 0 < unit.size) (phase : Nat) :
        BlockResult (fun pair => BlockTreeValid valid pair.1 ∧ BlockCacheValid valid pair.2) error
          ((periodicBlocks decode unit positive width phase count).run []) :=
      periodicBlocks_valid valid error decode callbacks unit positive width phase count [] (fun _ member => by cases member)
    rw [mapBlocksSpec]
    dsimp only
    repeat' first
      | (solve | omega)
      | (simp only [pure_bind])
      | subst count
      | (solve | exact BlockTreeValid.empty valid)
      | (solve | exact BlockTreeValid.uniform valid _ _ (by assumption))
      | (solve | exact BlockTreeValid.split valid _ _ _ (by assumption) (by assumption))
      | (solve | exact (by assumption : BlockTreeValid valid _))
      | (refine BlockResult.bind valid (BlockTreeValid valid) error _ _ (callbacks _) ?_; intro value held)
      | (refine BlockResult.bind (BlockTreeValid valid) (BlockTreeValid valid) error _ _ (ih _ (by omega) _) ?_; intro tree held)
      | (refine BlockResult.bind (fun pair : CompactArray.Tree α count × List (BlockEntry α) => BlockTreeValid valid pair.1 ∧ BlockCacheValid valid pair.2)
          (BlockTreeValid valid) error _ _ (periodic _ _ _) ?_; intro pair held)
      | (solve | exact held.1)
      | split
      | (dsimp only; split)

/-- Coverage summaries are relative to a block. Both sides are evaluated
    before selecting the first hole, so a later semantic error is not lost. -/
private def combineMissing (offset : Nat) (left right : Option Nat) : Option Nat :=
  match left with
  | some index => some index
  | none => right.map (offset + ·)

private abbrev CheckEntry := Nat × Nat × Option Nat

private def periodicCheck {ε : Type} (check : ByteImage → Except ε (Option Nat))
    (unit : ByteImage) (positive : 0 < unit.size) (width phase count : Nat) :
    StateT (List CheckEntry) (Except ε) (Option Nat) := do
  let entries ← getThe (List CheckEntry)
  if let some entry := entries.find? (fun entry => entry.1 == phase && entry.2.1 == count) then
    return entry.2.2
  let result ←
    if count == 0 then pure none
    else if width % unit.size == 0 || count == 1 then
      liftM (check ⟨width, .periodic unit.tree positive phase width⟩)
    else if large : 2 ≤ count then do
      let left ← periodicCheck check unit positive width phase (count / 2)
      let right ← periodicCheck check unit positive width
        ((phase + (count / 2) * width) % unit.size) (count - count / 2)
      pure (combineMissing ((count / 2) * width) left right)
    else pure none
  modify (fun entries => (phase, count, result) :: entries)
  return result
termination_by count

private theorem periodicCheck_errors {ε : Type} (error : ε → Prop)
    (check : ByteImage → Except ε (Option Nat))
    (callbacks : ∀ image, BlockResult (fun _ => True) error (check image))
    (unit : ByteImage) (positive : 0 < unit.size) (width phase count : Nat) :
    ∀ entries failure, (periodicCheck check unit positive width phase count).run entries = .error failure → error failure := by
  induction count using trustIrNatStrongInduction generalizing phase with
  | ind count ih =>
    intro entries failure executed
    rw [periodicCheck] at executed
    have getter : (getThe (List CheckEntry) : StateT (List CheckEntry) (Except ε) (List CheckEntry)) entries = .ok (entries,entries) := rfl
    cases found : entries.find? (fun entry => entry.1 == phase && entry.2.1 == count) <;>
      cases callbackRun : check ⟨width, .periodic unit.tree positive phase width⟩ <;>
      repeat' first
      | (solve | cases executed)
      | (solve | exact BlockResult.error_of_eq (fun _ => True) error (check _) _ (callbacks _) (by assumption))
      | (solve | cases executed; exact BlockResult.error_of_eq (fun _ => True) error (check _) _ (callbacks _) (by assumption))
      | (solve | exact ih (count / 2) (by omega) phase entries _ (by assumption))
      | (solve | exact ih (count - count / 2) (by omega) _ _ _ (by assumption))
      | (solve | cases executed; exact ih (count / 2) (by omega) phase entries _ (by assumption))
      | (solve | cases executed; exact ih (count - count / 2) (by omega) _ _ _ (by assumption))
      | (simp only [StateT.run,StateT.bind,StateT.pure,block_lift_run,block_modify_run,getter,found,callbackRun,
          bind,pure,Except.bind,Except.pure] at executed)
      | split at executed
      | (dsimp only at executed; split at executed)

/-- Inspect every logical block's semantic result while retaining only exact
    phase/count summaries for a certified periodic region. External sources
    remain pointwise. Errors retain left-to-right precedence over holes. -/
def checkBlocksSpec {ε : Type} (check : ByteImage → Except ε (Option Nat))
    (image : ByteImage) (width count : Nat) : Except ε (Option Nat) := do
  let image := WindowRuntime.canonicalImage image
  if count == 0 then return none
  if width == 0 then return ← check empty
  if image.size == width * count then
    if let some (unit, phase) := image.periodicWindow then
      if positive : 0 < unit.size then
        return (← (periodicCheck check unit positive width phase count).run []).1
  if large : 2 ≤ count then
    let left ← checkBlocksSpec check (image.slice 0 ((count / 2) * width)) width (count / 2)
    let right ← checkBlocksSpec check (image.slice ((count / 2) * width)
      ((count - count / 2) * width)) width (count - count / 2)
    return combineMissing ((count / 2) * width) left right
  else return ← check (image.slice 0 width)
termination_by count

/-- Covered-byte checking forwards only callback errors. Cached summaries
contain successful optional offsets and cannot fabricate a new error. -/
theorem checkBlocksSpec_errors {ε : Type} (error : ε → Prop)
    (check : ByteImage → Except ε (Option Nat))
    (callbacks : ∀ image, BlockResult (fun _ => True) error (check image))
    (image : ByteImage) (width count : Nat) :
    BlockResult (fun _ => True) error (checkBlocksSpec check image width count) := by
  induction count using trustIrNatStrongInduction generalizing image with
  | ind count ih =>
    rw [checkBlocksSpec]
    dsimp only
    repeat' first
      | (solve | exact True.intro)
      | (simp only [pure_bind])
      | (solve | exact callbacks _)
      | (refine BlockResult.bind (fun _ => True) (fun _ => True) error _ _ (callbacks _) ?_; intro _ _; exact True.intro)
      | (refine BlockResult.bind (fun _ => True) (fun _ => True) error _ _ (ih _ (by omega) _) ?_; intro value _)
      | (refine BlockResult.bind (fun _ => True) (fun _ => True) error _ _ ?_ ?_
         · cases run : (periodicCheck check _ _ width _ count).run [] with
           | ok pair => exact True.intro
           | error failure => exact periodicCheck_errors error check callbacks _ _ _ _ _ _ failure run
         · intro _ _; exact True.intro)
      | split
      | (dsimp only; split)

namespace WindowRuntime

private abbrev BlockKey := Key × Nat × Nat
private structure MapEntry (α ε : Type) where
  result : Except ε (CompactArray.Packed α)
  window : Window
private structure MapCache (α ε : Type) where
  memo : trustIrHashMap BlockKey (MapEntry α ε) := ∅
  stats : Stats := {}

private structure CheckEntry (ε : Type) where
  result : Except ε (Option Nat)
  window : Window
private structure CheckCache (ε : Type) where
  memo : trustIrHashMap BlockKey (CheckEntry ε) := ∅
  stats : Stats := {}


end WindowRuntime

/-- Every recursive entry canonicalizes the callback's retained window in both
    the logical specification and compiled traversal. Callbacks may inspect
    constructors as well as extent/bytes; no extensionality premise is assumed.
    Memoization is local to one fixed callback and exact canonical window. -/
@[nospecialize, trustIrExtern 6 "l_TrustIr_ByteImage_mapBlocks(#1, #2, #3, #4, #5, #6)"]
def mapBlocks {α ε : Type} (decode : ByteImage → Except ε α)
    (image : ByteImage) (width count : Nat) : Except ε (CompactArray.Tree α count) :=
  mapBlocksSpec decode image width count

/-- Public mapper validity refers to the original executable specification;
its optimized implementation and error order are unchanged. -/
theorem mapBlocks_valid {α ε : Type} (valid : α → Prop) (error : ε → Prop)
    (decode : ByteImage → Except ε α) (callbacks : ∀ image, BlockResult valid error (decode image))
    (image : ByteImage) (width count : Nat) :
    BlockResult (BlockTreeValid valid) error (mapBlocks decode image width count) :=
  mapBlocksSpec_valid valid error decode callbacks image width count


@[nospecialize, trustIrExtern 5 "l_TrustIr_ByteImage_checkBlocks(#1, #2, #3, #4, #5)"]
def checkBlocks {ε : Type} (check : ByteImage → Except ε (Option Nat))
    (image : ByteImage) (width count : Nat) : Except ε (Option Nat) :=
  checkBlocksSpec check image width count

theorem checkBlocks_errors {ε : Type} (error : ε → Prop)
    (check : ByteImage → Except ε (Option Nat))
    (callbacks : ∀ image, BlockResult (fun _ => True) error (check image))
    (image : ByteImage) (width count : Nat) :
    BlockResult (fun _ => True) error (checkBlocks check image width count) :=
  checkBlocksSpec_errors error check callbacks image width count


end TrustIr.ByteImage

namespace TrustIr.ByteImage
/-- Opaque access to existing pure helpers for the separate runtime representation.
    These aliases retain their original private declarations and confer no runtime proof. -/
abbrev runtimeScanWhere := scanWhere
abbrev runtimePeriodicBlocks := @periodicBlocks
abbrev runtimePeriodicCheck := @periodicCheck
abbrev runtimeCombineMissing := combineMissing

/-- Every logical block authorizes the checker on any window with the same
    visible bytes. Retained constructors and invisible bytes give no authority. -/
def CheckedBlocks {ε : Type} (check : ByteImage → Except ε (Option Nat))
    (source : ByteImage) (width count : Nat) : Prop :=
  ∀ slot, slot < count → ∀ image, image.size = width →
    (∀ index, index < width → image.get index = source.get (slot * width + index)) → check image = .ok none

private def PhaseChecked {ε : Type} (check : ByteImage → Except ε (Option Nat))
    (unit : ByteImage) (width phase count : Nat) : Prop :=
  ∀ slot, slot < count → ∀ image, image.size = width →
    (∀ index, index < width → image.get index = unit.get ((phase + slot * width + index) % unit.size)) →
      check image = .ok none

private def CheckCacheNone (entries : List CheckEntry) : Prop :=
  ∀ entry ∈ entries, entry.2.2 = none

private theorem check_cache_find_none (entries : List CheckEntry) (test : CheckEntry → Bool)
    (safe : CheckCacheNone entries) (entry : CheckEntry) (found : entries.find? test = some entry) :
    entry.2.2 = none := by
  induction entries with
  | nil => cases found
  | cons first rest ih =>
    simp only [List.find?_cons] at found
    cases hit : test first with
    | false =>
      simp only [hit] at found
      exact ih (fun held member => safe held (List.mem_cons_of_mem _ member)) found
    | true =>
      simp only [hit] at found
      cases found
      exact safe _ (by simp)

private theorem periodicCheck_none_of_windows {ε : Type} (check : ByteImage → Except ε (Option Nat))
    (unit : ByteImage) (positive : 0 < unit.size) (width phase count : Nat)
    (callbacks : PhaseChecked check unit width phase count) :
    BlockStateResult CheckCacheNone (fun missing => missing = none) (fun _ : ε => False)
      (periodicCheck check unit positive width phase count) := by
  induction count using trustIrNatStrongInduction generalizing phase with
  | ind count ih =>
    intro entries safe
    rw [periodicCheck]
    have getter : (getThe (List CheckEntry) : StateT (List CheckEntry) (Except ε) (List CheckEntry)) entries =
      .ok (entries,entries) := rfl
    simp only [StateT.bind,StateT.get,StateT.pure,StateT.run,getter,bind,pure,Except.bind,Except.pure]
    cases found : entries.find? (fun entry => entry.1 == phase && entry.2.1 == count) with
    | some entry =>
      have empty := check_cache_find_none entries _ safe entry found
      simp only [found,empty]
      exact ⟨rfl,safe⟩
    | none =>
      simp only [found]
      let building : StateT (List CheckEntry) (Except ε) (Option Nat) := do
        if count == 0 then pure none
        else if width % unit.size == 0 || count == 1 then
          liftM (check ⟨width, .periodic unit.tree positive phase width⟩)
        else if large : 2 ≤ count then do
          let left ← periodicCheck check unit positive width phase (count / 2)
          let right ← periodicCheck check unit positive width
            ((phase + (count / 2) * width) % unit.size) (count - count / 2)
          pure (combineMissing ((count / 2) * width) left right)
        else pure none
      have body : BlockStateResult CheckCacheNone (fun missing => missing = none) (fun _ : ε => False) building := by
        dsimp only [building]
        split
        · exact BlockStateResult.pure _ _ _ _ rfl
        · rename_i notZero
          have nonzero : 0 < count := by
            have nonzero : count ≠ 0 := by simpa only [beq_iff_eq] using notZero
            omega
          split
          ·
            have checked : check ⟨width, .periodic unit.tree positive phase width⟩ = .ok none := by
              apply callbacks 0 nonzero ⟨width, .periodic unit.tree positive phase width⟩ rfl
              intro index inside
              simp only [get,Tree.get,if_pos inside,Nat.zero_mul,Nat.add_zero]
            apply BlockStateResult.lift
            rw [checked]
            rfl
          · split
            · have left : PhaseChecked check unit width phase (count / 2) := by
                intro slot inside image extent bytes
                exact callbacks slot (by omega) image extent bytes
              have right : PhaseChecked check unit width ((phase + (count / 2) * width) % unit.size) (count - count / 2) := by
                intro slot inside image extent bytes
                apply callbacks (count / 2 + slot) (by omega) image extent
                intro index inByte
                rw [bytes index inByte]
                apply congrArg unit.get
                rw [Nat.add_assoc,Nat.mod_add_mod]
                simp only [Nat.add_mul,Nat.add_assoc]
              apply BlockStateResult.bind _ (fun missing => missing = none) _ _ _ _
                (ih _ (by omega) phase left)
              intro first firstNone
              apply BlockStateResult.bind _ (fun missing => missing = none) _ _ _ _
                (ih _ (by omega) _ right)
              intro later laterNone
              subst first
              subst later
              exact BlockStateResult.pure _ _ _ _ rfl
            · exact BlockStateResult.pure _ _ _ _ rfl
      have finish (missing : Option Nat) (empty : missing = none) :
          BlockStateResult CheckCacheNone (fun result => result = none) (fun _ : ε => False) (do
            modify (fun cache : List CheckEntry => (phase,count,missing) :: cache)
            pure missing) := by
        intro cache cacheSafe
        subst missing
        refine ⟨rfl,?_⟩
        intro entry member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · rfl
        · exact cacheSafe entry member
      have finished := (BlockStateResult.bind _ (fun missing => missing = none) (fun result => result = none) _
        building _ body finish) entries safe
      by_cases zero : (count == 0) = true <;>
        by_cases direct : (width % unit.size == 0 || count == 1) = true <;>
          by_cases large : 2 ≤ count <;>
            simp only [building,zero,direct,large,Bool.false_eq_true,ite_true,ite_false,dif_pos,dif_neg,pure_bind,bind_assoc,
              block_state_pure_bind,block_state_bind_assoc] at finished ⊢ <;>
            exact finished

theorem CheckedBlocks.congr {ε : Type} {check : ByteImage → Except ε (Option Nat)}
    {first second : ByteImage} {width count : Nat}
    (same : ∀ index, second.get index = first.get index)
    (checked : CheckedBlocks check first width count) : CheckedBlocks check second width count := by
  intro slot inside image extent bytes
  apply checked slot inside image extent
  intro index inByte
  exact (bytes index inByte).trans (same _)

theorem CheckedBlocks.subrange {ε : Type} {check : ByteImage → Except ε (Option Nat)}
    {source : ByteImage} {width count : Nat} (checked : CheckedBlocks check source width count)
    (extent : source.size = width * count) (start length : Nat) (bounded : start + length ≤ count) :
    CheckedBlocks check (source.slice (start * width) (length * width)) width length := by
  intro slot inside image size bytes
  apply checked (start + slot) (by omega) image size
  intro index inByte
  have inRequest : slot * width + index < length * width := by
    simpa only [Nat.mul_comm length width] using slot_byte_bound width length slot index inside inByte
  have position : start * width + (slot * width + index) = (start + slot) * width + index := by
    simp only [Nat.add_mul,Nat.add_assoc]
  have inSource : start * width + (slot * width + index) < source.size := by
    rw [position,extent]
    exact slot_byte_bound width count (start + slot) index (by omega) inByte
  rw [bytes index inByte,get_slice source (start * width) (length * width) _ inRequest inSource,position]

private theorem periodicCheck_run_none {ε : Type} (check : ByteImage → Except ε (Option Nat))
    (unit : ByteImage) (positive : 0 < unit.size) (width phase count : Nat)
    (callbacks : PhaseChecked check unit width phase count) :
    ∃ cache, (periodicCheck check unit positive width phase count).run [] = .ok (none,cache) := by
  have valid := periodicCheck_none_of_windows check unit positive width phase count callbacks []
    (by intro entry member; cases member)
  cases run : (periodicCheck check unit positive width phase count).run [] with
  | error error => rw [run] at valid; exact False.elim valid
  | ok pair =>
    rw [run] at valid
    obtain ⟨missing,cache⟩ := pair
    obtain ⟨rfl,_safe⟩ := valid
    exact ⟨cache,rfl⟩

/-- Completeness of the actual checker traversal under logical block custody.
    Periodic-window observations are the sole external geometry premise; the
    proof layer discharges it from the original window theorem. -/
theorem checkBlocksSpec_none_of_checked_of_periods
    (windowLaw : ∀ (image unit : ByteImage) (phase : Nat), image.periodicWindow = some (unit,phase) →
      0 < unit.size ∧ ∀ index, index < image.size → image.get index = unit.get ((phase + index) % unit.size))
    {ε : Type} (check : ByteImage → Except ε (Option Nat)) (image : ByteImage) (width count : Nat)
    (extent : image.size = width * count) (checked : CheckedBlocks check image width count) :
    checkBlocksSpec check image width count = .ok none := by
  induction count using trustIrNatStrongInduction generalizing image with
  | ind count ih =>
    let source := WindowRuntime.canonicalImage image
    have sourceExtent : source.size = width * count := by rw [WindowRuntime.canonicalImage_size]; exact extent
    have sourceChecked : CheckedBlocks check source width count :=
      checked.congr (WindowRuntime.canonicalImage_get image)
    have periodicRun (unit : ByteImage) (phase : Nat) (positive : 0 < unit.size)
        (window : source.periodicWindow = some (unit,phase)) :
        (do let pair ← (periodicCheck check unit positive width phase count).run []; pure pair.1) = .ok none := by
      have phaseChecked : PhaseChecked check unit width phase count := by
        intro slot inside held size bytes
        apply sourceChecked slot inside held size
        intro index inByte
        rw [bytes index inByte,(windowLaw source unit phase window).2 _
          (by rw [sourceExtent]; exact slot_byte_bound width count slot index inside inByte)]
        simp only [Nat.add_assoc]
      obtain ⟨cache,run⟩ := periodicCheck_run_none check unit positive width phase count phaseChecked
      simp only [run,Bind.bind,Except.bind,Pure.pure,Except.pure]
    have emptyRun (nonzero : count ≠ 0) (zero : width = 0) : check empty = .ok none := by
      apply sourceChecked 0 (Nat.pos_of_ne_zero nonzero) empty (by rw [zero]; rfl)
      intro index inside
      omega
    have splitRun (nonzero : count ≠ 0) :
        (if large : 2 ≤ count then do
          let left ← checkBlocksSpec check (source.slice 0 ((count / 2) * width)) width (count / 2)
          let right ← checkBlocksSpec check (source.slice ((count / 2) * width) ((count - count / 2) * width)) width (count - count / 2)
          pure (combineMissing ((count / 2) * width) left right)
        else check (source.slice 0 width)) = .ok none := by
      by_cases large : 2 ≤ count
      · rw [dif_pos large]
        have total : count / 2 * width + (count - count / 2) * width = width * count := by
          rw [← Nat.add_mul,Nat.add_sub_of_le (Nat.div_le_self count 2),Nat.mul_comm]
        have leftBound : count / 2 * width ≤ source.size := by
          rw [sourceExtent,← total]
          exact Nat.le_add_right _ _
        have rightSpace : source.size - count / 2 * width = (count - count / 2) * width := by
          rw [sourceExtent,← total,Nat.add_sub_cancel_left]
        have leftExtent : (source.slice 0 ((count / 2) * width)).size = width * (count / 2) := by
          rw [size_slice,Nat.sub_zero,Nat.min_eq_left leftBound,Nat.mul_comm]
        have rightExtent : (source.slice ((count / 2) * width) ((count - count / 2) * width)).size = width * (count - count / 2) := by
          rw [size_slice,rightSpace,Nat.min_self,Nat.mul_comm]
        have leftChecked : CheckedBlocks check (source.slice 0 ((count / 2) * width)) width (count / 2) := by
          simpa only [Nat.zero_mul] using sourceChecked.subrange sourceExtent 0 (count / 2) (by omega)
        have rightChecked := sourceChecked.subrange sourceExtent (count / 2) (count - count / 2) (by omega)
        rw [ih _ (by omega) _ leftExtent leftChecked,ih _ (by omega) _ rightExtent rightChecked]
        rfl
      · rw [dif_neg large]
        have one : count = 1 := by omega
        have heldSize : (source.slice 0 width).size = width := by
          rw [size_slice,Nat.sub_zero,sourceExtent,one,Nat.mul_one,Nat.min_self]
        apply sourceChecked 0 (by omega) _ heldSize
        intro index inByte
        rw [get_slice source 0 width index inByte (by rw [sourceExtent,one,Nat.mul_one]; simpa only [Nat.zero_add] using inByte)]
        simp only [Nat.zero_add,Nat.zero_mul]
    rw [checkBlocksSpec]
    dsimp only
    have exactSize : (WindowRuntime.canonicalImage image).size = width * count := sourceExtent
    simp only [exactSize,beq_self_eq_true,ite_true]
    repeat' first
      | rfl
      | (solve | exact splitRun (by simpa only [beq_iff_eq] using (by assumption : ¬ (count == 0) = true)))
      | (solve | simpa only [dif_pos (by assumption : 2 ≤ count)] using splitRun (by simpa only [beq_iff_eq] using (by assumption : ¬ (count == 0) = true)))
      | (solve | simpa only [dif_neg (by assumption : ¬ 2 ≤ count)] using splitRun (by simpa only [beq_iff_eq] using (by assumption : ¬ (count == 0) = true)))
      | (solve | exact emptyRun (by simpa only [beq_iff_eq] using (by assumption : ¬ (count == 0) = true)) (by simpa only [beq_iff_eq] using (by assumption : (width == 0) = true)))
      | (solve | exact periodicRun _ _ _ (by assumption))
      | (simp only [pure_bind,bind_pure])
      | split
      | (dsimp only; split)
end TrustIr.ByteImage
