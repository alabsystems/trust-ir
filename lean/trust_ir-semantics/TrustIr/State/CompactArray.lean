-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import TrustIr.CompilerCompat

namespace TrustIr.CompactArray

open Std (Format)

/-- Strong induction stated through the common well-founded kernel API. -/
private theorem strongInduction {motive : Nat → Prop} (n : Nat)
    (ind : ∀ n, (∀ m, m < n → motive m) → motive n) : motive n :=
  Nat.lt_wfRel.wf.fix ind n

inductive Leaf (α : Type) : Nat → Type where
  | nil : Leaf α 0
  | cons {size : Nat} (head : α) (tail : Leaf α size) : Leaf α (size + 1)
  deriving Repr

def Leaf.get? {α : Type} {size : Nat} (leaf : Leaf α size) (index : Nat) : Option α :=
  match leaf, index with
  | .nil, _ => none
  | .cons head _, 0 => some head
  | .cons _ tail, index + 1 => tail.get? index

def Leaf.set? {α : Type} {size : Nat} (leaf : Leaf α size) (index : Nat) (value : α) :
    Option (Leaf α size) :=
  match leaf, index with
  | .nil, _ => none
  | .cons _ tail, 0 => some (.cons value tail)
  | .cons head tail, index + 1 => (tail.set? index value).map (Leaf.cons head)

theorem Leaf.get_set_hit {α : Type} {size : Nat} (leaf : Leaf α size)
    (index : Nat) (value : α) (updated : Leaf α size)
    (h : leaf.set? index value = some updated) : updated.get? index = some value := by
  induction leaf generalizing index with
  | nil => simp [Leaf.set?] at h
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [Leaf.set?, Option.some.injEq] at h
      cases h
      rfl
    | succ index =>
      cases ht : tail.set? index value with
      | none => simp [Leaf.set?, ht] at h
      | some next =>
        simp only [Leaf.set?, ht, Option.map, Option.some.injEq] at h
        cases h
        exact ih index next ht

theorem Leaf.get_set_other {α : Type} {size : Nat} (leaf : Leaf α size)
    (index other : Nat) (value : α) (updated : Leaf α size)
    (h : leaf.set? index value = some updated) (hne : other ≠ index) :
    updated.get? other = leaf.get? other := by
  induction leaf generalizing index other with
  | nil => simp [Leaf.set?] at h
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [Leaf.set?, Option.some.injEq] at h
      subst updated
      cases other with
      | zero => exact False.elim (hne rfl)
      | succ other => rfl
    | succ index =>
      cases ht : tail.set? index value with
      | none => simp [Leaf.set?, ht] at h
      | some next =>
        simp only [Leaf.set?, ht, Option.map, Option.some.injEq] at h
        subst updated
        cases other with
        | zero => rfl
        | succ other => exact ih index other next ht (by omega)

/-- Every branch bisects its logical extent. Update history cannot create
    a linear chain of successively appended singleton nodes. -/
inductive Tree (α : Type) : Nat → Type where
  | uniform (count : Nat) (value : α) : Tree α count
  | dense {size : Nat} (small : size ≤ 16) (values : Leaf α size) : Tree α size
  | split {size : Nat} (large : 2 ≤ size)
      (left : Tree α (size / 2)) (right : Tree α (size - size / 2)) : Tree α size
  /-- A finite cyclic window retains one nonempty immutable value template.
      Its extent need not be a multiple of the retained period. -/
  | periodic {period : Nat} (unit : Tree α period) (positive : 0 < period)
      (phase count : Nat) : Tree α count

def Tree.repr {α : Type} [Repr α] {size : Nat} : Tree α size → Format
  | .uniform count value => Format.paren (Format.text "uniform " ++ _root_.repr count ++
      Format.text " " ++ _root_.repr value)
  | .dense _ values => Format.paren (Format.text "dense " ++ _root_.repr values)
  | .split _ left right => Format.paren (Format.text "split " ++ left.repr ++
      Format.text " " ++ right.repr)
  | .periodic unit _ phase count => Format.paren (Format.text "periodic " ++ unit.repr ++
      Format.text " " ++ _root_.repr phase ++ Format.text " " ++ _root_.repr count)

instance {α : Type} [Repr α] {size : Nat} : Repr (Tree α size) where
  reprPrec tree _ := tree.repr

def Tree.get? {α : Type} {size : Nat} (tree : Tree α size) (index : Nat) : Option α :=
  match tree with
  | .uniform count value => if index < count then some value else none
  | .dense _ values => values.get? index
  | .split (size := size) _ left right =>
    if index < size / 2 then left.get? index else right.get? (index - size / 2)
  | .periodic (period := period) unit _ phase count =>
    if index < count then unit.get? ((phase + index) % period) else none

def Tree.nodes {α : Type} {size : Nat} : Tree α size → Nat
  | .uniform _ _ => 1
  | .dense _ _ => 1
  | .split _ left right => 1 + left.nodes + right.nodes
  | .periodic unit _ _ _ => 1 + unit.nodes

private theorem lowerHalf_lt (count : Nat) (large : 2 ≤ count) : count / 2 < count :=
  Nat.div_lt_self (Nat.lt_of_lt_of_le (by decide : 0 < 2) large) (by decide)

private theorem upperHalf_lt (count : Nat) (large : 2 ≤ count) : count - count / 2 < count := by
  have positive : 0 < count := Nat.lt_of_lt_of_le (by decide : 0 < 2) large
  have half : 1 ≤ count / 2 := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
    (by simpa only [Nat.one_mul] using large)
  exact Nat.sub_lt positive (Nat.lt_of_succ_le half)

def Tree.set? {α : Type} {size : Nat} (tree : Tree α size) (index : Nat) (value : α) :
    Option (Tree α size) :=
  if index < size then
    match tree with
    | .uniform count old =>
      if large : 2 ≤ count then
        if index < count / 2 then
          ((Tree.uniform (count / 2) old).set? index value).map
            (fun next => .split large next (.uniform (count - count / 2) old))
        else
          ((Tree.uniform (count - count / 2) old).set? (index - count / 2) value).map
            (fun next => .split large (.uniform (count / 2) old) next)
      else some (.uniform count value)
    | .periodic unit positive phase count =>
      if large : 2 ≤ count then
        if index < count / 2 then
          ((Tree.periodic unit positive phase (count / 2)).set? index value).map
            (fun next => .split large next (.periodic unit positive (phase + count / 2) (count - count / 2)))
        else
          ((Tree.periodic unit positive (phase + count / 2) (count - count / 2)).set? (index - count / 2) value).map
            (fun next => .split large (.periodic unit positive phase (count / 2)) next)
      else some (.uniform count value)
    | .dense small values => (values.set? index value).map (fun next => .dense small next)
    | .split large left right =>
      if index < size / 2 then
        (left.set? index value).map (fun next => .split large next right)
      else
        (right.set? (index - size / 2) value).map (fun next => .split large left next)
  else none
termination_by size
decreasing_by
  all_goals simp_wf
  · exact lowerHalf_lt _ (by assumption)
  · exact upperHalf_lt _ (by assumption)
  · exact lowerHalf_lt _ (by assumption)
  · exact upperHalf_lt _ (by assumption)
  · exact lowerHalf_lt _ (by assumption)
  · exact upperHalf_lt _ (by assumption)

theorem Tree.get_set_hit {α : Type} {size : Nat} (tree : Tree α size)
    (index : Nat) (value : α) (updated : Tree α size)
    (h : tree.set? index value = some updated) : updated.get? index = some value := by
  induction size using strongInduction generalizing index with
  | ind size ih =>
    cases tree with
    | uniform _ old =>
      rw [Tree.set?] at h
      by_cases hi : index < size
      · by_cases large : 2 ≤ size
        · by_cases side : index < size / 2
          · cases hu : (Tree.uniform (size / 2) old).set? index value with
            | none => simp [hi, large, side, hu] at h
            | some next =>
              simp only [hi, if_true, large, dite_true, side, hu,
                Option.map, Option.some.injEq] at h
              subst updated
              simp only [Tree.get?, side, if_true]
              exact ih _ (by omega) _ _ next hu
          · cases hu : (Tree.uniform (size - size / 2) old).set? (index - size / 2) value with
            | none => simp [hi, large, side, hu] at h
            | some next =>
              simp only [hi, if_true, large, dite_true, side, if_false, hu,
                Option.map, Option.some.injEq] at h
              subst updated
              simp only [Tree.get?, side, if_false]
              exact ih _ (by omega) _ _ next hu
        · simp only [hi, if_true, large, dite_false, Option.some.injEq] at h
          subst updated
          simp [Tree.get?, hi]
      · simp [hi] at h
    | periodic unit positive phase _ =>
      rw [Tree.set?] at h
      by_cases hi : index < size
      · by_cases large : 2 ≤ size
        · by_cases side : index < size / 2
          · cases hu : (Tree.periodic unit positive phase (size / 2)).set? index value with
            | none => simp [hi, large, side, hu] at h
            | some next =>
              simp only [hi, if_true, large, dite_true, side, hu,
                Option.map, Option.some.injEq] at h
              subst updated
              simp only [Tree.get?, side, if_true]
              exact ih _ (by omega) _ _ next hu
          · cases hu : (Tree.periodic unit positive (phase + size / 2) (size - size / 2)).set? (index - size / 2) value with
            | none => simp [hi, large, side, hu] at h
            | some next =>
              simp only [hi, if_true, large, dite_true, side, if_false, hu,
                Option.map, Option.some.injEq] at h
              subst updated
              simp only [Tree.get?, side, if_false]
              exact ih _ (by omega) _ _ next hu
        · simp only [hi, if_true, large, dite_false, Option.some.injEq] at h
          subst updated
          simp [Tree.get?, hi]
      · simp [hi] at h
    | dense small values =>
      rw [Tree.set?] at h
      by_cases hi : index < size
      · cases hu : values.set? index value with
        | none => simp [hi, hu] at h
        | some next =>
          simp only [hi, if_true, hu, Option.map, Option.some.injEq] at h
          subst updated
          exact values.get_set_hit index value next hu
      · simp [hi] at h
    | split large left right =>
      rw [Tree.set?] at h
      by_cases hi : index < size
      · by_cases side : index < size / 2
        · cases hu : left.set? index value with
          | none => simp [hi, side, hu] at h
          | some next =>
            simp only [hi, if_true, side, hu, Option.map, Option.some.injEq] at h
            subst updated
            simp only [Tree.get?, side, if_true]
            exact ih _ (by omega) _ _ next hu
        · cases hu : right.set? (index - size / 2) value with
          | none => simp [hi, side, hu] at h
          | some next =>
            simp only [hi, if_true, side, if_false, hu, Option.map, Option.some.injEq] at h
            subst updated
            simp only [Tree.get?, side, if_false]
            exact ih _ (by omega) _ _ next hu
      · simp [hi] at h

theorem Tree.get_split_uniform {α : Type} {size : Nat} (large : 2 ≤ size)
    (old : α) (other : Nat) :
    (Tree.split large (.uniform (size / 2) old)
      (.uniform (size - size / 2) old)).get? other =
      (Tree.uniform size old).get? other := by
  simp only [Tree.get?]
  split <;> split <;> (try split) <;> simp_all <;> omega

theorem Tree.get_split_periodic {α : Type} {period size : Nat} (large : 2 ≤ size)
    (unit : Tree α period) (positive : 0 < period) (phase other : Nat) :
    (Tree.split large (.periodic unit positive phase (size / 2))
      (.periodic unit positive (phase + size / 2) (size - size / 2))).get? other =
      (Tree.periodic unit positive phase size).get? other := by
  by_cases inside : other < size
  · by_cases side : other < size / 2
    · simp [Tree.get?, inside, side]
    · have right : other - size / 2 < size - size / 2 := by omega
      have arithmetic : phase + size / 2 + (other - size / 2) = phase + other := by omega
      simp [Tree.get?, inside, side, right, arithmetic]
  · have side : ¬ other < size / 2 := by omega
    have right : ¬ other - size / 2 < size - size / 2 := by omega
    simp [Tree.get?, inside, side, right]

theorem Tree.get_set_other {α : Type} {size : Nat} (tree : Tree α size)
    (index other : Nat) (value : α) (updated : Tree α size)
    (h : tree.set? index value = some updated) (hne : other ≠ index) :
    updated.get? other = tree.get? other := by
  induction size using strongInduction generalizing index other with
  | ind size ih =>
    cases tree with
    | uniform _ old =>
      rw [Tree.set?] at h
      by_cases hi : index < size
      · by_cases large : 2 ≤ size
        · by_cases side : index < size / 2
          · cases hu : (Tree.uniform (size / 2) old).set? index value with
            | none => simp [hi, large, side, hu] at h
            | some next =>
              simp only [hi, if_true, large, dite_true, side, hu,
                Option.map, Option.some.injEq] at h
              subst updated
              rw [← Tree.get_split_uniform large old other]
              simp only [Tree.get?]
              split
              · simpa only [Tree.get?, if_pos (by assumption : other < size / 2)] using
                  (ih _ (by omega) _ _ _ next hu hne)
              · rfl
          · cases hu : (Tree.uniform (size - size / 2) old).set? (index - size / 2) value with
            | none => simp [hi, large, side, hu] at h
            | some next =>
              simp only [hi, if_true, large, dite_true, side, if_false, hu,
                Option.map, Option.some.injEq] at h
              subst updated
              rw [← Tree.get_split_uniform large old other]
              simp only [Tree.get?]
              split
              · rfl
              · exact ih _ (by omega) _ _ _ next hu (by omega)
        · simp only [hi, if_true, large, dite_false, Option.some.injEq] at h
          subst updated
          have ho : ¬other < size := by omega
          simp [Tree.get?, ho]
      · simp [hi] at h
    | periodic unit positive phase _ =>
      rw [Tree.set?] at h
      by_cases hi : index < size
      · by_cases large : 2 ≤ size
        · by_cases side : index < size / 2
          · cases hu : (Tree.periodic unit positive phase (size / 2)).set? index value with
            | none => simp [hi, large, side, hu] at h
            | some next =>
              simp only [hi, if_true, large, dite_true, side, hu,
                Option.map, Option.some.injEq] at h
              subst updated
              rw [← Tree.get_split_periodic large unit positive phase other]
              simp only [Tree.get?]
              split
              · simpa only [Tree.get?, if_pos (by assumption : other < size / 2)] using
                  (ih _ (by omega) _ _ _ next hu hne)
              · rfl
          · cases hu : (Tree.periodic unit positive (phase + size / 2) (size - size / 2)).set? (index - size / 2) value with
            | none => simp [hi, large, side, hu] at h
            | some next =>
              simp only [hi, if_true, large, dite_true, side, if_false, hu,
                Option.map, Option.some.injEq] at h
              subst updated
              rw [← Tree.get_split_periodic large unit positive phase other]
              simp only [Tree.get?]
              split
              · rfl
              · exact ih _ (by omega) _ _ _ next hu (by omega)
        · simp only [hi, if_true, large, dite_false, Option.some.injEq] at h
          subst updated
          have ho : ¬other < size := by omega
          simp [Tree.get?, ho]
      · simp [hi] at h
    | dense small values =>
      rw [Tree.set?] at h
      by_cases hi : index < size
      · cases hu : values.set? index value with
        | none => simp [hi, hu] at h
        | some next =>
          simp only [hi, if_true, hu, Option.map, Option.some.injEq] at h
          subst updated
          exact values.get_set_other index other value next hu hne
      · simp [hi] at h
    | split large left right =>
      rw [Tree.set?] at h
      by_cases hi : index < size
      · by_cases side : index < size / 2
        · cases hu : left.set? index value with
          | none => simp [hi, side, hu] at h
          | some next =>
            simp only [hi, if_true, side, hu, Option.map, Option.some.injEq] at h
            subst updated
            simp only [Tree.get?]
            split
            · exact ih _ (by omega) _ _ _ next hu hne
            · rfl
        · cases hu : right.set? (index - size / 2) value with
          | none => simp [hi, side, hu] at h
          | some next =>
            simp only [hi, if_true, side, if_false, hu, Option.map, Option.some.injEq] at h
            subst updated
            simp only [Tree.get?]
            split
            · rfl
            · exact ih _ (by omega) _ _ _ next hu (by omega)
      · simp [hi] at h

theorem Leaf.set_none_iff {α : Type} {size : Nat} (leaf : Leaf α size)
    (index : Nat) (value : α) : leaf.set? index value = none ↔ size ≤ index := by
  induction leaf generalizing index with
  | nil => simp [Leaf.set?]
  | cons head tail ih =>
    cases index with
    | zero => simp [Leaf.set?]
    | succ index =>
      simp only [Leaf.set?]
      cases ht : tail.set? index value with
      | none => simpa [ht] using ih index
      | some next => simpa [ht] using ih index

theorem Tree.set_none_iff {α : Type} {size : Nat} (tree : Tree α size)
    (index : Nat) (value : α) : tree.set? index value = none ↔ size ≤ index := by
  induction size using strongInduction generalizing index with
  | ind size ih =>
    cases tree with
    | uniform _ old =>
      rw [Tree.set?]
      by_cases hi : index < size
      · simp only [hi, if_true, Nat.not_le.mpr hi, iff_false]
        by_cases large : 2 ≤ size
        · simp only [large, dite_true]
          split
          · have hr := ih _ (by omega) (.uniform (size / 2) old) index
            cases ht : (Tree.uniform (size / 2) old).set? index value with
            | none => simp [ht] at hr; omega
            | some next => simp [Option.map]
          · have hr := ih _ (by omega) (.uniform (size - size / 2) old) (index - size / 2)
            cases ht : (Tree.uniform (size - size / 2) old).set? (index - size / 2) value with
            | none => simp [ht] at hr; omega
            | some next => simp [Option.map]
        · simp [large]
      · simp [hi, Nat.le_of_not_lt hi]
    | periodic unit positive phase _ =>
      rw [Tree.set?]
      by_cases hi : index < size
      · simp only [hi, if_true, Nat.not_le.mpr hi, iff_false]
        by_cases large : 2 ≤ size
        · simp only [large, dite_true]
          split
          · have hr := ih _ (by omega) (.periodic unit positive phase (size / 2)) index
            cases ht : (Tree.periodic unit positive phase (size / 2)).set? index value with
            | none => simp [ht] at hr; omega
            | some next => simp [Option.map]
          · have hr := ih _ (by omega) (.periodic unit positive (phase + size / 2) (size - size / 2)) (index - size / 2)
            cases ht : (Tree.periodic unit positive (phase + size / 2) (size - size / 2)).set? (index - size / 2) value with
            | none => simp [ht] at hr; omega
            | some next => simp [Option.map]
        · simp [large]
      · simp [hi, Nat.le_of_not_lt hi]
    | dense small values =>
      rw [Tree.set?]
      by_cases hi : index < size
      · simp only [hi, if_true, Nat.not_le.mpr hi, iff_false]
        have hr := values.set_none_iff index value
        cases ht : values.set? index value with
        | none => simp [ht] at hr; omega
        | some next => simp [Option.map]
      · simp [hi, Nat.le_of_not_lt hi]
    | split large left right =>
      rw [Tree.set?]
      by_cases hi : index < size
      · simp only [hi, if_true, Nat.not_le.mpr hi, iff_false]
        split
        · have hr := ih _ (by omega) left index
          cases ht : left.set? index value with
          | none => simp [ht] at hr; omega
          | some next => simp [Option.map]
        · have hr := ih _ (by omega) right (index - size / 2)
          cases ht : right.set? (index - size / 2) value with
          | none => simp [ht] at hr; omega
          | some next => simp [Option.map]
      · simp [hi, Nat.le_of_not_lt hi]

def Tree.height {α : Type} {size : Nat} : Tree α size → Nat
  | .uniform _ _ => 1
  | .dense _ _ => 1
  | .split _ left right => max left.height right.height + 1
  | .periodic unit _ _ _ => unit.height + 1

def Tree.periodDepth {α : Type} {size : Nat} : Tree α size → Nat
  | .uniform _ _ | .dense _ _ => 0
  | .split _ left right => max left.periodDepth right.periodDepth
  | .periodic unit _ _ _ => unit.periodDepth + 1

def Tree.supportExtent {α : Type} {size : Nat} : Tree α size → Nat
  | .uniform count _ => count
  | .dense (size := size) _ _ => size
  | .split (size := size) _ left right => max size (max left.supportExtent right.supportExtent)
  | .periodic unit _ _ count => max count unit.supportExtent

/-- Logical extent bounds paths when there are no retained periodic templates.
    General periodic storage must also bound retained template depth. -/
theorem Tree.height_le_no_periods_of_le_pow {α : Type} {size : Nat} (tree : Tree α size)
    (bits : Nat) (bound : size ≤ 2 ^ bits) (noPeriods : tree.periodDepth = 0) : tree.height ≤ bits + 1 := by
  induction bits generalizing size with
  | zero =>
    cases tree with
    | uniform _ _ => simp [Tree.height]
    | dense _ _ => simp [Tree.height]
    | split large _ _ => simp only [Nat.pow_zero] at bound; omega
    | periodic unit positive phase count => simp [Tree.periodDepth] at noPeriods
  | succ bits ih =>
    cases tree with
    | uniform _ _ => simp [Tree.height]
    | dense _ _ => simp [Tree.height]
    | split large left right =>
      simp only [Nat.pow_succ] at bound
      have hl : size / 2 ≤ 2 ^ bits := by omega
      have hr : size - size / 2 ≤ 2 ^ bits := by omega
      have parts : left.periodDepth = 0 ∧ right.periodDepth = 0 := by
        simp only [Tree.periodDepth] at noPeriods
        constructor <;> omega
      have hleft := ih left hl parts.1
      have hright := ih right hr parts.2
      simp only [Tree.height]
      omega
    | periodic unit positive phase count => simp [Tree.periodDepth] at noPeriods

/-- Retained-support bounds include the root extent. -/
theorem Tree.extent_le_supportExtent {α : Type} {size : Nat} (tree : Tree α size) :
    size ≤ tree.supportExtent := by
  cases tree with
  | uniform _ _ => exact Nat.le_refl _
  | dense _ _ => exact Nat.le_refl _
  | split _ _ _ => exact Nat.le_max_left _ _
  | periodic _ _ _ _ => exact Nat.le_max_left _ _

/-- A finite window pays for its own balanced path and for every retained
    periodic-template level. Logical extent alone cannot bound template depth. -/
theorem Tree.height_le_with_periods {α : Type} {size : Nat} (tree : Tree α size)
    (localBits supportBits : Nat) (extentBound : size ≤ 2 ^ localBits)
    (support : tree.supportExtent ≤ 2 ^ supportBits) :
    tree.height ≤ localBits + 1 + tree.periodDepth * (supportBits + 1) := by
  induction tree generalizing localBits supportBits with
  | uniform count value => simp [Tree.height, Tree.periodDepth]
  | dense small values => simp [Tree.height, Tree.periodDepth]
  | @split size large left right ihl ihr =>
    have leftSupport : left.supportExtent ≤ 2 ^ supportBits := by
      simp only [Tree.supportExtent] at support
      omega
    have rightSupport : right.supportExtent ≤ 2 ^ supportBits := by
      simp only [Tree.supportExtent] at support
      omega
    cases localBits with
    | zero => simp only [Nat.pow_zero] at extentBound; omega
    | succ bits =>
      have halves : size / 2 ≤ 2 ^ bits ∧ size - size / 2 ≤ 2 ^ bits := by
        simp only [Nat.pow_succ] at extentBound
        constructor <;> omega
      have lh := ihl bits supportBits halves.1 leftSupport
      have rh := ihr bits supportBits halves.2 rightSupport
      have lp := Nat.mul_le_mul_right (supportBits + 1) (Nat.le_max_left left.periodDepth right.periodDepth)
      have rp := Nat.mul_le_mul_right (supportBits + 1) (Nat.le_max_right left.periodDepth right.periodDepth)
      simp only [Tree.height, Tree.periodDepth]
      omega
  | @periodic period unit positive phase count ih =>
    have unitSupport : unit.supportExtent ≤ 2 ^ supportBits := by
      simp only [Tree.supportExtent] at support
      omega
    have unitExtent : period ≤ 2 ^ supportBits := Nat.le_trans unit.extent_le_supportExtent unitSupport
    have bound := ih supportBits supportBits unitExtent unitSupport
    simp only [Tree.height, Tree.periodDepth, Nat.add_mul, Nat.one_mul]
    omega

theorem Tree.height_le_of_support_le_pow {α : Type} {size : Nat} (tree : Tree α size)
    (bits : Nat) (support : tree.supportExtent ≤ 2 ^ bits) :
    tree.height ≤ (tree.periodDepth + 1) * (bits + 1) := by
  have bound := tree.height_le_with_periods bits bits
    (Nat.le_trans tree.extent_le_supportExtent support) support
  simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using bound

/-- Copies only a bounded leaf from the source buffer. -/
def Leaf.ofArray {α : Type} (values : Array α) (start count : Nat)
    (_bound : start + count ≤ values.size) : Leaf α count :=
  match count with
  | 0 => .nil
  | count + 1 => .cons (values[start]'(by omega))
      (Leaf.ofArray values (start + 1) count (by omega))

/-- Splits buffer ranges without copying intermediate subarrays. -/
def Tree.ofArrayRange {α : Type} (values : Array α) (start count : Nat)
    (bound : start + count ≤ values.size) : Tree α count :=
  if small : count ≤ 16 then
    .dense small (Leaf.ofArray values start count bound)
  else
    .split (by omega)
      (Tree.ofArrayRange values start (count / 2) (by omega))
      (Tree.ofArrayRange values (start + count / 2) (count - count / 2) (by omega))
termination_by count
decreasing_by all_goals simp_wf; omega

def Tree.ofArray {α : Type} (values : Array α) : Tree α values.size :=
  Tree.ofArrayRange values 0 values.size (by omega)

theorem Leaf.get_ofArray {α : Type} (values : Array α) (start count index : Nat)
    (bound : start + count ≤ values.size) (inside : index < count) :
    (Leaf.ofArray values start count bound).get? index =
      some (values[start + index]'(by omega)) := by
  induction count generalizing start index with
  | zero => omega
  | succ count ih =>
    cases index with
    | zero => simp only [Leaf.ofArray, Leaf.get?, Nat.add_zero]
    | succ index =>
      simpa only [Leaf.ofArray, Leaf.get?, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using ih (start + 1) index (by omega) (by omega)

theorem Tree.get_ofArrayRange {α : Type} (values : Array α) (start count index : Nat)
    (bound : start + count ≤ values.size) (inside : index < count) :
    (Tree.ofArrayRange values start count bound).get? index =
      some (values[start + index]'(by omega)) := by
  induction count using strongInduction generalizing start index with
  | ind count ih =>
    rw [Tree.ofArrayRange]
    by_cases small : count ≤ 16
    · simp only [small, dite_true, Tree.get?]
      exact Leaf.get_ofArray values start count index bound inside
    · simp only [small, dite_false, Tree.get?]
      by_cases side : index < count / 2
      · simp only [side, if_true]
        exact ih _ (by omega) start index (by omega) side
      · simp only [side, if_false]
        have result := ih (count - count / 2) (by omega)
          (start + count / 2) (index - count / 2) (by omega) (by omega)
        have he : start + count / 2 + (index - count / 2) = start + index := by omega
        simpa only [he] using result

structure Packed (α : Type) where
  size : Nat
  tree : Tree α size
  deriving Repr

def Packed.uniform {α : Type} (count : Nat) (value : α) : Packed α :=
  ⟨count, .uniform count value⟩

def Packed.ofArray {α : Type} (values : Array α) : Packed α :=
  ⟨values.size, Tree.ofArray values⟩

def Packed.get? {α : Type} (values : Packed α) (index : Nat) : Option α :=
  values.tree.get? index

def Packed.set? {α : Type} (values : Packed α) (index : Nat) (value : α) : Option (Packed α) :=
  (values.tree.set? index value).map (fun tree => ⟨values.size, tree⟩)

/-- Every visible logical leaf position retains an actual value. -/
theorem Leaf.get_exists {α : Type} {size : Nat} (leaf : Leaf α size) (index : Nat) (inside : index < size) :
    ∃ value, leaf.get? index = some value := by
  induction leaf generalizing index with
  | nil => omega
  | cons value rest ih =>
    cases index with
    | zero => exact ⟨value,rfl⟩
    | succ index => exact ih index (by omega)

/-- All compact shapes have total in-range logical lookup. Hidden templates
    outside the visible count do not introduce extra logical positions. -/
theorem Tree.get_exists {α : Type} {size : Nat} (tree : Tree α size) (index : Nat) (inside : index < size) :
    ∃ value, tree.get? index = some value := by
  induction tree generalizing index with
  | uniform count value => exact ⟨value,by simp only [Tree.get?,if_pos inside]⟩
  | dense small values => exact values.get_exists index inside
  | @split size large left right first second =>
    by_cases before : index < size / 2
    · obtain ⟨value,found⟩ := first index before
      exact ⟨value,by simp only [Tree.get?,if_pos before,found]⟩
    · obtain ⟨value,found⟩ := second (index - size / 2) (by omega)
      exact ⟨value,by simp only [Tree.get?,if_neg before,found]⟩
  | @periodic period unit positive phase count ih =>
    obtain ⟨value,found⟩ := ih ((phase + index) % period) (Nat.mod_lt _ positive)
    exact ⟨value,by simp only [Tree.get?,if_pos inside,found]⟩

theorem Packed.get_exists {α : Type} (values : Packed α) (index : Nat) (inside : index < values.size) :
    ∃ value, values.get? index = some value := values.tree.get_exists index inside

theorem Leaf.get_none_of_ge {α : Type} {size : Nat} (leaf : Leaf α size)
    (index : Nat) (outside : size ≤ index) : leaf.get? index = none := by
  induction leaf generalizing index with
  | nil => rfl
  | cons head tail ih =>
    cases index with
    | zero => omega
    | succ index => exact ih index (by omega)

theorem Tree.get_none_of_ge {α : Type} {size : Nat} (tree : Tree α size)
    (index : Nat) (outside : size ≤ index) : tree.get? index = none := by
  induction tree generalizing index with
  | uniform count value => simp [Tree.get?, Nat.not_lt.mpr outside]
  | dense _ values => exact values.get_none_of_ge index outside
  | split large left right ihl ihr =>
    simp only [Tree.get?]
    rw [if_neg (by omega)]
    exact ihr _ (by omega)
  | periodic unit positive phase count ih => simp [Tree.get?, show ¬ index < count by omega]

theorem Tree.get_ofArray {α : Type} (values : Array α) (index : Nat) :
    (Tree.ofArray values).get? index = values[index]? := by
  by_cases inside : index < values.size
  · simp only [Tree.ofArray, getElem?_def, inside, dite_true]
    simpa only [Nat.zero_add] using
      Tree.get_ofArrayRange values 0 values.size index (by omega) inside
  · rw [Tree.get_none_of_ge _ index (Nat.le_of_not_lt inside)]
    simp [getElem?_def, inside]

end TrustIr.CompactArray

namespace TrustIr.CompactArray

/-- Inspect only the finite visible leaf range; skipped payloads are not
    passed to the callback. Counts beyond the leaf are naturally clipped. -/
def Leaf.checkRangeSpec {α ε : Type} (check : α → Except ε Unit) {size : Nat}
    (leaf : Leaf α size) (offset count : Nat) : Except ε Unit :=
  if count = 0 then pure () else
  match leaf with
  | .nil => pure ()
  | .cons head tail =>
    if offset = 0 then do check head; tail.checkRangeSpec check 0 (count - 1)
    else tail.checkRangeSpec check (offset - 1) count

/-- Pure visible stored-value validation. Source payloads outside the clipped
    range are not inspected, including invalid retained values. -/
def Tree.checkRangeSpec {α ε : Type} (check : α → Except ε Unit) {size : Nat}
    (tree : Tree α size) (offset count : Nat) : Except ε Unit :=
  let count := min count (size - offset)
  if count = 0 then pure () else
  match tree with
  | .uniform _ value => check value
  | .dense _ values => values.checkRangeSpec check offset count
  | .split (size := size) _ left right => do
    let before := min count (size / 2 - offset)
    left.checkRangeSpec check offset before
    right.checkRangeSpec check (offset + before - size / 2) (count - before)
  | .periodic (period := period) unit _ phase _ => do
    let start := (phase + offset) % period
    let before := min count (period - start)
    unit.checkRangeSpec check start before
    unit.checkRangeSpec check 0 (min period (count - before))

namespace StoredCheckRuntime

structure Stats where
  visits : Nat := 0
  hits : Nat := 0
  payloads : Nat := 0
  deriving Repr
end StoredCheckRuntime

/-- Check pure membership once per stored payload, in logical order. An empty
    uniform has no payload to inspect. This is not an effectful logical map. -/
@[nospecialize, trustIrExtern 5 "l_TrustIr_CompactArray_Leaf_checkStored(#1, #2, #3, #4, #5)"]
def Leaf.checkStored {α ε : Type} (check : α → Except ε Unit) {size : Nat} :
    Leaf α size → Except ε Unit
  | .nil => pure ()
  | .cons head tail => do check head; tail.checkStored check

@[nospecialize, trustIrExtern 5 "l_TrustIr_CompactArray_Tree_checkStored(#1, #2, #3, #4, #5)"]
def Tree.checkStored {α ε : Type} (check : α → Except ε Unit) {size : Nat} :
    Tree α size → Except ε Unit
  | .uniform count value => if count == 0 then pure () else check value
  | .dense _ values => values.checkStored check
  | .split _ left right => do left.checkStored check; right.checkStored check
  | .periodic (period := period) unit _ phase count =>
    if count = 0 then pure () else do
      let start := phase % period
      let before := min count (period - start)
      unit.checkRangeSpec check start before
      unit.checkRangeSpec check 0 (min period (count - before))

@[nospecialize, trustIrExtern 7 "l_TrustIr_CompactArray_Leaf_checkRange(#1, #2, #3, #4, #5, #6, #7)"]
def Leaf.checkRange {α ε : Type} (check : α → Except ε Unit) {size : Nat}
    (leaf : Leaf α size) (offset count : Nat) : Except ε Unit :=
  leaf.checkRangeSpec check offset count

@[nospecialize, trustIrExtern 7 "l_TrustIr_CompactArray_Tree_checkRange(#1, #2, #3, #4, #5, #6, #7)"]
def Tree.checkRange {α ε : Type} (check : α → Except ε Unit) {size : Nat}
    (tree : Tree α size) (offset count : Nat) : Except ε Unit :=
  tree.checkRangeSpec check offset count

theorem Leaf.checkRangeSpec_zero {α ε : Type} (check : α → Except ε Unit)
    {size : Nat} (leaf : Leaf α size) (offset : Nat) :
    leaf.checkRangeSpec check offset 0 = .ok () := by
  cases leaf <;> simp [Leaf.checkRangeSpec, Except.pure, Pure.pure]

theorem Leaf.checkRangeSpec_full {α ε : Type} (check : α → Except ε Unit)
    {size : Nat} (leaf : Leaf α size) :
    leaf.checkRangeSpec check 0 size = leaf.checkStored check := by
  induction leaf with
  | nil => rfl
  | cons head tail ih => simp [Leaf.checkRangeSpec, Leaf.checkStored, ih]

theorem Tree.checkRangeSpec_empty {α ε : Type} (check : α → Except ε Unit)
    {size : Nat} (tree : Tree α size) (offset count : Nat)
    (empty : count = 0 ∨ size ≤ offset) :
    tree.checkRangeSpec check offset count = .ok () := by
  have zero : min count (size - offset) = 0 := by
    rcases empty with zero | outside
    · simp [zero]
    · simp [Nat.sub_eq_zero_of_le outside]
  cases tree <;> simp [Tree.checkRangeSpec, zero, Except.pure, Pure.pure]

/-- Full-range validation preserves the complete result, including the actual
    first callback error, rather than merely agreeing on successful membership. -/
theorem Tree.checkRangeSpec_full {α ε : Type} (check : α → Except ε Unit)
    {size : Nat} (tree : Tree α size) :
    tree.checkRangeSpec check 0 size = tree.checkStored check := by
  induction tree with
  | uniform count value => simp [Tree.checkRangeSpec, Tree.checkStored]
  | @dense size small values =>
    rw [Tree.checkRangeSpec]
    simp only [Nat.sub_zero, Nat.min_self]
    by_cases zero : size = 0
    · subst size
      cases values
      rfl
    · rw [if_neg zero]
      exact values.checkRangeSpec_full check
  | @split size large left right ihl ihr =>
    have positive : size ≠ 0 := by omega
    have half : size / 2 ≤ size := Nat.div_le_self _ _
    rw [Tree.checkRangeSpec]
    simp only [Nat.sub_zero, Nat.min_self, if_neg positive, Nat.min_eq_right half,
      Nat.zero_add, Nat.sub_self]
    rw [ihl, ihr]
    rfl
  | periodic unit positive phase count ih =>
    simp only [Tree.checkRangeSpec, Tree.checkStored, Nat.sub_zero, Nat.min_self, Nat.add_zero]

theorem Tree.checkRange_full {α ε : Type} (check : α → Except ε Unit)
    {size : Nat} (tree : Tree α size) :
    tree.checkRange check 0 size = tree.checkStored check :=
  tree.checkRangeSpec_full check

private theorem unit_bind_ok_iff {ε : Type} (first later : Except ε Unit) :
    (do first; later) = .ok () ↔ first = .ok () ∧ later = .ok () := by
  cases first with
  | error error => simp [Except.bind, Bind.bind]
  | ok unit => cases unit; simp [Except.bind, Bind.bind]

theorem Leaf.checkRangeSpec_iff_get {α ε : Type} (check : α → Except ε Unit)
    {size : Nat} (leaf : Leaf α size) (offset count : Nat) :
    leaf.checkRangeSpec check offset count = .ok () ↔
      ∀ index value, offset ≤ index → index < offset + count →
        leaf.get? index = some value → check value = .ok () := by
  induction leaf generalizing offset count with
  | nil => simp [Leaf.checkRangeSpec, Leaf.get?, Except.pure, Pure.pure]
  | cons head tail ih =>
    by_cases zero : count = 0
    · subst count
      constructor
      · intro _ index value lower upper _
        omega
      · intro _
        exact Leaf.checkRangeSpec_zero check _ offset
    · cases offset with
      | zero =>
        rw [Leaf.checkRangeSpec, if_neg zero, if_pos rfl, unit_bind_ok_iff, ih]
        constructor
        · rintro ⟨first, rest⟩ index value lower upper found
          cases index with
          | zero =>
            have same : head = value := by simpa [Leaf.get?] using found
            simpa [same] using first
          | succ index => exact rest index value (by omega) (by omega) found
        · intro members
          refine ⟨members 0 head (by omega) (by omega) rfl, ?_⟩
          intro index value lower upper found
          exact members (index + 1) value (by omega) (by omega) found
      | succ offset =>
        rw [Leaf.checkRangeSpec, if_neg zero, if_neg (by omega), Nat.add_sub_cancel, ih]
        constructor
        · intro rest index value lower upper found
          cases index with
          | zero => omega
          | succ index => exact rest index value (by omega) (by omega) found
        · intro members index value lower upper found
          exact members (index + 1) value (by omega) (by omega) found

/-- Successful checking is exactly membership validity in the clipped visible
    range. Retained payloads outside this range impose no callback premise. -/
theorem Tree.checkRangeSpec_iff_get {α ε : Type} (check : α → Except ε Unit)
    {size : Nat} (tree : Tree α size) (offset count : Nat) :
    tree.checkRangeSpec check offset count = .ok () ↔
      ∀ index value, offset ≤ index → index < offset + min count (size - offset) →
        tree.get? index = some value → check value = .ok () := by
  induction tree generalizing offset count with
  | uniform size stored =>
    by_cases zero : min count (size - offset) = 0
    · rw [Tree.checkRangeSpec, if_pos zero]
      constructor
      · intro _ index value lower upper _
        omega
      · intro _; rfl
    · rw [Tree.checkRangeSpec, if_neg zero]
      constructor
      · intro checked index value lower upper found
        have inside : index < size := by have := Nat.min_le_right count (size - offset); omega
        have same : stored = value := by simpa [Tree.get?, inside] using found
        simpa [same] using checked
      · intro members
        exact members offset stored (Nat.le_refl _) (by omega)
          (by simp [Tree.get?, show offset < size by omega])
  | dense small values =>
    rw [Tree.checkRangeSpec]
    split
    · rename_i zero
      constructor
      · intro _ index value lower upper _
        omega
      · intro _; rfl
    · exact values.checkRangeSpec_iff_get check offset _
  | @split size large left right ihl ihr =>
    let visible := min count (size - offset)
    let before := min visible (size / 2 - offset)
    have beforeVisible : before ≤ visible := Nat.min_le_left _ _
    have beforeBound : before ≤ size / 2 - offset := Nat.min_le_right _ _
    by_cases zero : visible = 0
    · rw [Tree.checkRangeSpec, if_pos zero]
      constructor
      · intro _ index value lower upper _
        change index < offset + visible at upper
        omega
      · intro _; rfl
    · have leftCount : min before (size / 2 - offset) = before := Nat.min_eq_left beforeBound
      have rightCount : min (visible - before) (size - size / 2 - (offset + before - size / 2)) =
          visible - before := Nat.min_eq_left (by omega)
      rw [Tree.checkRangeSpec, if_neg zero]
      change (do left.checkRangeSpec check offset before
                 right.checkRangeSpec check (offset + before - size / 2) (visible - before)) = .ok () ↔ _
      rw [unit_bind_ok_iff, ihl, ihr]
      simp only [leftCount, rightCount]
      constructor
      · rintro ⟨first, later⟩ index value lower upper found
        change index < offset + visible at upper
        by_cases side : index < size / 2
        · apply first index value lower
          · dsimp [before] at *; omega
          · simpa [Tree.get?, side] using found
        · have crosses : size / 2 ≤ offset + before := by dsimp [before] at *; omega
          apply later (index - size / 2) value
          · dsimp [before] at *; omega
          · omega
          · simpa [Tree.get?, side] using found
      · intro members
        constructor
        · intro index value lower upper found
          have side : index < size / 2 := by omega
          apply members index value lower (by change index < offset + visible; omega)
          simpa [Tree.get?, side] using found
        · intro index value lower upper found
          have crosses : size / 2 ≤ offset + before := by dsimp [before] at *; omega
          apply members (index + size / 2) value (by omega)
          · change index + size / 2 < offset + visible
            omega
          · have side : ¬ index + size / 2 < size / 2 := by omega
            simpa [Tree.get?, side] using found

  | @periodic period unit positive phase size ih =>
    let visible := min count (size - offset)
    let start := (phase + offset) % period
    let before := min visible (period - start)
    let after := min period (visible - before)
    have startBound : start < period := Nat.mod_lt _ positive
    have visibleBound : visible ≤ size - offset := Nat.min_le_right _ _
    have beforeVisible : before ≤ visible := Nat.min_le_left _ _
    have beforeBound : before ≤ period - start := Nat.min_le_right _ _
    have afterPeriod : after ≤ period := Nat.min_le_left _ _
    have afterVisible : after ≤ visible - before := Nat.min_le_right _ _
    have phaseAt (index : Nat) (lower : offset ≤ index) :
        (phase + index) % period = (start + (index - offset)) % period := by
      have arithmetic : phase + index = (phase + offset) + (index - offset) := by omega
      rw [arithmetic, ← Nat.mod_add_mod (phase + offset) period (index - offset)]
    have wrapAt (index : Nat) (lower : before ≤ index) (full : before = period - start) :
        (start + index) % period = (index - before) % period := by
      have arithmetic : start + index = period + (index - before) := by omega
      rw [arithmetic]
      simp [Nat.add_mod]
    by_cases zero : visible = 0
    · rw [Tree.checkRangeSpec, if_pos zero]
      constructor
      · intro _ index value lower upper _
        change index < offset + visible at upper
        omega
      · intro _; rfl
    · rw [Tree.checkRangeSpec, if_neg zero]
      change (do unit.checkRangeSpec check start before
                 unit.checkRangeSpec check 0 after) = .ok () ↔ _
      rw [unit_bind_ok_iff, ih, ih]
      have leftCount : min before (period - start) = before := Nat.min_eq_left beforeBound
      have rightCount : min after (period - 0) = after := by simpa using Nat.min_eq_left afterPeriod
      simp only [leftCount, rightCount, Nat.zero_add]
      constructor
      · rintro ⟨first, later⟩ index value lower upper found
        change index < offset + visible at upper
        have sourceBound : index < size := by omega
        simp only [Tree.get?, if_pos sourceBound] at found
        rw [phaseAt index lower] at found
        by_cases early : index - offset < before
        · rw [Nat.mod_eq_of_lt (show start + (index - offset) < period by omega)] at found
          exact first (start + (index - offset)) value (by omega) (by omega) found
        · have full : before = period - start := by dsimp [before] at *; omega
          rw [wrapAt (index - offset) (by omega) full] at found
          have modulo : (index - offset - before) % period < period := Nat.mod_lt _ positive
          have bounded : (index - offset - before) % period ≤ index - offset - before := Nat.mod_le _ _
          apply later ((index - offset - before) % period) value (by omega)
          · dsimp [after]; omega
          · exact found
      · intro members
        constructor
        · intro index value lower upper found
          apply members (offset + (index - start)) value (by omega)
          · change offset + (index - start) < offset + visible
            omega
          · have sourceBound : offset + (index - start) < size := by omega
            rw [Tree.get?, if_pos sourceBound, phaseAt _ (by omega)]
            have relative : offset + (index - start) - offset = index - start := by omega
            have restore : start + (index - start) = index := by omega
            rw [relative, restore, Nat.mod_eq_of_lt (show index < period by omega)]
            exact found
        · intro index value lower upper found
          have full : before = period - start := by dsimp [before] at *; omega
          apply members (offset + before + index) value (by omega)
          · change offset + before + index < offset + visible
            omega
          · have sourceBound : offset + before + index < size := by omega
            rw [Tree.get?, if_pos sourceBound, phaseAt _ (by omega)]
            have relative : offset + before + index - offset = before + index := by omega
            rw [relative, wrapAt (before + index) (by omega) full]
            have restore : before + index - before = index := by omega
            rw [restore, Nat.mod_eq_of_lt (show index < period by omega)]
            exact found

/-- Logical contract of the public wrapper; this does not prove refinement
    of its unsafe runtime replacement. -/
theorem Tree.checkRange_iff_get {α ε : Type} (check : α → Except ε Unit)
    {size : Nat} (tree : Tree α size) (offset count : Nat) :
    tree.checkRange check offset count = .ok () ↔
      ∀ index value, offset ≤ index → index < offset + min count (size - offset) →
        tree.get? index = some value → check value = .ok () :=
  tree.checkRangeSpec_iff_get check offset count

/-- Changing only retained values outside the visible interval cannot change
    success. This concerns membership, not equality of callback error payloads. -/
theorem Tree.checkRangeSpec_congr_ok {α ε : Type} (check : α → Except ε Unit)
    {size : Nat} (left right : Tree α size) (offset count : Nat)
    (same : ∀ index, offset ≤ index → index < offset + min count (size - offset) →
      left.get? index = right.get? index) :
    left.checkRangeSpec check offset count = .ok () ↔
      right.checkRangeSpec check offset count = .ok () := by
  rw [left.checkRangeSpec_iff_get, right.checkRangeSpec_iff_get]
  constructor
  · intro checked index value lower upper found
    apply checked index value lower upper
    rw [same index lower upper]
    exact found
  · intro checked index value lower upper found
    apply checked index value lower upper
    rw [← same index lower upper]
    exact found

#trustIrAxioms Leaf.checkRangeSpec_full <= [propext, Quot.sound]
#trustIrAxioms Tree.checkRangeSpec_empty <= [propext]
#trustIrAxioms Tree.checkRangeSpec_full <= [propext, Quot.sound, Classical.choice]
#trustIrAxioms Tree.checkRange_full <= [propext, Quot.sound, Classical.choice]

#trustIrAxioms Leaf.checkRangeSpec_iff_get <= [propext, Quot.sound, Classical.choice]
#trustIrAxioms Tree.checkRangeSpec_iff_get <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms Tree.checkRange_iff_get <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms Tree.checkRangeSpec_congr_ok <= [propext, Classical.choice, Quot.sound]

namespace OrderedComparison

/-- Continue only after actual success; preserve the first false or error. -/
def andThen {ε : Type} (first later : Except ε Bool) : Except ε Bool :=
  match first with
  | .ok true => later
  | result => result

theorem andThen_assoc {ε : Type} (a b c : Except ε Bool) :
    andThen (andThen a b) c = andThen a (andThen b c) := by
  cases a with
  | error _ => rfl
  | ok value => cases value <;> rfl

theorem andThen_true_right {ε : Type} (a : Except ε Bool) :
    andThen a (.ok true) = a := by
  cases a with
  | error _ => rfl
  | ok value => cases value <;> rfl

theorem andThen_self {ε : Type} (a : Except ε Bool) : andThen a a = a := by
  cases a with
  | error _ => rfl
  | ok value => cases value <;> rfl

theorem bind_eq_andThen {ε : Type} (a b : Except ε Bool) :
    (do let passed ← a; if passed then b else pure false) = andThen a b := by
  cases a with
  | error _ => rfl
  | ok value => cases value <;> rfl

theorem andThen_eq_true {ε : Type} (a b : Except ε Bool) :
    andThen a b = .ok true ↔ a = .ok true ∧ b = .ok true := by
  cases a with
  | error _ => simp [andThen]
  | ok value => cases value <;> simp [andThen]

theorem andThen_stopped {ε : Type} (a b : Except ε Bool) (stopped : a ≠ .ok true) :
    andThen a b = a := by
  cases a with
  | error _ => rfl
  | ok value =>
    cases value with
    | false => rfl
    | true => exact False.elim (stopped rfl)

/-- Independent index-by-index comparison in increasing logical order.
    This is a mathematical specification, not a compact execution engine. -/
def run {ε : Type} (check : Nat → Except ε Bool) (start : Nat) : Nat → Except ε Bool
  | 0 => .ok true
  | count + 1 =>
    match check start with
    | .ok true => run check (start + 1) count
    | result => result

theorem run_zero {ε : Type} (check : Nat → Except ε Bool) (start : Nat) :
    run check start 0 = .ok true := rfl

theorem run_succ {ε : Type} (check : Nat → Except ε Bool) (start count : Nat) :
    run check start (count + 1) = andThen (check start) (run check (start + 1) count) := rfl

theorem congr {ε : Type} (left right : Nat → Except ε Bool)
    (startLeft startRight count : Nat)
    (agree : ∀ index, index < count → left (startLeft + index) = right (startRight + index)) :
    run left startLeft count = run right startRight count := by
  induction count generalizing startLeft startRight with
  | zero => rfl
  | succ count ih =>
    have first := agree 0 (by omega)
    simp only [Nat.add_zero] at first
    have rest := ih (startLeft + 1) (startRight + 1) (by
      intro index inside
      have next := agree (index + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next)
    simp only [run_succ, first, rest]

theorem append {ε : Type} (check : Nat → Except ε Bool) (start first later : Nat) :
    run check start (first + later) =
      andThen (run check start first) (run check (start + first) later) := by
  induction first generalizing start with
  | zero => simp [run_zero, andThen]
  | succ first ih =>
    simp only [Nat.succ_add, run_succ, ih]
    rw [andThen_assoc]
    congr 2

theorem constant {ε : Type} (result : Except ε Bool) (start count : Nat) :
    run (fun _ => result) start (count + 1) = result := by
  induction count generalizing start with
  | zero => exact andThen_true_right result
  | succ count ih =>
    change andThen result (run (fun _ => result) (start + 1) (count + 1)) = result
    rw [ih]
    exact andThen_self result

theorem success_iff {ε : Type} (check : Nat → Except ε Bool) (start count : Nat) :
    run check start count = .ok true ↔
      ∀ index, index < count → check (start + index) = .ok true := by
  induction count generalizing start with
  | zero =>
    constructor
    · intro _ index inside
      omega
    · intro _
      rfl
  | succ count ih =>
    rw [run_succ, andThen_eq_true, ih]
    constructor
    · intro passed index inside
      cases index with
      | zero => simpa only [Nat.add_zero] using passed.1
      | succ index =>
        have next := passed.2 index (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next
    · intro passed
      constructor
      · simpa only [Nat.add_zero] using passed 0 (by omega)
      · intro index inside
        have next := passed (index + 1) (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next

/-- A complete period preserves the entire result, including the first error.
    Only the ordered callback results repeat; no comparator law is assumed. -/
theorem period_prefix {ε : Type} (check : Nat → Except ε Bool) (period count : Nat)
    (positive : 0 < period) (enough : period ≤ count)
    (repeats : ∀ index, check index = check (index % period)) :
    run check 0 count = run check 0 period := by
  have split := append check 0 period (count - period)
  rw [Nat.add_sub_of_le enough] at split
  cases passed : run check 0 period with
  | error _ => rw [split, passed]; rfl
  | ok value =>
    cases value with
    | false => rw [split, passed]; rfl
    | true =>
      apply (success_iff check 0 count).mpr
      intro index _
      rw [Nat.zero_add, repeats index]
      simpa only [Nat.zero_add] using
        (success_iff check 0 period).mp passed (index % period) (Nat.mod_lt _ positive)

end OrderedComparison

/-- An operation borrows a cyclic source instead of constructing split views.
    The requested count is separate from the positive retained source extent. -/
private structure CyclicWindow (α : Type) where
  size : Nat
  positive : 0 < size
  tree : Tree α size
  phase : Nat

private def normalizeCyclic {α : Type} {size : Nat} (tree : Tree α size)
    (positive : 0 < size) (phase count : Nat) : CyclicWindow α :=
  let phase := phase % size
  let original : CyclicWindow α := ⟨size, positive, tree, phase⟩
  if count = 0 then original else
  match tree with
  | .uniform _ value => ⟨1, by decide, .uniform 1 value, 0⟩
  | .dense _ _ => original
  | .split (size := size) large left right =>
    if phase + count ≤ size / 2 then
      normalizeCyclic left (by omega) phase count
    else if size / 2 ≤ phase ∧ phase + count ≤ size then
      normalizeCyclic right (by omega) (phase - size / 2) count
    else original
  | .periodic (period := period) unit innerPositive innerPhase size =>
    if size % period = 0 ∨ phase + count ≤ size then
      normalizeCyclic unit innerPositive ((innerPhase + phase) % period) count
    else original

private def shiftCyclic {α : Type} (window : CyclicWindow α) (offset : Nat) : CyclicWindow α :=
  ⟨window.size, window.positive, window.tree, (window.phase + offset) % window.size⟩

private def cyclicRead {α : Type} (window : CyclicWindow α) (index : Nat) : Option α :=
  window.tree.get? ((window.phase + index) % window.size)

private theorem normalizeCyclic_get {α : Type} {size : Nat} (tree : Tree α size)
    (positive : 0 < size) (phase count index : Nat) (inside : index < count) :
    cyclicRead (normalizeCyclic tree positive phase count) index =
      tree.get? ((phase + index) % size) := by
  induction tree generalizing phase count with
  | uniform size value =>
    have nonzero : count ≠ 0 := by omega
    rw [normalizeCyclic, if_neg nonzero]
    simp [cyclicRead, Tree.get?, Nat.mod_lt _ positive, Nat.mod_one]
  | dense small values =>
    have nonzero : count ≠ 0 := by omega
    rw [normalizeCyclic, if_neg nonzero]
    simp only [cyclicRead, Nat.mod_add_mod]
  | @split size large left right ihl ihr =>
    have nonzero : count ≠ 0 := by omega
    have half : size / 2 ≤ size := Nat.div_le_self _ _
    simp only [normalizeCyclic, if_neg nonzero]
    split
    · rename_i contained
      rw [ihl]
      · have inLeft : phase % size + index < size / 2 := by omega
        have inRoot : phase % size + index < size := by omega
        have arithmetic : (phase + index) % size = phase % size + index := by
          rw [← Nat.mod_add_mod phase size index, Nat.mod_eq_of_lt inRoot]
        rw [arithmetic, Tree.get?, if_pos inLeft, Nat.mod_eq_of_lt inLeft]
      · exact inside
    · split
      · rename_i contained
        rw [ihr]
        · have inRoot : phase % size + index < size := by omega
          have inRight : phase % size - size / 2 + index < size - size / 2 := by omega
          have arithmetic : (phase + index) % size = phase % size + index := by
            rw [← Nat.mod_add_mod phase size index, Nat.mod_eq_of_lt inRoot]
          rw [arithmetic, Tree.get?, if_neg (by omega), Nat.mod_eq_of_lt inRight]
          congr 1
          omega
        · exact inside
      · simp only [cyclicRead, Nat.mod_add_mod]
  | @periodic period unit innerPositive innerPhase size ih =>
    have nonzero : count ≠ 0 := by omega
    simp only [normalizeCyclic, if_neg nonzero]
    split
    · rename_i usable
      rw [ih]
      · have inRoot : (phase + index) % size < size := Nat.mod_lt _ positive
        rw [Tree.get?, if_pos inRoot, Nat.mod_add_mod]
        congr 1
        rcases usable with aligned | contained
        · have divides : period ∣ size := Nat.dvd_of_mod_eq_zero aligned
          rw [← Nat.mod_add_mod phase size index]
          rw [Nat.add_mod innerPhase ((phase % size + index) % size),
            Nat.mod_mod_of_dvd _ divides, ← Nat.add_mod]
          simp only [Nat.add_assoc]
        · have inWindow : phase % size + index < size := by omega
          rw [← Nat.mod_add_mod phase size index, Nat.mod_eq_of_lt inWindow]
          congr 1
          omega
      · exact inside
    · simp only [cyclicRead, Nat.mod_add_mod]

private theorem cyclicRead_mod {α : Type} (window : CyclicWindow α) (joint index : Nat)
    (divides : window.size ∣ joint) :
    cyclicRead window (index % joint) = cyclicRead window index := by
  unfold cyclicRead
  congr 1
  rw [Nat.add_mod window.phase (index % joint), Nat.mod_mod_of_dvd _ divides, ← Nat.add_mod]

private def cyclicCheck {α β ε : Type} (eq : α → β → Except ε Bool)
    (left : CyclicWindow α) (right : CyclicWindow β) (index : Nat) : Except ε Bool :=
  match cyclicRead left index, cyclicRead right index with
  | some a, some b => eq a b
  | _, _ => .ok false

private theorem cyclicRead_shift {α : Type} (window : CyclicWindow α) (offset index : Nat) :
    cyclicRead (shiftCyclic window offset) index = cyclicRead window (offset + index) := by
  simp only [cyclicRead, shiftCyclic, Nat.mod_add_mod, Nat.add_assoc]

private theorem cyclicCheck_shift {α β ε : Type} (eq : α → β → Except ε Bool)
    (left : CyclicWindow α) (right : CyclicWindow β) (offset index : Nat) :
    cyclicCheck eq (shiftCyclic left offset) (shiftCyclic right offset) index =
      cyclicCheck eq left right (offset + index) := by
  simp only [cyclicCheck, cyclicRead_shift]

/-- Exact ordered comparison of cyclic source windows. A complete joint period
    suffices for an arbitrary pure comparator: the ordered input PAIRS repeat.
    There is no comparator reflexivity, symmetry or transitivity assumption. -/
private def cyclicEqSpec {α β ε : Type} (eq : α → β → Except ε Bool)
    (left : CyclicWindow α) (right : CyclicWindow β) (count : Nat) : Except ε Bool :=
  if zero : count = 0 then pure true else do
    let left := normalizeCyclic left.tree left.positive left.phase count
    let right := normalizeCyclic right.tree right.positive right.phase count
    match left.tree, right.tree with
    | .uniform _ a, .uniform _ b => eq a b
    | _, _ =>
      let joint := Nat.lcm left.size right.size
      if smaller : joint < count then cyclicEqSpec eq left right joint
      else if count = 1 then
        match cyclicRead left 0, cyclicRead right 0 with
        | some a, some b => eq a b
        | _, _ => pure false
      else
        let first ← cyclicEqSpec eq left right (count / 2)
        if first then cyclicEqSpec eq (shiftCyclic left (count / 2)) (shiftCyclic right (count / 2)) (count - count / 2)
        else pure false
termination_by count
decreasing_by
  all_goals
    simp_wf
    try dsimp only [left, right, joint] at *
    omega

private theorem cyclicEqSpec_ordered {α β ε : Type} (eq : α → β → Except ε Bool) :
    ∀ count (left : CyclicWindow α) (right : CyclicWindow β),
      cyclicEqSpec eq left right count = OrderedComparison.run (cyclicCheck eq left right) 0 count := by
  intro count
  induction count using strongInduction with
  | ind count ih =>
    intro left right
    by_cases zero : count = 0
    · subst count
      rw [cyclicEqSpec]
      rfl
    · let next (l : CyclicWindow α) (r : CyclicWindow β) : Except ε Bool :=
        let joint := Nat.lcm l.size r.size
        if joint < count then cyclicEqSpec eq l r joint
        else if count = 1 then cyclicCheck eq l r 0
        else do
          let first ← cyclicEqSpec eq l r (count / 2)
          if first then
            cyclicEqSpec eq (shiftCyclic l (count / 2))
              (shiftCyclic r (count / 2)) (count - count / 2)
          else pure false
      have nextLaw (l : CyclicWindow α) (r : CyclicWindow β) :
          next l r = OrderedComparison.run (cyclicCheck eq l r) 0 count := by
        dsimp only [next]
        split
        · rename_i smaller
          rw [ih _ smaller l r]
          apply (OrderedComparison.period_prefix (cyclicCheck eq l r)
            (Nat.lcm l.size r.size) count
            (Nat.pos_of_ne_zero (Nat.lcm_ne_zero (Nat.ne_of_gt l.positive)
              (Nat.ne_of_gt r.positive))) (Nat.le_of_lt smaller) _).symm
          intro index
          simp only [cyclicCheck]
          rw [cyclicRead_mod l _ index (Nat.dvd_lcm_left _ _),
            cyclicRead_mod r _ index (Nat.dvd_lcm_right _ _)]
        · split
          · rename_i one
            rw [one, OrderedComparison.run_succ, OrderedComparison.run_zero]
            exact (OrderedComparison.andThen_true_right _).symm
          · rename_i notOne
            have large : 2 ≤ count := by omega
            rw [ih _ (lowerHalf_lt count large) l r,
              ih _ (upperHalf_lt count large) (shiftCyclic l (count / 2))
                (shiftCyclic r (count / 2))]
            rw [OrderedComparison.bind_eq_andThen]
            change OrderedComparison.andThen
              (OrderedComparison.run (cyclicCheck eq l r) 0 (count / 2))
              (OrderedComparison.run
                (cyclicCheck eq (shiftCyclic l (count / 2)) (shiftCyclic r (count / 2)))
                0 (count - count / 2)) = _
            have shifted := OrderedComparison.congr
              (cyclicCheck eq (shiftCyclic l (count / 2)) (shiftCyclic r (count / 2)))
              (cyclicCheck eq l r) 0 (count / 2) (count - count / 2) (by
                intro index _
                simpa only [Nat.zero_add] using cyclicCheck_shift eq l r (count / 2) index)
            rw [shifted]
            simpa only [Nat.zero_add, Nat.add_sub_of_le (Nat.div_le_self count 2)] using
              (OrderedComparison.append (cyclicCheck eq l r) 0 (count / 2)
                (count - count / 2)).symm
      have uniformLaw (l : CyclicWindow α) (r : CyclicWindow β) (a : α) (b : β)
          (hl : l.tree = .uniform l.size a) (hr : r.tree = .uniform r.size b) :
          eq a b = OrderedComparison.run (cyclicCheck eq l r) 0 count := by
        have same := OrderedComparison.congr (cyclicCheck eq l r) (fun _ => eq a b)
          0 0 count (by
            intro index _
            simp only [Nat.zero_add, cyclicCheck, cyclicRead]
            rw [hl, hr]
            simp [Tree.get?, Nat.mod_lt _ l.positive, Nat.mod_lt _ r.positive])
        rw [same]
        cases count with
        | zero => exact False.elim (zero rfl)
        | succ count => exact (OrderedComparison.constant (eq a b) 0 count).symm
      have step (l : CyclicWindow α) (r : CyclicWindow β) :
          (match l.tree, r.tree with
          | .uniform _ a, .uniform _ b => eq a b
          | _, _ => next l r) = OrderedComparison.run (cyclicCheck eq l r) 0 count := by
        cases l with
        | mk ls lp lt phaseL =>
          cases r with
          | mk rs rp rt phaseR =>
            cases lt <;> cases rt
            all_goals first | exact nextLaw _ _ | exact uniformLaw _ _ _ _ rfl rfl
      let l := normalizeCyclic left.tree left.positive left.phase count
      let r := normalizeCyclic right.tree right.positive right.phase count
      calc
        cyclicEqSpec eq left right count = (match l.tree, r.tree with
          | .uniform _ a, .uniform _ b => eq a b
          | _, _ => next l r) := by
            rw [cyclicEqSpec, dif_neg zero]
            dsimp only [l, r, next, cyclicCheck]
            rfl
        _ = OrderedComparison.run (cyclicCheck eq l r) 0 count := step l r
        _ = OrderedComparison.run (cyclicCheck eq left right) 0 count := by
          apply OrderedComparison.congr
          intro index inside
          simp only [Nat.zero_add, cyclicCheck]
          have leftRead := normalizeCyclic_get left.tree left.positive left.phase count index inside
          have rightRead := normalizeCyclic_get right.tree right.positive right.phase count index inside
          change cyclicRead l index = cyclicRead left index at leftRead
          change cyclicRead r index = cyclicRead right index at rightRead
          rw [leftRead, rightRead]

namespace EqualityRuntime

structure Stats where
  visits : Nat := 0
  hits : Nat := 0
  deriving Repr
end EqualityRuntime

/-- Ordered comparison on the complete logical extent, retaining compressed
    periodic sources and actual finite restart boundaries. -/
def Tree.eqByMSpec {α β ε : Type} (eq : α → β → Except ε Bool) {size : Nat}
    (left : Tree α size) (right : Tree β size) : Except ε Bool :=
  if zero : size = 0 then pure true else
    cyclicEqSpec eq ⟨size, by omega, left, 0⟩ ⟨size, by omega, right, 0⟩ size

/-- The logical comparison remains the ordered pure specification. Compiled
    execution reuses completed comparisons within one fixed callback context. -/
@[nospecialize, trustIrExtern 7 "l_TrustIr_CompactArray_Tree_eqByM(#1, #2, #3, #4, #5, #6, #7)"]
def Tree.eqByM {α β ε : Type} (eq : α → β → Except ε Bool) {size : Nat}
    (left : Tree α size) (right : Tree β size) : Except ε Bool :=
  left.eqByMSpec eq right

/-- Increasing-index reference semantics. No normalization, compression or
    comparator equivalence law participates in this specification. -/
def Tree.eqByMOrderedSpec {α β ε : Type} (eq : α → β → Except ε Bool) {size : Nat}
    (left : Tree α size) (right : Tree β size) : Except ε Bool :=
  OrderedComparison.run (fun index =>
    match left.get? index, right.get? index with
    | some a, some b => eq a b
    | _, _ => .ok false) 0 size

/-- The optimized pure comparison preserves the complete ordered result,
    including the first callback error, for arbitrary element/error types. -/
theorem Tree.eqByMSpec_eq_ordered {α β ε : Type} (eq : α → β → Except ε Bool)
    {size : Nat} (left : Tree α size) (right : Tree β size) :
    left.eqByMSpec eq right = left.eqByMOrderedSpec eq right := by
  by_cases empty : size = 0
  · subst size
    rfl
  · rw [Tree.eqByMSpec, dif_neg empty, cyclicEqSpec_ordered]
    unfold Tree.eqByMOrderedSpec
    apply OrderedComparison.congr
    intro index inside
    simp only [Nat.zero_add, cyclicCheck, cyclicRead, Nat.mod_eq_of_lt inside]

/-- Contract for the public function's kernel body. This does not establish
    refinement of its unsafe runtime replacement. -/
theorem Tree.eqByM_eq_ordered {α β ε : Type} (eq : α → β → Except ε Bool)
    {size : Nat} (left : Tree α size) (right : Tree β size) :
    left.eqByM eq right = left.eqByMOrderedSpec eq right :=
  left.eqByMSpec_eq_ordered eq right

#trustIrAxioms OrderedComparison.period_prefix <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms Tree.eqByMSpec_eq_ordered <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms Tree.eqByM_eq_ordered <= [propext, Classical.choice, Quot.sound]

end TrustIr.CompactArray

namespace TrustIr.CompactArray

theorem Packed.get_ofArray {α : Type} (values : Array α) (index : Nat) :
    (Packed.ofArray values).get? index = values[index]? :=
  Tree.get_ofArray values index

theorem Packed.get_ofList {α : Type} (values : List α) (index : Nat) :
    (Packed.ofArray values.toArray).get? index = trustIrListGet? values index := by
  rw [Packed.get_ofArray, CompilerCompat.getElem?_toArray]

/-- Every logical member of a successful stored-payload check passes the
    same predicate. Uniform compression does not omit a logical value. -/
theorem Leaf.checkStored_get {α ε : Type} (check : α → Except ε Unit)
    {size : Nat} (leaf : Leaf α size) (index : Nat) (value : α)
    (checked : leaf.checkStored check = .ok ()) (found : leaf.get? index = some value) :
    check value = .ok () := by
  induction leaf generalizing index with
  | nil => simp [Leaf.get?] at found
  | cons head tail ih =>
    cases first : check head with
    | error error => simp [Leaf.checkStored, first, Except.bind, Except.pure, Bind.bind, Pure.pure] at checked
    | ok unit =>
      cases unit
      have rest : tail.checkStored check = .ok () := by
        simpa [Leaf.checkStored, first, Except.bind, Except.pure, Bind.bind, Pure.pure] using checked
      cases index with
      | zero =>
        have same : head = value := by simpa [Leaf.get?] using found
        simpa [same] using first
      | succ index => exact ih index rest found

theorem Tree.checkStored_get {α ε : Type} (check : α → Except ε Unit)
    {size : Nat} (tree : Tree α size) (index : Nat) (value : α)
    (checked : tree.checkStored check = .ok ()) (found : tree.get? index = some value) :
    check value = .ok ()  := by
  have inside : index < size := by
    by_cases bound : index < size
    · exact bound
    · have absent := tree.get_none_of_ge index (by omega)
      rw [absent] at found
      cases found
  have rangeChecked : tree.checkRangeSpec check 0 size = .ok () := by
    rw [tree.checkRangeSpec_full]
    exact checked
  exact (tree.checkRangeSpec_iff_get check 0 size).mp rangeChecked index value
    (by omega) (by simpa only [Nat.zero_add, Nat.sub_zero, Nat.min_self] using inside) found

theorem Leaf.checkStored_of_get {α ε : Type} (check : α → Except ε Unit)
    {size : Nat} (leaf : Leaf α size)
    (members : ∀ index value, leaf.get? index = some value → check value = .ok ()) :
    leaf.checkStored check = .ok () := by
  induction leaf with
  | nil => rfl
  | cons head tail ih =>
    have first := members 0 head rfl
    have rest := ih (fun index value found => members (index + 1) value found)
    simp [Leaf.checkStored, first, rest, Except.bind, Except.pure, Bind.bind, Pure.pure]

theorem Tree.checkStored_of_get {α ε : Type} (check : α → Except ε Unit)
    {size : Nat} (tree : Tree α size)
    (members : ∀ index value, tree.get? index = some value → check value = .ok ()) :
    tree.checkStored check = .ok ()  := by
  rw [← tree.checkRangeSpec_full]
  apply (tree.checkRangeSpec_iff_get check 0 size).mpr
  intro index value _ _ found
  exact members index value found

theorem Tree.checkStored_iff_get {α ε : Type} (check : α → Except ε Unit)
    {size : Nat} (tree : Tree α size) : tree.checkStored check = .ok () ↔
    ∀ index value, tree.get? index = some value → check value = .ok () :=
  ⟨fun checked index value found => tree.checkStored_get check index value checked found,
   tree.checkStored_of_get check⟩

end TrustIr.CompactArray
