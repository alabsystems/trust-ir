-- Copyright 2026 Andrew Yates | Apache-2.0
-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.CompilerCompat
import Init.Data.Nat.Log2

namespace TrustIr

/-- Exact sparse binary indexing of natural-number source identifiers. A node
    stores zero; its children consume the low even/odd bit of a positive key.
    No dense allocation, hashing, maximum identifier or execution fuel is used. -/
inductive NatIndexTree (α : Type) where
  | empty
  | node (value : Option α) (even odd : NatIndexTree α)

namespace NatIndexTree
variable {α : Type}

def value : NatIndexTree α → Option α
  | .empty => none
  | .node value _ _ => value

def even : NatIndexTree α → NatIndexTree α
  | .empty => .empty
  | .node _ even _ => even

def odd : NatIndexTree α → NatIndexTree α
  | .empty => .empty
  | .node _ _ odd => odd

def find : NatIndexTree α → Nat → Option α
  | .empty, _ => none
  | .node value even odd, key =>
    if key = 0 then value
    else if key % 2 = 0 then find even (key / 2)
    else find odd (key / 2)

private noncomputable def insertSpec (tree : NatIndexTree α) (key : Nat) (entry : α) : NatIndexTree α :=
  if zero : key = 0 then .node (some entry) tree.even tree.odd
  else if key % 2 = 0 then
    .node tree.value (insertSpec tree.even (key / 2) entry) tree.odd
  else .node tree.value tree.even (insertSpec tree.odd (key / 2) entry)
termination_by key
decreasing_by all_goals exact Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)

/-- New paths recurse on a derived structural witness. Existing paths use
    structural tree recursion below and carry no executable numeric witness. -/
private def pathBelow : (bound key : Nat) → key < bound → α → NatIndexTree α
  | 0, key, below, _ => False.elim (Nat.not_lt_zero key below)
  | bound + 1, key, below, entry =>
    if zero : key = 0 then .node (some entry) .empty .empty
    else if key % 2 = 0 then
      .node none (pathBelow bound (key / 2)
        (Nat.lt_of_lt_of_le (Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide))
          (Nat.le_of_lt_succ below)) entry) .empty
    else .node none .empty (pathBelow bound (key / 2)
        (Nat.lt_of_lt_of_le (Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide))
          (Nat.le_of_lt_succ below)) entry)

/-- Consume an existing routing constructor explicitly so native execution
    can reuse it when unshared. Only a new suffix constructs a numeric path. -/
def insert : NatIndexTree α → Nat → α → NatIndexTree α
  | .empty, key, entry => pathBelow (key + 1) key (Nat.lt_succ_self key) entry
  | .node stored even odd, key, entry =>
    if key = 0 then .node (some entry) even odd
    else if key % 2 = 0 then .node stored (insert even (key / 2) entry) odd
    else .node stored even (insert odd (key / 2) entry)

private theorem pathBelow_eq_spec (bound key : Nat) (below : key < bound) (entry : α) :
    pathBelow bound key below entry = insertSpec .empty key entry := by
  induction key using trustIrNatStrongInduction generalizing bound with
  | ind key ih =>
    cases bound with
    | zero => exact False.elim (Nat.not_lt_zero key below)
    | succ bound =>
      rw [pathBelow, insertSpec]
      simp only [value, even, odd]
      by_cases zero : key = 0
      · simp only [zero, dite_true, ite_true]
      · simp only [zero, dite_false, ite_false]
        have smaller : key / 2 < key :=
          Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)
        have childBound : key / 2 < bound :=
          Nat.lt_of_lt_of_le smaller (Nat.le_of_lt_succ below)
        split <;> rw [ih (key / 2) smaller bound childBound]

/-- Exact old one-step behavior for every tree, including arbitrary empty
    routing nodes. The well-founded specification is erased proof material. -/
theorem insert_unfold (tree : NatIndexTree α) (key : Nat) (entry : α) :
    tree.insert key entry =
      if key = 0 then .node (some entry) tree.even tree.odd
      else if key % 2 = 0 then
        .node tree.value (tree.even.insert (key / 2) entry) tree.odd
      else .node tree.value tree.even (tree.odd.insert (key / 2) entry) := by
  cases tree with
  | node stored even odd => rfl
  | empty =>
    have equation (id : Nat) :
        (NatIndexTree.empty : NatIndexTree α).insert id entry = insertSpec .empty id entry :=
      pathBelow_eq_spec (id + 1) id (Nat.lt_succ_self id) entry
    rw [equation, insertSpec]
    by_cases zero : key = 0
    · simp only [zero, dite_true, ite_true]
    · simp only [zero, dite_false, ite_false]
      split <;> simp only [value, even, odd] <;> rw [equation]

def depth : NatIndexTree α → Nat
  | .empty => 0
  | .node _ even odd => 1 + max even.depth odd.depth

/-- Actual nonempty nodes visited by lookup, independently of the value stored
    in them. An absent branch stops immediately. -/
def lookupSteps : NatIndexTree α → Nat → Nat
  | .empty, _ => 0
  | .node _ even odd, key =>
    1 + if key = 0 then 0
      else if key % 2 = 0 then lookupSteps even (key / 2)
      else lookupSteps odd (key / 2)

theorem lookupSteps_le_depth (tree : NatIndexTree α) (key : Nat) :
    tree.lookupSteps key ≤ tree.depth := by
  induction tree generalizing key with
  | empty => exact Nat.le_refl _
  | node value even odd evenIH oddIH =>
    simp only [lookupSteps, depth]
    split
    · omega
    · split
      · have bound := evenIH (key / 2); omega
      · have bound := oddIH (key / 2); omega

/-- Root zero slot plus one node for each significant binary digit. -/
def keyDepth (key : Nat) : Nat :=
  if zero : key = 0 then 1 else 1 + keyDepth (key / 2)
termination_by key
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)

theorem keyDepth_le_of_lt_two_pow (key bits : Nat) (bound : key < 2 ^ bits) :
    keyDepth key ≤ bits + 1 := by
  induction bits generalizing key with
  | zero =>
    have zero : key = 0 := by
      simp only [Nat.pow_zero] at bound
      omega
    subst key
    rw [keyDepth]
    simp
  | succ bits ih =>
    rw [keyDepth]
    by_cases zero : key = 0
    · simp [zero]
    · simp only [zero, dite_false, ite_false]
      have half : key / 2 < 2 ^ bits := by
        rw [Nat.pow_succ] at bound
        omega
      have smaller := ih (key / 2) half
      omega

theorem depth_insert_le (tree : NatIndexTree α) (key : Nat) (entry : α) :
    (tree.insert key entry).depth ≤ max tree.depth (keyDepth key) := by
  induction key using trustIrNatStrongInduction generalizing tree with
  | ind key ih =>
    rw [insert_unfold, keyDepth]
    by_cases zero : key = 0
    · cases tree <;> simp [zero, depth, even, odd] <;> omega
    · simp only [zero, dite_false, ite_false]
      have smaller : key / 2 < key :=
        Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)
      have evenBound := ih (key / 2) smaller tree.even
      have oddBound := ih (key / 2) smaller tree.odd
      split <;> cases tree <;> simp only [depth, even, odd] at * <;> omega

/-- Insertion preserves every routing node and extends precisely the key's
    binary path. This equality permits an exact cached depth, not a looser
    numeric-key or declaration-count substitute for the existing work metric. -/
theorem depth_insert_eq (tree : NatIndexTree α) (key : Nat) (entry : α) :
    (tree.insert key entry).depth = max tree.depth (keyDepth key) := by
  induction key using trustIrNatStrongInduction generalizing tree with
  | ind key ih =>
    rw [insert_unfold, keyDepth]
    by_cases zero : key = 0
    · cases tree <;> simp [zero, depth, even, odd] <;> omega
    · simp only [zero, dite_false, ite_false]
      have smaller : key / 2 < key :=
        Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)
      have evenBound := ih (key / 2) smaller tree.even
      have oddBound := ih (key / 2) smaller tree.odd
      split <;> cases tree <;> simp only [depth, even, odd] at * <;> omega

/-- The same logical depth computed with Lean core's exact logarithm. No
    custom native implementation, word-width restriction or extern is added. -/
def keyDepthFast (key : Nat) : Nat := if key = 0 then 1 else Nat.log2 key + 2

theorem keyDepthFast_eq (key : Nat) : keyDepthFast key = keyDepth key := by
  induction key using trustIrNatStrongInduction with
  | ind key ih =>
    rw [keyDepthFast, keyDepth]
    by_cases zero : key = 0
    · simp [zero]
    · simp only [zero, dite_false, ite_false]
      by_cases one : key = 1
      · subst key; first | rfl | simp [Nat.log2_def, keyDepth]
      · have large : key ≥ 2 := by omega
        have smaller : key / 2 < key :=
          Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)
        have nonzero : key / 2 ≠ 0 := by omega
        have child := ih (key / 2) smaller
        simp only [keyDepthFast, nonzero, if_false] at child
        have logarithm : Nat.log2 key = Nat.log2 (key / 2) + 1 := by
          first | rw [Nat.log2, if_pos large] | rw [Nat.log2_def, if_pos large]
        rw [logarithm]
        omega

theorem find_unfold (tree : NatIndexTree α) (key : Nat) :
    tree.find key = if key = 0 then tree.value
      else if key % 2 = 0 then tree.even.find (key / 2)
      else tree.odd.find (key / 2) := by
  cases tree <;> simp [find, value, even, odd]

/-- The index's fundamental extensional update law is proved directly over
    binary keys; no correctness law of an external container is assumed. -/
theorem find_insert (tree : NatIndexTree α) (key query : Nat) (entry : α) :
    (tree.insert key entry).find query =
      if query = key then some entry else tree.find query := by
  induction key using trustIrNatStrongInduction generalizing tree query with
  | ind key ih =>
    by_cases zero : key = 0
    · subst key
      rw [insert_unfold]
      simp only [if_pos rfl, dif_pos rfl, dite_true, ite_true]
      rw [find]
      by_cases qZero : query = 0
      · simp [qZero]
      · rw [if_neg qZero, if_neg qZero, find_unfold tree query]
        simp only [qZero, if_false]
    · have smaller : key / 2 < key :=
        Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)
      rw [insert_unfold]
      simp only [if_neg zero, dif_neg zero]
      by_cases qZero : query = 0
      · subst query
        have neq : 0 ≠ key := Ne.symm zero
        split <;> simp [find_unfold, neq, value, even, odd]
      · by_cases kEven : key % 2 = 0 <;> by_cases qEven : query % 2 = 0
        · rw [if_pos kEven, find, if_neg qZero, if_pos qEven, ih _ smaller]
          rw [find_unfold tree query, if_neg qZero, if_pos qEven]
          have same : query / 2 = key / 2 ↔ query = key := by omega
          simp only [same]
        · rw [if_pos kEven, find, if_neg qZero, if_neg qEven]
          rw [find_unfold tree query, if_neg qZero, if_neg qEven]
          have neq : query ≠ key := by omega
          simp only [neq, if_false, odd]
        · rw [if_neg kEven, find, if_neg qZero, if_pos qEven]
          rw [find_unfold tree query, if_neg qZero, if_pos qEven]
          have neq : query ≠ key := by omega
          simp only [neq, if_false, even]
        · rw [if_neg kEven, find, if_neg qZero, if_neg qEven, ih _ smaller]
          rw [find_unfold tree query, if_neg qZero, if_neg qEven]
          have same : query / 2 = key / 2 ↔ query = key := by omega
          simp only [same]

end NatIndexTree

end TrustIr
