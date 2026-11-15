-- Copyright 2026 Andrew Yates | Apache-2.0
import Lean.Data.RBMap
import Init.Data.Nat.Compare

namespace TrustIr.NatRBMapInsert
open Lean
variable {α : Type}

/-- In-order data of the actual pinned RBNode. Colors are irrelevant to
    lookup correctness; no red/black-height invariant is assumed. -/
def rows : RBNode Nat (fun _ => α) → List (Nat × α)
  | .leaf => []
  | .node _ left key value right => rows left ++ (key, value) :: rows right

inductive Ascending : List (Nat × α) → Prop where
  | nil : Ascending []
  | cons {head tail} (rest : Ascending tail)
      (above : ∀ row ∈ tail, head.1 < row.1) : Ascending (head :: tail)

def Ordered (tree : RBNode Nat (fun _ => α)) : Prop := Ascending (rows tree)

theorem Ascending.left {left right : List (Nat × α)} (ordered : Ascending (left ++ right)) :
    Ascending left := by
  induction left with
  | nil => exact .nil
  | cons head tail ih =>
    cases ordered with
    | cons rest above =>
      exact .cons (ih rest) (fun row member => above row (by first | exact List.mem_append_of_mem_left right member | exact (show row ∈ tail ++ right from List.mem_append.mpr (Or.inl member))))

theorem Ascending.right {left right : List (Nat × α)} (ordered : Ascending (left ++ right)) :
    Ascending right := by
  induction left with
  | nil => exact ordered
  | cons head tail ih => cases ordered with | cons rest _ => exact ih rest

theorem Ascending.cross {left right : List (Nat × α)} (ordered : Ascending (left ++ right)) :
    ∀ a ∈ left, ∀ b ∈ right, a.1 < b.1 := by
  induction left with
  | nil => intro a member; cases member
  | cons head tail ih =>
    cases ordered with
    | cons rest above =>
      intro a member b rightMember
      cases member with
      | head => exact above b (by first | exact List.mem_append_of_mem_right tail rightMember | exact (show b ∈ tail ++ right from List.mem_append.mpr (Or.inr rightMember)))
      | tail _ member => exact ih rest a member b rightMember

theorem ordered_node {color : RBColor} {left right : RBNode Nat (fun _ => α)} {key : Nat} {value : α}
    (ordered : Ordered (.node color left key value right)) :
    Ordered left ∧ Ordered right ∧ (∀ row ∈ rows left, row.1 < key) ∧
      (∀ row ∈ rows right, key < row.1) := by
  have all : Ascending (rows left ++ (key, value) :: rows right) := ordered
  have suffix := all.right
  cases suffix with
  | cons rightOrdered above =>
    exact ⟨all.left, rightOrdered,
      fun row member => all.cross row member (key, value) (List.Mem.head _), above⟩

theorem rows_balance1 (left right : RBNode Nat (fun _ => α)) (key : Nat) (value : α) :
    rows (RBNode.balance1 left key value right) = rows left ++ (key, value) :: rows right := by
  unfold RBNode.balance1
  split <;> simp only [rows, List.append_assoc, List.cons_append]

theorem rows_balance2 (left right : RBNode Nat (fun _ => α)) (key : Nat) (value : α) :
    rows (RBNode.balance2 left key value right) = rows left ++ (key, value) :: rows right := by
  unfold RBNode.balance2
  split <;> simp only [rows, List.append_assoc, List.cons_append]

theorem rows_setBlack (tree : RBNode Nat (fun _ => α)) : rows tree.setBlack = rows tree := by
  cases tree <;> rfl

def insertRows (key : Nat) (value : α) : List (Nat × α) → List (Nat × α)
  | [] => [(key, value)]
  | head :: tail =>
    match compare key head.1 with
    | .lt => (key, value) :: head :: tail
    | .eq => (key, value) :: tail
    | .gt => head :: insertRows key value tail

theorem insertRows_mem (key : Nat) (value : α) (source : List (Nat × α))
    (row : Nat × α) (member : row ∈ insertRows key value source) :
    row = (key, value) ∨ row ∈ source := by
  induction source with
  | nil => cases member with | head => exact Or.inl rfl | tail _ impossible => cases impossible
  | cons head tail ih =>
    cases comparison : compare key head.1 <;> simp only [insertRows, comparison] at member
    · cases member with
      | head => exact Or.inl rfl
      | tail _ member => exact Or.inr member
    · cases member with
      | head => exact Or.inl rfl
      | tail _ member => exact Or.inr (List.Mem.tail _ member)
    · cases member with
      | head => exact Or.inr (List.Mem.head _)
      | tail _ member =>
        cases ih member with
        | inl same => exact Or.inl same
        | inr original => exact Or.inr (List.Mem.tail _ original)

theorem Ascending.insert_rows {source : List (Nat × α)} (ordered : Ascending source)
    (key : Nat) (value : α) : Ascending (insertRows key value source) := by
  induction ordered with
  | nil => exact .cons .nil (fun _ member => nomatch member)
  | @cons head tail rest above ih =>
    cases comparison : compare key head.1 with
    | lt =>
      simp only [insertRows, comparison]
      refine .cons (.cons rest above) ?_
      intro row member
      cases member with
      | head => exact Nat.compare_eq_lt.mp comparison
      | tail _ member => exact Nat.lt_trans (Nat.compare_eq_lt.mp comparison) (above row member)
    | eq =>
      simp only [insertRows, comparison]
      exact .cons rest (fun row member => (Nat.compare_eq_eq.mp comparison) ▸ above row member)
    | gt =>
      simp only [insertRows, comparison]
      refine .cons ih ?_
      intro row member
      cases insertRows_mem key value tail row member with
      | inl same => cases same; exact Nat.compare_eq_gt.mp comparison
      | inr original => exact above row original

theorem insertRows_append_before (key : Nat) (value : α) (initialRows suffix : List (Nat × α))
    (head : Nat × α) (before : key < head.1) :
    insertRows key value (initialRows ++ head :: suffix) = insertRows key value initialRows ++ head :: suffix := by
  induction initialRows with
  | nil => simp only [List.nil_append, insertRows, Nat.compare_eq_lt.mpr before, List.cons_append]
  | cons first rest ih =>
    cases comparison : compare key first.1 <;>
      simp only [List.cons_append, insertRows, comparison, ih]
    all_goals first | rfl | exact congrArg (first :: ·) ih

theorem insertRows_skip_prefix (key : Nat) (value : α) (initialRows suffix : List (Nat × α))
    (before : ∀ row ∈ initialRows, row.1 < key) :
    insertRows key value (initialRows ++ suffix) = initialRows ++ insertRows key value suffix := by
  induction initialRows with
  | nil => rfl
  | cons head tail ih =>
    have atHead : compare key head.1 = .gt := Nat.compare_eq_gt.mpr (before head (List.Mem.head _))
    simp only [List.cons_append, insertRows, atHead]
    exact congrArg (head :: ·) (ih (fun row member => before row (List.Mem.tail _ member)))

theorem rows_ins (tree : RBNode Nat (fun _ => α)) (ordered : Ordered tree) (key : Nat) (value : α) :
    rows (tree.ins compare key value) = insertRows key value (rows tree) := by
  induction tree with
  | leaf => rfl
  | node color left root old right ihLeft ihRight =>
    obtain ⟨leftOrdered, rightOrdered, leftBefore, _rightAfter⟩ := ordered_node ordered
    cases comparison : compare key root with
    | lt =>
      cases color <;>
        simp only [RBNode.ins, comparison, rows_balance1, rows, ihLeft leftOrdered]
      all_goals exact (insertRows_append_before key value (rows left) (rows right)
        (root, old) (Nat.compare_eq_lt.mp comparison)).symm
    | gt =>
      have skip : insertRows key value (rows left ++ (root, old) :: rows right) =
          rows left ++ insertRows key value ((root, old) :: rows right) :=
        insertRows_skip_prefix key value _ _
          (fun row member => Nat.lt_trans (leftBefore row member) (Nat.compare_eq_gt.mp comparison))
      cases color <;>
        simp only [RBNode.ins, comparison, rows_balance2, rows, ihRight rightOrdered,
          skip, insertRows, comparison]
    | eq =>
      have skip : insertRows key value (rows left ++ (root, old) :: rows right) =
          rows left ++ insertRows key value ((root, old) :: rows right) :=
        insertRows_skip_prefix key value _ _
          (fun row member => (Nat.compare_eq_eq.mp comparison) ▸ leftBefore row member)
      cases color <;> simp only [RBNode.ins, comparison, rows, skip, insertRows, comparison]

theorem rows_insert (tree : RBNode Nat (fun _ => α)) (ordered : Ordered tree) (key : Nat) (value : α) :
    rows (tree.insert compare key value) = insertRows key value (rows tree) := by
  unfold RBNode.insert
  split <;> simp only [rows_setBlack, rows_ins tree ordered]

theorem ordered_insert (tree : RBNode Nat (fun _ => α)) (ordered : Ordered tree) (key : Nat) (value : α) :
    Ordered (tree.insert compare key value) := by
  change Ascending (rows (tree.insert compare key value))
  rw [rows_insert tree ordered]
  exact ordered.insert_rows key value

def lookupRows : List (Nat × α) → Nat → Option α
  | [], _ => none
  | head :: tail, query => if query = head.1 then some head.2 else lookupRows tail query

theorem lookupRows_append (left right : List (Nat × α)) (query : Nat) :
    lookupRows (left ++ right) query =
      match lookupRows left query with
      | none => lookupRows right query
      | some value => some value := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.cons_append, lookupRows]
    split
    · rfl
    · exact ih

theorem lookupRows_none (source : List (Nat × α)) (query : Nat)
    (absent : ∀ row ∈ source, query ≠ row.1) : lookupRows source query = none := by
  induction source with
  | nil => rfl
  | cons head tail ih =>
    rw [lookupRows, if_neg (absent head (List.Mem.head _))]
    exact ih (fun row member => absent row (List.Mem.tail _ member))

theorem lookupRows_insert (source : List (Nat × α)) (key query : Nat) (value : α) :
    lookupRows (insertRows key value source) query =
      if query = key then some value else lookupRows source query := by
  induction source with
  | nil => simp only [insertRows, lookupRows]
  | cons head tail ih =>
    cases comparison : compare key head.1 with
    | lt => simp only [insertRows, comparison, lookupRows]
    | eq =>
      have same := Nat.compare_eq_eq.mp comparison
      have original : lookupRows (head :: tail) query =
          if query = key then some head.2 else lookupRows tail query := by
        simp only [lookupRows, same]
      rw [insertRows, comparison, lookupRows, original]
      split <;> simp_all only [if_pos, if_neg]
    | gt =>
      have different : key ≠ head.1 := by have order := Nat.compare_eq_gt.mp comparison; omega
      simp only [insertRows, comparison, lookupRows, ih]
      by_cases atKey : query = key <;> by_cases atHead : query = head.1 <;> simp_all

theorem find_eq_lookupRows (tree : RBNode Nat (fun _ => α)) (ordered : Ordered tree) (query : Nat) :
    tree.find compare query = lookupRows (rows tree) query := by
  induction tree with
  | leaf => rfl
  | node color left key value right ihLeft ihRight =>
    obtain ⟨leftOrdered, rightOrdered, leftBefore, rightAfter⟩ := ordered_node ordered
    cases comparison : compare query key with
    | lt =>
      have order := Nat.compare_eq_lt.mp comparison
      have absent : lookupRows ((key, value) :: rows right) query = none :=
        lookupRows_none _ query (by
          intro row member
          cases member with
          | head => simp only; omega
          | tail _ member => have later := rightAfter row member; omega)
      simp only [RBNode.find, comparison, ihLeft leftOrdered, rows, lookupRows_append, absent]
      cases lookupRows (rows left) query <;> rfl
    | eq =>
      have same := Nat.compare_eq_eq.mp comparison
      have absent : lookupRows (rows left) query = none :=
        lookupRows_none _ query (fun row member => by have before := leftBefore row member; omega)
      have atRoot : lookupRows ((key, value) :: rows right) query = some value := by
        simp only [lookupRows, if_pos same]
      simp only [RBNode.find, comparison, rows, lookupRows_append, absent, atRoot]
    | gt =>
      have order := Nat.compare_eq_gt.mp comparison
      have absent : lookupRows (rows left) query = none :=
        lookupRows_none _ query (fun row member => by have before := leftBefore row member; omega)
      have different : query ≠ key := by omega
      simp only [RBNode.find, comparison, ihRight rightOrdered, rows, lookupRows_append,
        absent, lookupRows, if_neg different]

theorem find_insert (tree : RBNode Nat (fun _ => α)) (ordered : Ordered tree) (key query : Nat) (value : α) :
    (tree.insert compare key value).find compare query =
      if query = key then some value else tree.find compare query := by
  rw [find_eq_lookupRows _ (ordered_insert tree ordered key value), rows_insert tree ordered,
    lookupRows_insert, find_eq_lookupRows tree ordered]

/-- An actual insert-only history. This deliberately does not assert a law
    for arbitrary erased maps or turn Lean's history tag into an axiom. -/
inductive InsertOnly : RBMap Nat α compare → Prop where
  | empty : InsertOnly (mkRBMap Nat α compare)
  | insert {map : RBMap Nat α compare} (history : InsertOnly map) (key : Nat) (value : α) :
      InsertOnly (map.insert key value)

theorem InsertOnly.ordered {map : RBMap Nat α compare} (history : InsertOnly map) : Ordered map.1 := by
  induction history with
  | empty => exact .nil
  | @insert map _history key value ih => exact ordered_insert map.1 ih key value

theorem find?_empty (query : Nat) : (mkRBMap Nat α compare).find? query = none := rfl

theorem find?_insert {map : RBMap Nat α compare} (history : InsertOnly map) (key query : Nat) (value : α) :
    (map.insert key value).find? query = if query = key then some value else map.find? query :=
  find_insert map.1 history.ordered key query value

variable {ρ : Type}

def prefer (original fallback : Option α) : Option α :=
  match original with
  | some value => some value
  | none => fallback

def firstValue (key : ρ → Nat) (value : ρ → α) : List ρ → Nat → Option α
  | [], _ => none
  | head :: tail, query =>
    if query = key head then some (value head) else firstValue key value tail query

/-- Exactly the insert-only, first-wins fold used by original header lookup.
    A stored `none` payload is an occupied entry, not an absent map key. -/
def firstWinsFrom (key : ρ → Nat) (value : ρ → α) (entries : List ρ)
    (initial : RBMap Nat α compare) : RBMap Nat α compare :=
  entries.foldl (fun table row =>
    if table.contains (key row) then table else table.insert (key row) (value row)) initial

theorem firstWinsFrom_insertOnly (key : ρ → Nat) (value : ρ → α) (entries : List ρ)
    (initial : RBMap Nat α compare) (history : InsertOnly initial) :
    InsertOnly (firstWinsFrom key value entries initial) := by
  induction entries generalizing initial with
  | nil => exact history
  | cons head tail ih =>
    simp only [firstWinsFrom, List.foldl_cons]
    split
    · exact ih initial history
    · exact ih (initial.insert (key head) (value head)) (.insert history (key head) (value head))

theorem firstWinsFrom_find (key : ρ → Nat) (value : ρ → α) (entries : List ρ)
    (initial : RBMap Nat α compare) (history : InsertOnly initial) (query : Nat) :
    (firstWinsFrom key value entries initial).find? query =
      prefer (initial.find? query) (firstValue key value entries query) := by
  induction entries generalizing initial with
  | nil =>
    change initial.find? query = prefer (initial.find? query) none
    cases initial.find? query <;> rfl
  | cons head tail ih =>
    cases known : initial.find? (key head) with
    | none =>
      simp only [firstWinsFrom, List.foldl_cons, RBMap.contains, known, Option.isSome,
        Bool.false_eq_true, if_false]
      change (firstWinsFrom key value tail (initial.insert (key head) (value head))).find? query =
        prefer (initial.find? query) (firstValue key value (head :: tail) query)
      rw [ih (initial.insert (key head) (value head)) (.insert history (key head) (value head)),
        find?_insert history]
      by_cases atHead : query = key head <;> simp only [atHead, firstValue, if_pos, if_neg, if_true, if_false, prefer]
      · simp only [known, prefer]
    | some previous =>
      simp only [firstWinsFrom, List.foldl_cons, RBMap.contains, known, Option.isSome, if_true]
      change (firstWinsFrom key value tail initial).find? query =
        prefer (initial.find? query) (firstValue key value (head :: tail) query)
      rw [ih initial history]
      by_cases atHead : query = key head <;> simp only [atHead, firstValue, if_pos, if_neg, if_true, if_false, prefer]
      · simp only [known, prefer]

theorem firstWins_empty_find (key : ρ → Nat) (value : ρ → α) (entries : List ρ) (query : Nat) :
    (firstWinsFrom key value entries (mkRBMap Nat α compare)).find? query =
      firstValue key value entries query := by
  rw [firstWinsFrom_find key value entries _ .empty query, find?_empty]
  rfl

end TrustIr.NatRBMapInsert
