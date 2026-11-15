-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.NatIndexTree
namespace TrustIr

/-- Executable binary routing with singleton suffixes stored in one leaf.
    Keys remain arbitrary naturals. `toTree` supplies the exact original
    logical view, including every routing constructor; inference uses `find`
    and `insert` directly and never needs to materialize that view. -/
inductive NatIndexStorage (α : Type) where
  | empty
  | leaf (key : Nat) (entry : α)
  | node (value : Option α) (even odd : NatIndexStorage α)

namespace NatIndexStorage
variable {α : Type}

def value : NatIndexStorage α → Option α
  | .empty => none
  | .leaf key entry => if key = 0 then some entry else none
  | .node value _ _ => value

def even : NatIndexStorage α → NatIndexStorage α
  | .empty => .empty
  | .leaf key entry => if key = 0 then .empty else if key % 2 = 0 then .leaf (key / 2) entry else .empty
  | .node _ even _ => even

def odd : NatIndexStorage α → NatIndexStorage α
  | .empty => .empty
  | .leaf key entry => if key = 0 then .empty else if key % 2 = 0 then .empty else .leaf (key / 2) entry
  | .node _ _ odd => odd

def find : NatIndexStorage α → Nat → Option α
  | .empty, _ => none
  | .leaf key entry, query => if query = key then some entry else none
  | .node value even odd, key =>
    if key = 0 then value else if key % 2 = 0 then find even (key / 2) else find odd (key / 2)

def toTree : NatIndexStorage α → NatIndexTree α
  | .empty => .empty
  | .leaf key entry => NatIndexTree.empty.insert key entry
  | .node value even odd => .node value even.toTree odd.toTree

/-- Every old tree, including noncanonical empty routing nodes, has an exact
    representation. Compression imposes no canonical-shape requirement. -/
def ofTree : NatIndexTree α → NatIndexStorage α
  | .empty => .empty
  | .node value even odd => .node value (ofTree even) (ofTree odd)

theorem toTree_ofTree (tree : NatIndexTree α) : (ofTree tree).toTree = tree := by
  induction tree with
  | empty => rfl
  | node value even odd evenIH oddIH => simp only [ofTree, toTree, evenIH, oddIH]

private theorem toTree_node (stored : Option α) (even odd : NatIndexStorage α) :
    (NatIndexStorage.node stored even odd).toTree = NatIndexTree.node stored even.toTree odd.toTree := rfl

theorem toTree_value (tree : NatIndexStorage α) : tree.toTree.value = tree.value := by
  cases tree with
  | empty => rfl
  | node _ _ _ => rfl
  | leaf key entry =>
    rw [toTree, NatIndexTree.insert_unfold]
    by_cases zero : key = 0 <;> by_cases parity : key % 2 = 0 <;>
      simp [zero, parity, value, NatIndexTree.value]

theorem toTree_even (tree : NatIndexStorage α) : tree.toTree.even = tree.even.toTree := by
  cases tree with
  | empty => rfl
  | node _ _ _ => rfl
  | leaf key entry =>
    rw [toTree, NatIndexTree.insert_unfold]
    by_cases zero : key = 0 <;> by_cases parity : key % 2 = 0 <;>
      simp [zero, parity, even, toTree, NatIndexTree.even]

theorem toTree_odd (tree : NatIndexStorage α) : tree.toTree.odd = tree.odd.toTree := by
  cases tree with
  | empty => rfl
  | node _ _ _ => rfl
  | leaf key entry =>
    rw [toTree, NatIndexTree.insert_unfold]
    by_cases zero : key = 0 <;> by_cases parity : key % 2 = 0 <;>
      simp [zero, parity, odd, toTree, NatIndexTree.odd]

theorem toTree_find (tree : NatIndexStorage α) (key : Nat) : tree.toTree.find key = tree.find key := by
  induction tree generalizing key with
  | empty => rfl
  | leaf stored entry => simp [toTree, find, NatIndexTree.find_insert, NatIndexTree.find]
  | node stored even odd evenIH oddIH =>
    simp only [toTree, NatIndexTree.find, find]
    split
    · rfl
    · split
      · exact evenIH _
      · exact oddIH _

private theorem empty_insert_overwrite (key : Nat) (old entry : α) :
    ((NatIndexTree.empty : NatIndexTree α).insert key old).insert key entry =
      NatIndexTree.empty.insert key entry := by
  induction key using trustIrNatStrongInduction with
  | ind key ih =>
    have before := NatIndexTree.insert_unfold (NatIndexTree.empty : NatIndexTree α) key old
    have after := NatIndexTree.insert_unfold (NatIndexTree.empty : NatIndexTree α) key entry
    by_cases zero : key = 0
    · simp only [zero, if_true, NatIndexTree.even, NatIndexTree.odd] at before after
      rw [zero, before, NatIndexTree.insert_unfold]
      simp only [zero, if_true, NatIndexTree.even, NatIndexTree.odd]
      exact after.symm
    · have smaller : key / 2 < key := Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)
      by_cases parity : key % 2 = 0 <;>
        simp only [zero, if_false, parity, if_true, NatIndexTree.value,
          NatIndexTree.even, NatIndexTree.odd] at before after
      all_goals
        rw [before, NatIndexTree.insert_unfold]
        simp only [zero, if_false, parity, if_true, NatIndexTree.value, NatIndexTree.even, NatIndexTree.odd]
        rw [ih (key / 2) smaller]
        exact after.symm

private def insertBelow : (bound key : Nat) → key < bound → NatIndexStorage α → α → NatIndexStorage α
  | 0, key, below, _, _ => False.elim (Nat.not_lt_zero key below)
  | _ + 1, key, _, .empty, entry => .leaf key entry
  | bound + 1, key, below, .leaf stored old, entry =>
    if stored = key then .leaf key entry
    else if zero : key = 0 then .node (some entry) (NatIndexStorage.leaf stored old).even (NatIndexStorage.leaf stored old).odd
    else if key % 2 = 0 then
      .node (NatIndexStorage.leaf stored old).value
        (insertBelow bound (key / 2)
          (Nat.lt_of_lt_of_le (Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)) (Nat.le_of_lt_succ below))
          (NatIndexStorage.leaf stored old).even entry) (NatIndexStorage.leaf stored old).odd
    else .node (NatIndexStorage.leaf stored old).value (NatIndexStorage.leaf stored old).even
      (insertBelow bound (key / 2)
        (Nat.lt_of_lt_of_le (Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)) (Nat.le_of_lt_succ below))
        (NatIndexStorage.leaf stored old).odd entry)
  | bound + 1, key, below, .node stored even odd, entry =>
    if zero : key = 0 then .node (some entry) even odd
    else if key % 2 = 0 then .node stored
      (insertBelow bound (key / 2)
        (Nat.lt_of_lt_of_le (Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)) (Nat.le_of_lt_succ below)) even entry) odd
    else .node stored even (insertBelow bound (key / 2)
      (Nat.lt_of_lt_of_le (Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)) (Nat.le_of_lt_succ below)) odd entry)

def insert : NatIndexStorage α → Nat → α → NatIndexStorage α
  | .empty, key, entry => .leaf key entry
  | .leaf stored old, key, entry => insertBelow (key + 1) key (Nat.lt_succ_self key) (.leaf stored old) entry
  | .node stored even odd, key, entry =>
    if key = 0 then .node (some entry) even odd
    else if key % 2 = 0 then .node stored (insert even (key / 2) entry) odd
    else .node stored even (insert odd (key / 2) entry)

private theorem insertBelow_view (bound key : Nat) (below : key < bound)
    (tree : NatIndexStorage α) (entry : α) :
    (insertBelow bound key below tree entry).toTree = tree.toTree.insert key entry := by
  induction key using trustIrNatStrongInduction generalizing bound tree with
  | ind key ih =>
    cases bound with
    | zero => exact False.elim (Nat.not_lt_zero key below)
    | succ bound =>
      cases tree with
      | empty => rfl
      | leaf stored old =>
        rw [insertBelow]
        by_cases same : stored = key
        · simp only [same, if_true, toTree]
          exact (empty_insert_overwrite key old entry).symm
        · simp only [same, if_false]
          have shape := NatIndexTree.insert_unfold (NatIndexStorage.leaf stored old).toTree key entry
          by_cases zero : key = 0
          · simp only [zero, dite_true]
            change NatIndexTree.node (some entry)
              (NatIndexStorage.leaf stored old).even.toTree
              (NatIndexStorage.leaf stored old).odd.toTree = _
            simp only [zero, if_true] at shape
            rw [shape, toTree_even, toTree_odd]
          · simp only [zero, dite_false]
            have smaller : key / 2 < key := Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)
            have childBelow : key / 2 < bound := Nat.lt_of_lt_of_le smaller (Nat.le_of_lt_succ below)
            by_cases parity : key % 2 = 0 <;> simp only [parity, if_true, if_false]
            all_goals
              rw [toTree_node, ih (key / 2) smaller bound childBelow]
              simp only [zero, if_false, parity, if_true] at shape
              rw [shape, toTree_value, toTree_even, toTree_odd]
      | node stored even odd =>
        rw [insertBelow]
        have shape := NatIndexTree.insert_unfold (NatIndexStorage.node stored even odd).toTree key entry
        by_cases zero : key = 0
        · simp only [zero, dite_true]
          rw [toTree_node]
          simp only [zero, if_true, toTree, NatIndexTree.even, NatIndexTree.odd] at shape
          exact shape.symm
        · simp only [zero, dite_false]
          have smaller : key / 2 < key := Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)
          have childBelow : key / 2 < bound := Nat.lt_of_lt_of_le smaller (Nat.le_of_lt_succ below)
          by_cases parity : key % 2 = 0 <;> simp only [parity, if_true, if_false]
          all_goals
            rw [toTree_node, ih (key / 2) smaller bound childBelow]
            simp only [zero, if_false, parity, if_true, toTree, NatIndexTree.value,
              NatIndexTree.even, NatIndexTree.odd] at shape
            exact shape.symm

theorem toTree_insert (tree : NatIndexStorage α) (key : Nat) (entry : α) :
    (tree.insert key entry).toTree = tree.toTree.insert key entry := by
  induction tree generalizing key with
  | empty => rfl
  | leaf stored old => exact insertBelow_view (key + 1) key (Nat.lt_succ_self key) (.leaf stored old) entry
  | node stored even odd evenIH oddIH =>
    rw [insert]
    have shape := NatIndexTree.insert_unfold (NatIndexStorage.node stored even odd).toTree key entry
    by_cases zero : key = 0
    · simp only [zero, if_true]
      rw [toTree_node]
      simp only [zero, if_true, toTree, NatIndexTree.even, NatIndexTree.odd] at shape
      exact shape.symm
    · by_cases parity : key % 2 = 0 <;> simp only [zero, if_false, parity, if_true]
      all_goals
        rw [toTree_node]
        first | rw [evenIH] | rw [oddIH]
        simp only [zero, if_false, parity, if_true, toTree, NatIndexTree.value,
          NatIndexTree.even, NatIndexTree.odd] at shape
        exact shape.symm

theorem find_insert (tree : NatIndexStorage α) (key query : Nat) (entry : α) :
    (tree.insert key entry).find query = if query = key then some entry else tree.find query := by
  rw [← toTree_find, toTree_insert, NatIndexTree.find_insert, toTree_find]

/-- Structural, proof-only binary depth, without a recursive function in its type. -/
inductive KeyDepthCertificate : Nat → Nat → Prop where
  | zero : KeyDepthCertificate 0 1
  | step (key depth : Nat) (positive : key ≠ 0)
      (child : KeyDepthCertificate (key / 2) depth) : KeyDepthCertificate key (1 + depth)

inductive DepthCertificate : NatIndexStorage α → Nat → Prop where
  | empty : DepthCertificate .empty 0
  | leaf (key depth : Nat) (entry : α) (certificate : KeyDepthCertificate key depth) :
      DepthCertificate (.leaf key entry) depth
  | node (stored : Option α) (even odd : NatIndexStorage α) (evenDepth oddDepth : Nat)
      (evenCertificate : DepthCertificate even evenDepth) (oddCertificate : DepthCertificate odd oddDepth) :
      DepthCertificate (.node stored even odd) (1 + max evenDepth oddDepth)

theorem keyDepth_certificate (key : Nat) : KeyDepthCertificate key (NatIndexTree.keyDepth key) := by
  trustIrCompilerProof {
    induction key using trustIrNatStrongInduction with
    | ind key ih =>
      rw [NatIndexTree.keyDepth]
      by_cases zero : key = 0
      · simp only [zero, dite_true]
        exact .zero
      · simp only [zero, dite_false]
        exact .step key _ zero (ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)))
  } {
    let step (key : Nat) (rec : (child : Nat) → child < key → Nat) : Nat :=
      if zero : key = 0 then 1 else 1 + rec (key / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide))
    have go_congr (key fuel₁ fuel₂ : Nat) (h₁ : key < fuel₁) (h₂ : key < fuel₂) :
        WellFounded.Nat.fix.go (fun x : Nat => x) step fuel₁ key h₁ =
          WellFounded.Nat.fix.go (fun x : Nat => x) step fuel₂ key h₂ := by
      induction fuel₁ generalizing key fuel₂ with
      | zero => exact (Nat.not_lt_zero key h₁).elim
      | succ fuel₁ ih =>
        cases fuel₂ with
        | zero => exact (Nat.not_lt_zero key h₂).elim
        | succ fuel₂ =>
          delta WellFounded.Nat.fix.go
          change (if zero : key = 0 then 1 else 1 + WellFounded.Nat.fix.go (fun x : Nat => x) step fuel₁ (key / 2) _) =
            (if zero : key = 0 then 1 else 1 + WellFounded.Nat.fix.go (fun x : Nat => x) step fuel₂ (key / 2) _)
          by_cases zero : key = 0
          · rw [dif_pos zero, dif_pos zero]
          · rw [dif_neg zero, dif_neg zero]
            exact congrArg (Nat.add 1) (ih (key / 2) fuel₂ _ _)

    have keyDepth_eq (key : Nat) :
        NatIndexTree.keyDepth key = if zero : key = 0 then 1 else 1 + NatIndexTree.keyDepth (key / 2) := by
      delta NatIndexTree.keyDepth
      change WellFounded.Nat.fix (fun x : Nat => x) step key = _
      delta WellFounded.Nat.fix
      refine (go_congr key _ (key + 1) _ (Nat.lt_add_one key)).trans ?_
      conv =>
        lhs
        delta WellFounded.Nat.fix.go
      change (if zero : key = 0 then 1 else 1 + WellFounded.Nat.fix.go (fun x : Nat => x) step key (key / 2) _) = _
      by_cases zero : key = 0
      · rw [dif_pos zero, dif_pos zero]
      · rw [dif_neg zero, dif_neg zero]
        exact congrArg (Nat.add 1) (go_congr (key / 2) key _ _ _)
    induction key using trustIrNatStrongInduction with
    | ind key ih =>
      rw [keyDepth_eq]
      by_cases zero : key = 0
      · simp only [zero, dite_true]
        exact .zero
      · simp only [zero, dite_false]
        exact .step key _ zero (ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)))
  }

theorem KeyDepthCertificate.eq_depth {key depth : Nat} (certificate : KeyDepthCertificate key depth) :
    NatIndexTree.keyDepth key = depth := by
  trustIrCompilerProof {
    induction certificate with
    | zero => first | rfl | simp [NatIndexTree.keyDepth]
    | step key depth positive child ih =>
      rw [NatIndexTree.keyDepth, dif_neg positive, ih]
  } {
    have unique {key left right : Nat} (a : KeyDepthCertificate key left)
        (b : KeyDepthCertificate key right) : left = right := by
      induction a generalizing right with
      | zero =>
        cases b with
        | zero => rfl
        | step key depth positive child => exact (positive rfl).elim
      | step key depth positive child ih =>
        cases b with
        | zero => exact (positive rfl).elim
        | step key other positive' child' => exact congrArg (Nat.add 1) (ih child')
    exact unique (keyDepth_certificate key) certificate
  }

theorem DepthCertificate.eq_view {tree : NatIndexStorage α} {depth : Nat}
    (certificate : DepthCertificate tree depth) : tree.toTree.depth = depth := by
  induction certificate with
  | empty => rfl
  | leaf key depth entry certificate =>
    simp only [toTree, NatIndexTree.depth_insert_eq, NatIndexTree.depth, Nat.zero_max]
    exact certificate.eq_depth
  | node stored even odd evenDepth oddDepth evenCertificate oddCertificate evenIH oddIH =>
    simp only [toTree, NatIndexTree.depth, evenIH, oddIH]

theorem depth_certificate (tree : NatIndexStorage α) : DepthCertificate tree tree.toTree.depth := by
  induction tree with
  | empty => exact .empty
  | leaf key entry =>
    simp only [toTree, NatIndexTree.depth_insert_eq, NatIndexTree.depth, Nat.zero_max]
    exact .leaf key _ entry (keyDepth_certificate key)
  | node stored even odd evenIH oddIH =>
    exact .node stored even odd _ _ evenIH oddIH

end NatIndexStorage
end TrustIr

#trustIrAxiomsExact TrustIr.NatIndexStorage.keyDepth_certificate == [propext]
#trustIrAxiomsExact TrustIr.NatIndexStorage.KeyDepthCertificate.eq_depth == [propext]
