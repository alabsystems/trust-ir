-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.NatIndex

namespace TrustIr.NatIndexTree
variable {α : Type}

/-- Actual routing constructors, independently of the number of occupied
    value slots. This is distinct from the semantic declaration work count. -/
def nodeCount : NatIndexTree α → Nat
  | .empty => 0
  | .node _ even odd => 1 + nodeCount even + nodeCount odd

/-- New suffix constructors are the only steps that carry the structural
    numeric witness. Existing routes recurse directly on the tree. -/
def newPathSteps : NatIndexTree α → Nat → Nat
  | .empty, key => keyDepth key
  | .node _ even odd, key =>
    if key = 0 then 0
    else if key % 2 = 0 then newPathSteps even (key / 2)
    else newPathSteps odd (key / 2)

theorem nodeCount_empty_insert (key : Nat) (entry : α) :
    nodeCount (NatIndexTree.empty.insert key entry) = keyDepth key := by
  induction key using trustIrNatStrongInduction with
  | ind key ih =>
    rw [insert_unfold, keyDepth]
    by_cases zero : key = 0
    · simp [zero, even, odd, nodeCount]
    · simp only [zero, dite_false, ite_false]
      have smaller : key / 2 < key := Nat.div_lt_self (Nat.pos_of_ne_zero zero) (by decide)
      split <;> simp only [value, even, odd, nodeCount] <;> rw [ih _ smaller] <;> omega

theorem nodeCount_insert (tree : NatIndexTree α) (key : Nat) (entry : α) :
    (tree.insert key entry).nodeCount = tree.nodeCount + tree.newPathSteps key := by
  induction tree generalizing key with
  | empty => simpa only [nodeCount, newPathSteps, Nat.zero_add] using nodeCount_empty_insert key entry
  | node stored even odd evenIH oddIH =>
    rw [insert_unfold]
    by_cases zero : key = 0
    · simp [zero, NatIndexTree.even, NatIndexTree.odd, nodeCount, newPathSteps]
    · by_cases parity : key % 2 = 0 <;>
        simp only [zero, if_false, parity, if_true, value, NatIndexTree.even,
          NatIndexTree.odd, nodeCount, newPathSteps]
      · rw [evenIH]; omega
      · rw [oddIH]; omega

theorem newPathSteps_le_keyDepth (tree : NatIndexTree α) (key : Nat) :
    tree.newPathSteps key ≤ keyDepth key := by
  induction tree generalizing key with
  | empty => exact Nat.le_refl _
  | node stored even odd evenIH oddIH =>
    rw [newPathSteps, keyDepth]
    by_cases zero : key = 0
    · simp [zero]
    · simp only [zero, dite_false, ite_false]
      split
      · have bound := evenIH (key / 2); omega
      · have bound := oddIH (key / 2); omega

end TrustIr.NatIndexTree

namespace TrustIr.NatIndexStorage
variable {α : Type}

/-- Physical routing/leaf objects. This counts the executable compressed
    representation, separately from the unchanged binary-view work metric. -/
def nodeCount : NatIndexStorage α → Nat
  | .empty => 0
  | .leaf _ _ => 1
  | .node _ even odd => 1 + nodeCount even + nodeCount odd

def depth : NatIndexStorage α → Nat
  | .empty => 0
  | .leaf _ _ => 1
  | .node _ even odd => 1 + max even.depth odd.depth

/-- Each leaf compares the complete remaining natural key once. No claim is
    made that an arbitrary-precision equality is a constant-time bit operation. -/
def lookupSteps : NatIndexStorage α → Nat → Nat
  | .empty, _ => 0
  | .leaf _ _, _ => 1
  | .node _ even odd, key =>
    1 + if key = 0 then 0
      else if key % 2 = 0 then lookupSteps even (key / 2)
      else lookupSteps odd (key / 2)

theorem lookupSteps_le_depth (tree : NatIndexStorage α) (key : Nat) :
    tree.lookupSteps key ≤ tree.depth := by
  induction tree generalizing key with
  | empty => exact Nat.le_refl _
  | leaf _ _ => exact Nat.le_refl _
  | node value even odd evenIH oddIH =>
    simp only [lookupSteps, depth]
    split
    · omega
    · split
      · have bound := evenIH (key / 2); omega
      · have bound := oddIH (key / 2); omega

private theorem keyDepth_positive (key : Nat) : 0 < NatIndexTree.keyDepth key := by
  rw [NatIndexTree.keyDepth]
  split <;> omega

theorem nodeCount_le_view (tree : NatIndexStorage α) :
    tree.nodeCount ≤ tree.toTree.nodeCount := by
  induction tree with
  | empty => exact Nat.le_refl _
  | leaf key entry =>
    simp only [nodeCount, toTree, NatIndexTree.nodeCount_empty_insert]
    exact keyDepth_positive key
  | node value even odd evenIH oddIH =>
    simp only [nodeCount, toTree, NatIndexTree.nodeCount]
    omega

theorem depth_le_view (tree : NatIndexStorage α) : tree.depth ≤ tree.toTree.depth := by
  induction tree with
  | empty => exact Nat.le_refl _
  | leaf key entry =>
    simp only [depth, toTree, NatIndexTree.depth_insert_eq, NatIndexTree.depth,
      Nat.zero_max]
    exact keyDepth_positive key
  | node value even odd evenIH oddIH =>
    simp only [depth, toTree, NatIndexTree.depth]
    omega

theorem ofTree_find (tree : NatIndexTree α) (key : Nat) :
    (NatIndexStorage.ofTree tree).find key = tree.find key := by
  rw [← toTree_find, toTree_ofTree]

end TrustIr.NatIndexStorage

namespace TrustIr.NatIndex
variable {α : Type}

theorem find?_ofTree (source : NatIndexTree α) (keyBound : Nat)
    (outside : ∀ key, keyBound ≤ key → source.find key = none) (query : Nat) :
    (ofTree source keyBound outside).find? query = source.find query :=
  NatIndexStorage.ofTree_find source query

theorem depth_ofTree (source : NatIndexTree α) (keyBound : Nat)
    (outside : ∀ key, keyBound ≤ key → source.find key = none) :
    (ofTree source keyBound outside).depth = source.depth := rfl

theorem keyBound_ofTree (source : NatIndexTree α) (keyBound : Nat)
    (outside : ∀ key, keyBound ≤ key → source.find key = none) :
    (ofTree source keyBound outside).keyBound = keyBound := rfl

theorem inserted_tree (index : NatIndex α) (key : Nat) (entry : α) :
    (index.insert key entry).tree = index.tree.insert key entry :=
  NatIndexStorage.toTree_insert _ _ _

theorem inserted_keyBound (index : NatIndex α) (key : Nat) (entry : α) :
    (index.insert key entry).keyBound = max index.keyBound (key + 1) := rfl

theorem inserted_depth (index : NatIndex α) (key : Nat) (entry : α) :
    (index.insert key entry).depth = max index.depth (NatIndexTree.keyDepth key) := by
  change max index.depthValue (NatIndexTree.keyDepthFast key) = _
  rw [NatIndexTree.keyDepthFast_eq]
  rfl

end TrustIr.NatIndex
