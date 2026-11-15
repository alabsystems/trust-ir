-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.State.ByteImageMapCache
namespace TrustIr.ByteImage.ImageMapRefinement

inductive ViewedChild : {size : Nat} → {tree : Tree size} → MapNodeView tree → MapNodeRef → Prop where
  | left (left right : MapNodeRef) : ViewedChild (.append left right) left
  | right (left right : MapNodeRef) : ViewedChild (.append left right) right
  | unit (unit : MapNodeRef) (positive : 0 < unit.size) (phase count : Nat) :
      ViewedChild (.periodic unit positive phase count) unit
  | source (source : MapNodeRef) (offset count : Nat) (inside : offset + count ≤ source.size) :
      ViewedChild (.view source offset count inside) source

inductive RetainedReachable (observe : (node : MapNodeRef) → MapNodeView node.tree)
    (root : MapNodeRef) : MapNodeRef → Prop where
  | root : RetainedReachable observe root root
  | child {parent child : MapNodeRef} : RetainedReachable observe root parent →
      ViewedChild (observe parent) child → RetainedReachable observe root child

-- Equal source values need NOT have equal identities. Only the physical
-- no-reused-live-identity direction is required, locally on the retained DAG.
def PhysicalKeySound (observe : (node : MapNodeRef) → MapNodeView node.tree)
    (root : MapNodeRef) : Prop :=
  ∀ left right, RetainedReachable observe root left → RetainedReachable observe root right →
    left.key = right.key → left.image = right.image

def CacheInvariant (observe : (node : MapNodeRef) → MapNodeView node.tree)
    (root : MapNodeRef) (f : Option UInt8 → Option UInt8) (cache : MapCache) : Prop :=
  ∀ key entry, trustIrHashMapFind? cache key = some entry →
    ∃ original : MapNodeRef, RetainedReachable observe root original ∧
      key = original.key ∧ entry.original = original.image ∧
      entry.mapped = ByteImage.map f original.image

-- A concrete witness that the representation does not canonicalize equal Trees.
def equalFillLeft : MapNodeRef := ⟨1, .fill 1 none, 1⟩
def equalFillRight : MapNodeRef := ⟨1, .fill 1 none, 2⟩
theorem equal_fill_sources : equalFillLeft.image = equalFillRight.image := rfl
theorem distinct_fill_keys_of_addresses (left right : USize) (different : left ≠ right) :
    (MapNodeRef.mk 1 (.fill 1 none) left).key ≠
      (MapNodeRef.mk 1 (.fill 1 none) right).key := by
  intro same
  exact different (congrArg Prod.snd same)

end TrustIr.ByteImage.ImageMapRefinement
