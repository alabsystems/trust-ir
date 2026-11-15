-- Copyright 2026 Andrew Yates | Apache-2.0
-- Concrete actual-cache refinement; physical identity/inspection remains explicit.
import TrustIr.Proofs.ByteImageMapCacheLaws
import TrustIr.Proofs.ByteImageMapCacheInvariant
namespace TrustIr.ByteImage.ImageMapRefinement

def StateInvariant (observe : (node : MapNodeRef) → MapNodeView node.tree)
    (root : MapNodeRef) (f : Option UInt8 → Option UInt8) (cache : MapCache) : Prop :=
  MapCacheLaws.Reachable cache ∧ CacheInvariant observe root f cache

theorem stateInvariant_empty (observe : (node : MapNodeRef) → MapNodeView node.tree)
    (root : MapNodeRef) (f : Option UInt8 → Option UInt8) :
    StateInvariant observe root f (∅ : MapCache) := by
  refine ⟨MapCacheLaws.reachable_empty, ?_⟩
  intro key entry found
  rw [MapCacheLaws.find_empty] at found
  cases found

/-- Actual insertion preserves the concrete retained-ref/source/mapped invariant.
    Its lookup equation is proved from each compiler's actual HashMap library. -/
theorem stateInvariant_insert (observe : (node : MapNodeRef) → MapNodeView node.tree)
    (root : MapNodeRef) (f : Option UInt8 → Option UInt8)
    (node : MapNodeRef) (retained : RetainedReachable observe root node)
    (cache : MapCache) (valid : StateInvariant observe root f cache)
    (mapped : Tree node.size) (correct : mapped = node.tree.map f) :
    StateInvariant observe root f
      (cache.insert node.key { original := node.image, mapped := ⟨node.size, mapped⟩ }) := by
  refine ⟨.insert node.key _ valid.1, ?_⟩
  intro query entry found
  rw [MapCacheLaws.find_insert cache valid.1] at found
  cases comparison : node.key == query with
  | false =>
    simp only [comparison] at found
    exact valid.2 query entry found
  | true =>
    simp only [comparison] at found
    have same := Option.some.inj found
    cases same
    refine ⟨node, retained, (eq_of_beq comparison).symm, rfl, ?_⟩
    rw [correct]
    rfl

/-- Complete six-constructor state proof; callbacks receive actual child refs.
    The final recursive theorem discharges children by its smaller-height IH. -/
theorem viewStep_refines (observe : (node : MapNodeRef) → MapNodeView node.tree)
    (root : MapNodeRef) (f : Option UInt8 → Option UInt8)
    {size : Nat} {tree : Tree size} (view : MapNodeView tree)
    (visit : (child : MapNodeRef) → child.tree.storageHeight < tree.storageHeight →
      StateM MapCache (Tree child.size))
    (children : ∀ child smaller, ViewedChild view child → ∀ cache,
      StateInvariant observe root f cache →
      (visit child smaller cache).1 = child.tree.map f ∧
      StateInvariant observe root f (visit child smaller cache).2)
    (cache : MapCache) (valid : StateInvariant observe root f cache) :
    (view.mapStep f visit cache).1 = tree.map f ∧
      StateInvariant observe root f (view.mapStep f visit cache).2 := by
  cases view with
  | fill count byte => exact ⟨rfl, valid⟩
  | literal data => exact ⟨rfl, valid⟩
  | source count read => exact ⟨rfl, valid⟩
  | append left right =>
    have leftHeight : left.tree.storageHeight < (Tree.append left.tree right.tree).storageHeight := by
      exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
    have rightHeight : right.tree.storageHeight < (Tree.append left.tree right.tree).storageHeight := by
      exact Nat.lt_succ_of_le (Nat.le_max_right _ _)
    have leftCorrect := children left leftHeight (.left left right) cache valid
    have rightCorrect := children right rightHeight (.right left right)
      (visit left leftHeight cache).2 leftCorrect.2
    refine ⟨?_, rightCorrect.2⟩
    change Tree.append (visit left leftHeight cache).1
      (visit right rightHeight (visit left leftHeight cache).2).1 = _
    rw [leftCorrect.1, rightCorrect.1]
    rfl
  | periodic unit positive phase count =>
    have height : unit.tree.storageHeight < (Tree.periodic unit.tree positive phase size).storageHeight :=
      Nat.lt_succ_self _
    have correct := children unit height (.unit unit positive phase size) cache valid
    refine ⟨?_, correct.2⟩
    change Tree.periodic (visit unit height cache).1 positive phase size = _
    rw [correct.1]
    rfl
  | view source offset count inside =>
    have height : source.tree.storageHeight < (Tree.view source.tree offset size inside).storageHeight :=
      Nat.lt_succ_self _
    have correct := children source height (.source source offset size inside) cache valid
    refine ⟨?_, correct.2⟩
    change Tree.view (visit source height cache).1 offset size inside = _
    rw [correct.1]
    rfl

/-- Actual reference-keyed core, arbitrary root/callback, retained ref and every
    concrete reachable cache satisfying the derived entry invariant. No lookup,
    insertion, miss or callback law is assumed; only physical key-source soundness. -/
theorem mapRefKeyed_refines (observe : (node : MapNodeRef) → MapNodeView node.tree)
    (root : MapNodeRef) (physical : PhysicalKeySound observe root)
    (f : Option UInt8 → Option UInt8) (node : MapNodeRef)
    (retained : RetainedReachable observe root node)
    (cache : MapCache) (valid : StateInvariant observe root f cache) :
    (mapRefKeyed observe f node cache).1 = node.tree.map f ∧
      StateInvariant observe root f (mapRefKeyed observe f node cache).2 := by
  cases found : trustIrHashMapFind? cache node.key with
  | some entry =>
    rcases valid.2 node.key entry found with ⟨original, originalHeld, keySame, originalEq, mappedEq⟩
    have sourceSame : original.image = node.image :=
      physical original node originalHeld retained keySame.symm
    have mappedCorrect : entry.mapped = ⟨node.size, node.tree.map f⟩ := by
      rw [mappedEq, sourceSame]
      rfl
    have same : entry.mapped.size = node.size := congrArg ByteImage.size mappedCorrect
    rw [mapRefKeyed_hit observe f node cache entry found same]
    exact ⟨tree_cast_of_image_eq entry.mapped (node.tree.map f) same mappedCorrect, valid⟩
  | none =>
    have step := viewStep_refines observe root f (observe node)
      (fun child _ => mapRefKeyed observe f child)
      (fun child smaller edge after afterValid =>
        mapRefKeyed_refines observe root physical f child
          (.child retained edge) after afterValid) cache valid
    rw [mapRefKeyed_miss observe f node cache found]
    cases result : ((observe node).mapStep f (fun child _ => mapRefKeyed observe f child)) cache with
    | mk mapped after =>
      simp only [result] at step ⊢
      exact ⟨step.1, stateInvariant_insert observe root f node retained after step.2 mapped step.1⟩
termination_by node.tree.storageHeight
decreasing_by assumption

/-- Full result from actual empty cache; no client cache-invariant premise. -/
theorem mapRefKeyed_empty_refines (observe : (node : MapNodeRef) → MapNodeView node.tree)
    (root : MapNodeRef) (physical : PhysicalKeySound observe root)
    (f : Option UInt8 → Option UInt8) :
    (mapRefKeyed observe f root (∅ : MapCache)).1 = root.tree.map f := by
  exact (mapRefKeyed_refines observe root physical f root .root ∅
    (stateInvariant_empty observe root f)).1
/-- Complete original ByteImage value, including its exact stored extent. This
    remains logical refinement; it does not instantiate the physical observer. -/
theorem mapRefKeyed_empty_image_refines (observe : (node : MapNodeRef) → MapNodeView node.tree)
    (root : MapNodeRef) (physical : PhysicalKeySound observe root)
    (f : Option UInt8 → Option UInt8) :
    (⟨root.size, (mapRefKeyed observe f root (∅ : MapCache)).1⟩ : ByteImage) =
      ByteImage.map f root.image := by
  rw [mapRefKeyed_empty_refines observe root physical f]
  rfl

end TrustIr.ByteImage.ImageMapRefinement
