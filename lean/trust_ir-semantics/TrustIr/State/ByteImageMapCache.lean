-- Copyright 2026 Andrew Yates | Apache-2.0
-- Representation-aware cache algorithm; native correspondence remains open.
import TrustIr.State.ByteImage

namespace TrustIr.ByteImage

/-- The actual constructor step with erased smaller-child witnesses. All six
    constructors, arbitrary callbacks, extents and left-before-right state flow
    are retained. The existing mapStep declaration is unchanged. -/
def Tree.mapStepBelow {σ : Type} (f : Option UInt8 → Option UInt8)
    {size : Nat} (tree : Tree size)
    (visit : {childSize : Nat} → (child : Tree childSize) →
      child.storageHeight < tree.storageHeight → StateM σ (Tree childSize)) :
    StateM σ (Tree size) := by
  cases tree with
  | fill count byte => exact fun state => (.fill size (f byte), state)
  | literal data =>
    let mapped : Tree data.size := by
      simpa only [Array.size_map] using Tree.literal (data.map f)
    exact fun state => (mapped, state)
  | append left right =>
    exact fun state =>
      let (left', state') := visit left (by
        simp only [Tree.storageHeight]
        exact Nat.lt_succ_of_le (Nat.le_max_left _ _)) state
      let (right', state'') := visit right (by
        simp only [Tree.storageHeight]
        exact Nat.lt_succ_of_le (Nat.le_max_right _ _)) state'
      (.append left' right', state'')
  | periodic unit positive phase count =>
    exact fun state =>
      let (unit', state') := visit unit (by
        simp only [Tree.storageHeight]
        exact Nat.lt_succ_self _) state
      (.periodic unit' positive phase size, state')
  | view original offset count inside =>
    exact fun state =>
      let (original', state') := visit original (by
        simp only [Tree.storageHeight]
        exact Nat.lt_succ_self _) state
      (.view original' offset size inside, state')
  | source count read => exact fun state => (.source size (fun index => f (read index)), state)

/-- Full state-transformer equality, with no restriction on the supplied child
    callback or starting state. No native/runtime correspondence is asserted. -/
theorem Tree.mapStepBelow_eq_mapStep {σ : Type} (f : Option UInt8 → Option UInt8)
    (visit : {childSize : Nat} → Tree childSize → StateM σ (Tree childSize))
    {size : Nat} (tree : Tree size) :
    tree.mapStepBelow f (fun child _ => visit child) = tree.mapStep f visit := by
  cases tree <;> rfl

/-- A retained representation identity paired with its complete source value.
    Distinct identities may denote propositionally equal source trees. -/
structure MapNodeRef where
  size : Nat
  tree : Tree size
  address : USize

def MapNodeRef.key (node : MapNodeRef) : MapCacheKey := (node.size, node.address)
def MapNodeRef.image (node : MapNodeRef) : ByteImage := ⟨node.size, node.tree⟩

/-- One inspection of a particular retained parent reference. Child references
    retain actual child identities; they are never inferred from tree equality. -/
inductive MapNodeView : {size : Nat} → Tree size → Type where
  | fill (count : Nat) (byte : Option UInt8) : MapNodeView (.fill count byte)
  | literal (data : Array (Option UInt8)) : MapNodeView (.literal data)
  | append (left right : MapNodeRef) : MapNodeView (.append left.tree right.tree)
  | periodic (unit : MapNodeRef) (positive : 0 < unit.size) (phase count : Nat) :
      MapNodeView (.periodic unit.tree positive phase count)
  | view (source : MapNodeRef) (offset count : Nat) (inside : offset + count ≤ source.size) :
      MapNodeView (.view source.tree offset count inside)
  | source (count : Nat) (read : Nat → Option UInt8) : MapNodeView (.source count read)

/-- Actual constructor/state transition over representation references. The
    callback receives each exact child reference, in original evaluation order. -/
def MapNodeView.mapStep {σ : Type} (f : Option UInt8 → Option UInt8)
    {size : Nat} {tree : Tree size} (view : MapNodeView tree)
    (visit : (child : MapNodeRef) → child.tree.storageHeight < tree.storageHeight →
      StateM σ (Tree child.size)) : StateM σ (Tree size) := by
  cases view with
  | fill count byte => exact fun state => (.fill size (f byte), state)
  | literal data =>
    let mapped : Tree data.size := by
      simpa only [Array.size_map] using Tree.literal (data.map f)
    exact fun state => (mapped, state)
  | append left right =>
    exact fun state =>
      let (left', state') := visit left (by
        simp only [Tree.storageHeight]
        exact Nat.lt_succ_of_le (Nat.le_max_left _ _)) state
      let (right', state'') := visit right (by
        simp only [Tree.storageHeight]
        exact Nat.lt_succ_of_le (Nat.le_max_right _ _)) state'
      (.append left' right', state'')
  | periodic unit positive phase count =>
    exact fun state =>
      let (unit', state') := visit unit (by
        simp only [Tree.storageHeight]
        exact Nat.lt_succ_self _) state
      (.periodic unit' positive phase size, state')
  | view source offset count inside =>
    exact fun state =>
      let (source', state') := visit source (by
        simp only [Tree.storageHeight]
        exact Nat.lt_succ_self _) state
      (.view source' offset size inside, state')
  | source count read => exact fun state => (.source size (fun index => f (read index)), state)

/-- Exact erasure law on every constructor, callback and state. This law does
    not equate references whose source trees happen to be equal. -/
theorem MapNodeView.mapStep_eq_mapStep {σ : Type} (f : Option UInt8 → Option UInt8)
    (visit : {childSize : Nat} → Tree childSize → StateM σ (Tree childSize))
    {size : Nat} {tree : Tree size} (view : MapNodeView tree) :
    view.mapStep f (fun child _ => visit child.tree) = tree.mapStep f visit := by
  cases view <;> rfl

/-- A representation-aware observer is indexed by the retained parent reference,
    not by its extensional Tree value. Key hits precede inspection and mapping. -/
def mapRefKeyed (observe : (node : MapNodeRef) → MapNodeView node.tree)
    (f : Option UInt8 → Option UInt8) (node : MapNodeRef) :
    StateM MapCache (Tree node.size) :=
  node.tree.mapCacheStep node.key
    (fun _ => (observe node).mapStep f (fun child smaller => mapRefKeyed observe f child))
termination_by node.tree.storageHeight
decreasing_by assumption

/-- A hit returns the exact retained mapped tree and unchanged cache. Neither
    the representation observer nor any source/map callback is invoked. -/
theorem mapRefKeyed_hit (observe : (node : MapNodeRef) → MapNodeView node.tree)
    (f : Option UInt8 → Option UInt8) (node : MapNodeRef) (cache : MapCache)
    (entry : MapCacheEntry) (found : trustIrHashMapFind? cache node.key = some entry)
    (same : entry.mapped.size = node.size) :
    mapRefKeyed observe f node cache = (same ▸ entry.mapped.tree, cache) := by
  rw [mapRefKeyed]
  exact Tree.mapCacheStep_hit node.key _ node.tree cache entry found same

/-- A true miss inspects this retained parent once, runs its actual child
    references in constructor order, then inserts the original and mapped
    payloads into the resulting child cache. This uses actual HashMap.insert. -/
theorem mapRefKeyed_miss (observe : (node : MapNodeRef) → MapNodeView node.tree)
    (f : Option UInt8 → Option UInt8) (node : MapNodeRef) (cache : MapCache)
    (missing : trustIrHashMapFind? cache node.key = none) :
    mapRefKeyed observe f node cache =
      let (mapped, after) :=
        ((observe node).mapStep f (fun child _ => mapRefKeyed observe f child)) cache
      (mapped, after.insert node.key
        { original := node.image, mapped := ⟨node.size, mapped⟩ }) := by
  rw [mapRefKeyed]
  exact Tree.mapCacheStep_miss node.key _ node.tree cache (by
    intro entry found
    rw [missing] at found
    cases found)

/-- Full constructor erasure at a miss for an arbitrary source callback. This
    is an equality of state transformers, not an assertion that IDs are equal. -/
theorem MapNodeView.mapStepBelow_erasure {σ : Type}
    (f : Option UInt8 → Option UInt8)
    (visit : {childSize : Nat} → Tree childSize → StateM σ (Tree childSize))
    {size : Nat} {tree : Tree size} (view : MapNodeView tree) :
    view.mapStep f (fun child _ => visit child.tree) =
      tree.mapStepBelow f (fun child _ => visit child) := by
  rw [MapNodeView.mapStep_eq_mapStep, Tree.mapStepBelow_eq_mapStep]

end TrustIr.ByteImage
