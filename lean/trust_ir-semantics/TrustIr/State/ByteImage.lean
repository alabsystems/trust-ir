-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import TrustIr.CompilerCompat

namespace TrustIr

namespace ByteImage

/-- Exact finite byte images. Extents are indices, not recursively recomputed
    lengths. Views retain their source; periodic regions retain one nonempty
    template and a phase. Absent bytes remain absent. -/
inductive Tree : Nat → Type where
  | fill (count : Nat) (byte : Option UInt8) : Tree count
  | literal (data : Array (Option UInt8)) : Tree data.size
  | append {leftSize rightSize : Nat} (left : Tree leftSize) (right : Tree rightSize) :
      Tree (leftSize + rightSize)
  | periodic {period : Nat} (unit : Tree period) (positive : 0 < period)
      (phase count : Nat) : Tree count
  | view {sourceSize : Nat} (source : Tree sourceSize) (offset count : Nat)
      (inside : offset + count ≤ sourceSize) : Tree count
  /-- An arbitrary external memory model supplies no repetition evidence. -/
  | source (count : Nat) (read : Nat → Option UInt8) : Tree count

def Tree.get {size : Nat} (tree : Tree size) (index : Nat) : Option UInt8 :=
  if index < size then
    match tree with
    | .fill _ byte => byte
    | .literal data => (data[index]?).getD none
    | .append (leftSize := leftSize) left right =>
      if index < leftSize then left.get index else right.get (index - leftSize)
    | .periodic (period := period) unit _ phase _ => unit.get ((phase + index) % period)
    | .view original offset _ _ => original.get (offset + index)
    | .source _ read => read index
  else none

def Tree.map {size : Nat} (f : Option UInt8 → Option UInt8) (tree : Tree size) : Tree size :=
  match tree with
  | .fill count byte => .fill count (f byte)
  | .literal data => by simpa only [Array.size_map] using (Tree.literal (data.map f))
  | .append left right => .append (left.map f) (right.map f)
  | .periodic unit positive phase count => .periodic (unit.map f) positive phase count
  | .view original offset count inside => .view (original.map f) offset count inside
  | .source count read => .source count (fun index => f (read index))

/-- Repeat a finite template, dropping an enclosing periodic layer only when
    its extent is a whole number of inner periods. A clipped, unaligned unit
    must keep its own restart boundary. No source function is inspected. -/
def Tree.repeatWindow {size : Nat} : (tree : Tree size) → (positive : 0 < size) →
    (phase count : Nat) → Tree count
  | .periodic (period := period) unit innerPositive innerPhase size, positive, phase, count =>
    if size % period = 0 then
      unit.repeatWindow innerPositive ((innerPhase + phase) % period) count
    else .periodic (.periodic unit innerPositive innerPhase size) positive phase count
  | tree, positive, phase, count => .periodic tree positive phase count

/-- Actual stored constructor depth, including retained views and templates;
    logical repetition counts do not contribute a path. -/
def Tree.storageHeight {size : Nat} : Tree size → Nat
  | .fill _ _ | .literal _ | .source _ _ => 1
  | .append left right => max left.storageHeight right.storageHeight + 1
  | .periodic unit _ _ _ => unit.storageHeight + 1
  | .view original _ _ _ => original.storageHeight + 1


/-- The actual constructor step used by the runtime map. Recursive traversal is
    supplied explicitly; this definition neither selects pointer keys nor trusts
    a cache. Its state effects are exactly those of the supplied child calls. -/
def Tree.mapStep {σ : Type} (f : Option UInt8 → Option UInt8)
    (visit : {size : Nat} → Tree size → StateM σ (Tree size))
    {size : Nat} : Tree size → StateM σ (Tree size)
  | .fill count byte => fun state => (.fill count (f byte), state)
  | .literal data =>
    let mapped : Tree data.size := by
      simpa only [Array.size_map] using Tree.literal (data.map f)
    fun state => (mapped, state)
  | .append left right => fun state =>
    let (left', state') := visit left state
    let (right', state'') := visit right state'
    (.append left' right', state'')
  | .periodic unit positive phase count => fun state =>
    let (unit', state') := visit unit state
    (.periodic unit' positive phase count, state')
  | .view original offset count inside => fun state =>
    let (original', state') := visit original state
    (.view original' offset count inside, state')
  | .source count read => fun state =>
    (.source count (fun index => f (read index)), state)

/-- A checked induction step for the runtime's uncached constructor traversal.
    Every recursive call must already refine the pure map and preserve `valid`
    on a strictly smaller stored tree. Pointer-key soundness, retention, and the
    establishment of that premise for the runtime cache remain separate duties. -/
theorem Tree.mapStep_refines {σ : Type} (valid : σ → Prop)
    (f : Option UInt8 → Option UInt8)
    (visit : {size : Nat} → Tree size → StateM σ (Tree size))
    {size : Nat} (tree : Tree size)
    (children : ∀ {childSize : Nat} (child : Tree childSize),
      child.storageHeight < tree.storageHeight → ∀ state, valid state →
        (visit child state).1 = child.map f ∧ valid (visit child state).2)
    (state : σ) (initial : valid state) :
    (tree.mapStep f visit state).1 = tree.map f ∧
      valid (tree.mapStep f visit state).2 := by
  cases tree with
  | fill count byte => exact ⟨rfl, initial⟩
  | literal data => exact ⟨rfl, initial⟩
  | source count read => exact ⟨rfl, initial⟩
  | append left right =>
    have leftSmaller : left.storageHeight < (Tree.append left right).storageHeight := by
      exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
    have rightSmaller : right.storageHeight < (Tree.append left right).storageHeight := by
      exact Nat.lt_succ_of_le (Nat.le_max_right _ _)
    have leftCorrect := children left leftSmaller state initial
    cases leftRun : visit left state with
    | mk left' state' =>
      simp only [leftRun] at leftCorrect
      have rightCorrect := children right rightSmaller state' leftCorrect.2
      cases rightRun : visit right state' with
      | mk right' state'' =>
        simp only [rightRun] at rightCorrect
        simp only [Tree.mapStep, leftRun, rightRun, Tree.map]
        exact ⟨by rw [leftCorrect.1, rightCorrect.1], rightCorrect.2⟩
  | periodic unit positive phase count =>
    have smaller : unit.storageHeight < unit.storageHeight + 1 :=
      Nat.lt_succ_self _
    have correct := children unit smaller state initial
    cases childRun : visit unit state with
    | mk unit' state' =>
      simp only [childRun] at correct
      simp only [Tree.mapStep, childRun, Tree.map]
      exact ⟨by rw [correct.1], correct.2⟩
  | view original offset count inside =>
    have smaller : original.storageHeight < original.storageHeight + 1 :=
      Nat.lt_succ_self _
    have correct := children original smaller state initial
    cases childRun : visit original state with
    | mk original' state' =>
      simp only [childRun] at correct
      simp only [Tree.mapStep, childRun, Tree.map]
      exact ⟨by rw [correct.1], correct.2⟩

/-- The recursive premise is inhabited constructively: a pure traversal uses the
    very same constructor step and returns exactly the specification and state.
    This supplies no claim about the unsafe runtime's pointer cache. -/
theorem Tree.mapStep_pure {σ : Type} (f : Option UInt8 → Option UInt8)
    {size : Nat} (tree : Tree size) (state : σ) :
    tree.mapStep f (fun {_} child state => (child.map f, state)) state =
      (tree.map f, state) := by
  cases tree <;> rfl


/-- Only the consecutive, aligned periodic spine can be removed. An arbitrary
    view, append or unaligned finite period ends this certificate. -/
def Tree.alignedPrefix {size : Nat} : Tree size → Nat
  | .periodic (period := period) unit _ _ size =>
    if size % period = 0 then unit.alignedPrefix + 1 else 0
  | _ => 0

/-- Compose adjacent finite views without reading their source. Periodic and
    append nodes remain opaque: cropping does not certify a new period. -/
def Tree.window {size : Nat} : (tree : Tree size) → (offset count : Nat) →
    (inside : offset + count ≤ size) → Tree count
  | .view original start _ bound, offset, count, inside =>
    original.window (start + offset) count (by omega)
  | tree, offset, count, inside => .view tree offset count inside

theorem Tree.get_window {size : Nat} (tree : Tree size) (offset count : Nat)
    (inside : offset + count ≤ size) (index : Nat) :
    (tree.window offset count inside).get index =
      if index < count then tree.get (offset + index) else none := by
  induction tree generalizing offset count with
  | view original start size bound ih =>
    simp only [Tree.window]
    rw [ih]
    by_cases hit : index < count
    · have sourceHit : offset + index < size := by omega
      simp only [if_pos hit, Tree.get, if_pos sourceHit, Nat.add_assoc]
    · simp only [if_neg hit]
  | fill size byte => rfl
  | literal data => rfl
  | append left right _ _ => rfl
  | periodic unit positive phase size _ => rfl
  | source size read => rfl

end ByteImage

/-- The authoritative byte image, with a constant-time logical extent. -/
structure ByteImage where
  size : Nat
  tree : ByteImage.Tree size

namespace ByteImage

def empty : ByteImage := ⟨0, .fill 0 none⟩
def fill (count : Nat) (byte : Option UInt8) : ByteImage := ⟨count, .fill count byte⟩
def ofArray (data : Array (Option UInt8)) : ByteImage := ⟨data.size, .literal data⟩
def ofList (data : List (Option UInt8)) : ByteImage := ofArray data.toArray
def source (count : Nat) (read : Nat → Option UInt8) : ByteImage := ⟨count, .source count read⟩

def get (image : ByteImage) (index : Nat) : Option UInt8 := image.tree.get index

def append (left right : ByteImage) : ByteImage :=
  if left.size = 0 then right
  else if right.size = 0 then left
  else ⟨left.size + right.size, .append left.tree right.tree⟩

/-- No loop over count, including empty templates and max-u64 counts. -/
def tile (unit : ByteImage) (count : Nat) : ByteImage :=
  if h : unit.size = 0 then empty
  else if count = 0 then empty
  else if count = 1 then unit
  else ⟨unit.size * count, unit.tree.repeatWindow (by omega) 0 (unit.size * count)⟩

/-- Cropping, with the same extent as List.drop followed by List.take.
    Creating a view neither reads nor allocates its logical bytes. -/
def slice (image : ByteImage) (offset count : Nat) : ByteImage :=
  if h : offset < image.size then
    let size := min count (image.size - offset)
    ⟨size, image.tree.window offset size (by have := Nat.min_le_right count (image.size - offset); omega)⟩
  else empty

@[nospecialize, trustIrExtern 2 "l_TrustIr_ByteImage_map(#1, #2)"]
def map (f : Option UInt8 → Option UInt8) (image : ByteImage) : ByteImage :=
  ⟨image.size, image.tree.map f⟩

/-- Actual cache payload: both images are retained by the same entry.
    This records references, not a proof about native pointer lifetime. -/
structure MapCacheEntry where
  original : ByteImage
  mapped : ByteImage

abbrev MapCacheKey := Nat × USize
abbrev MapCache := trustIrHashMap MapCacheKey MapCacheEntry

/-- The actual memoized visitor transition, apart from unsafe key creation.
    A hit must have the requested extent. A miss forces the supplied thunk once,
    then inserts both original and mapped images into its resulting cache.
    The Unit thunk prevents strict argument evaluation from mapping a literal on hits.
    No logical traversal or cache scan replaces the concrete HashMap operations. -/
@[inline] def Tree.mapCacheStep (identity : MapCacheKey) {size : Nat}
    (uncached : Unit → StateM MapCache (Tree size)) (tree : Tree size) :
    StateM MapCache (Tree size) := fun cache =>
  let miss := fun cache =>
    let (mapped, after) := uncached () cache
    (mapped, after.insert identity { original := ⟨size, tree⟩, mapped := ⟨size, mapped⟩ })
  match trustIrHashMapFind? cache identity with
  | some entry =>
    if same : entry.mapped.size = size then (same ▸ entry.mapped.tree, cache)
    else miss cache
  | none => miss cache

/-- Hit semantics include leaving the cache unchanged; no recursive callback runs. -/
theorem Tree.mapCacheStep_hit (identity : MapCacheKey) {size : Nat}
    (uncached : Unit → StateM MapCache (Tree size)) (tree : Tree size) (cache : MapCache)
    (entry : MapCacheEntry) (found : trustIrHashMapFind? cache identity = some entry)
    (same : entry.mapped.size = size) :
    tree.mapCacheStep identity uncached cache = (same ▸ entry.mapped.tree, cache) := by
  simp only [Tree.mapCacheStep, found, dif_pos same]

/-- Miss semantics specify the exact post-traversal cache and retained payload.
    HashMap preservation of a richer key/lifetime invariant is a separate premise. -/
theorem Tree.mapCacheStep_miss (identity : MapCacheKey) {size : Nat}
    (uncached : Unit → StateM MapCache (Tree size)) (tree : Tree size) (cache : MapCache)
    (missed : ∀ entry, trustIrHashMapFind? cache identity = some entry → entry.mapped.size ≠ size) :
    tree.mapCacheStep identity uncached cache =
      let (mapped, after) := uncached () cache
      (mapped, after.insert identity { original := ⟨size, tree⟩, mapped := ⟨size, mapped⟩ }) := by
  cases found : trustIrHashMapFind? cache identity with
  | none => simp only [Tree.mapCacheStep, found]
  | some entry => simp only [Tree.mapCacheStep, found, dif_neg (missed entry found)]

/-- Transport of a mapped image through the checked extent test is exact. -/
theorem tree_cast_of_image_eq (image : ByteImage) {size : Nat} (tree : Tree size)
    (same : image.size = size) (equal : image = ⟨size, tree⟩) :
    same ▸ image.tree = tree := by
  cases equal
  rfl

/-- Conditional cache-step refinement for the actual HashMap transition.
    Key/source identity, entry refinement, recursive miss correctness, and concrete
    HashMap insertion/lifetime-invariant preservation remain explicit duties.
    No unsafe pointer or recursive runtime callback is instantiated in this proof. -/
theorem Tree.mapCacheStep_refines (f : Option UInt8 → Option UInt8)
    (valid : MapCache → Prop) (identity : MapCacheKey) {size : Nat}
    (uncached : Unit → StateM MapCache (Tree size)) (tree : Tree size) (cache : MapCache)
    (initial : valid cache)
    (keySource : ∀ entry, trustIrHashMapFind? cache identity = some entry →
      entry.original = ⟨size, tree⟩)
    (entryRefines : ∀ entry, trustIrHashMapFind? cache identity = some entry →
      entry.mapped = ByteImage.map f entry.original)
    (missRefines : (∀ entry, trustIrHashMapFind? cache identity = some entry → entry.mapped.size ≠ size) →
      (uncached () cache).1 = tree.map f ∧ valid (uncached () cache).2)
    (insertPreserves : ∀ after mapped, valid after → mapped = tree.map f →
      valid (after.insert identity { original := ⟨size, tree⟩, mapped := ⟨size, mapped⟩ })) :
    (tree.mapCacheStep identity uncached cache).1 = tree.map f ∧
      valid (tree.mapCacheStep identity uncached cache).2 := by
  cases found : trustIrHashMapFind? cache identity with
  | some entry =>
    have mappedCorrect : entry.mapped = ⟨size, tree.map f⟩ := by
      rw [entryRefines entry found, keySource entry found]
      rfl
    have same : entry.mapped.size = size := congrArg ByteImage.size mappedCorrect
    rw [Tree.mapCacheStep_hit identity uncached tree cache entry found same]
    exact ⟨tree_cast_of_image_eq entry.mapped (tree.map f) same mappedCorrect, initial⟩
  | none =>
    have missed : ∀ entry, trustIrHashMapFind? cache identity = some entry → entry.mapped.size ≠ size := by
      intro entry impossible
      rw [found] at impossible
      cases impossible
    have correct := missRefines missed
    rw [Tree.mapCacheStep_miss identity uncached tree cache missed]
    cases run : uncached () cache with
    | mk mapped after =>
      simp only [run] at correct ⊢
      exact ⟨correct.1, insertPreserves after mapped correct.2 correct.1⟩

/-- Explicit finite materialization for scalar codecs and independent controls.
    Bulk memory operations must use the image itself. -/
def toList (image : ByteImage) : List (Option UInt8) :=
  (List.range image.size).map image.get

@[simp] theorem size_fill (count : Nat) (byte : Option UInt8) : (fill count byte).size = count := rfl
@[simp] theorem size_ofArray (data : Array (Option UInt8)) : (ofArray data).size = data.size := rfl
@[simp] theorem size_ofList (data : List (Option UInt8)) : (ofList data).size = data.length := by
  simp [ofList, ofArray]
@[simp] theorem size_append (left right : ByteImage) : (append left right).size = left.size + right.size := by
  by_cases leftEmpty : left.size = 0 <;> by_cases rightEmpty : right.size = 0 <;>
    simp [append, leftEmpty, rightEmpty]
@[simp] theorem size_tile (unit : ByteImage) (count : Nat) : (tile unit count).size = unit.size * count := by
  by_cases empty : unit.size = 0 <;> by_cases zero : count = 0 <;> by_cases one : count = 1 <;>
    simp [tile, empty, zero, one, ByteImage.empty]

@[simp] theorem get_fill (count index : Nat) (byte : Option UInt8) :
    (fill count byte).get index = if index < count then byte else none := rfl

theorem get_outside (image : ByteImage) (index : Nat) (outside : image.size ≤ index) :
    image.get index = none := by
  rcases image with ⟨size, tree⟩
  cases tree <;> simp_all [get, Tree.get] <;> intro impossible <;> omega

theorem get_ofArray (data : Array (Option UInt8)) (index : Nat) :
    (ofArray data).get index = (data[index]?).getD none := by
  by_cases inside : index < data.size
  · simp only [ofArray, get, Tree.get, if_pos inside]
  · simp only [ofArray, get, Tree.get, if_neg inside]
    simp [getElem?_def, inside]

theorem get_ofList (data : List (Option UInt8)) (index : Nat) :
    (ofList data).get index = (trustIrListGet? data index).getD none := by
  unfold ofList
  rw [get_ofArray, CompilerCompat.getElem?_toArray]

theorem size_slice (image : ByteImage) (offset count : Nat) :
    (slice image offset count).size = min count (image.size - offset) := by
  unfold slice
  split
  · rfl
  · simp_all [empty, Nat.sub_eq_zero_of_le]

theorem get_slice (image : ByteImage) (offset count index : Nat)
    (inCount : index < count) (inSource : offset + index < image.size) :
    (image.slice offset count).get index = image.get (offset + index) := by
  have starts : offset < image.size := by omega
  have inside : index < min count (image.size - offset) := by omega
  unfold get slice
  rw [dif_pos starts]
  rw [Tree.get_window, if_pos inside]

theorem get_append (left right : ByteImage) (index : Nat) :
    (append left right).get index =
      if index < left.size then left.get index else right.get (index - left.size) := by
  by_cases leftEmpty : left.size = 0
  · unfold append
    rw [if_pos leftEmpty]
    simp only [leftEmpty, Nat.not_lt_zero, if_false, Nat.sub_zero]
  by_cases rightEmpty : right.size = 0
  · simp only [append, if_neg leftEmpty, if_pos rightEmpty]
    by_cases inside : index < left.size
    · simp [inside]
    · rw [if_neg inside, get_outside left index (by omega),
        get_outside right (index - left.size) (by omega)]
  by_cases inside : index < left.size + right.size
  · unfold append
    rw [if_neg leftEmpty, if_neg rightEmpty]
    simp only [get, Tree.get, if_pos inside]
  · have beyondLeft : ¬ index < left.size := by omega
    have beyondRight : right.size ≤ index - left.size := by omega
    rw [if_neg beyondLeft, get_outside right (index - left.size) beyondRight]
    apply get_outside
    rw [size_append]
    omega

end ByteImage

/-- Byte storage is the source of truth, not a sidecar to an unrelated lookup
    function. Writes retain complete immutable images, so copies are snapshots. -/
inductive ByteStore where
  | empty
  | source (read : Nat → Option UInt8)
  | write (previous : ByteStore) (address : Nat) (image : ByteImage)

namespace ByteStore

def get (store : ByteStore) (address : Nat) : Option UInt8 :=
  match store with
  | .empty => none
  | .source read => read address
  | .write previous start image =>
    if start ≤ address ∧ address - start < image.size then image.get (address - start)
    else previous.get address

/-- Read the real retained write structure. Only arbitrary external memories
    produce source-function leaves; runtime fills/copies remain structural. -/
def snapshot (store : ByteStore) (address count : Nat) : ByteImage :=
  if count = 0 then ByteImage.empty
  else match store with
  | .empty => ByteImage.fill count none
  | .source read => ByteImage.source count (fun index => read (address + index))
  | .write previous start image =>
    if image.size = 0 ∨ address + count ≤ start ∨ start + image.size ≤ address then
      previous.snapshot address count
    else
      let stop := address + count
      let overlapStart := max address start
      let overlapStop := min stop (start + image.size)
      let beforeImage := previous.snapshot address (overlapStart - address)
      let middle := image.slice (overlapStart - start) (overlapStop - overlapStart)
      let suffix := previous.snapshot overlapStop (stop - overlapStop)
      ByteImage.append beforeImage (ByteImage.append middle suffix)

theorem size_snapshot (store : ByteStore) (address count : Nat) :
    (store.snapshot address count).size = count := by
  induction store generalizing address count with
  | empty => by_cases zero : count = 0 <;> simp [snapshot, zero, ByteImage.empty]
  | source read => by_cases zero : count = 0 <;> simp [snapshot, zero, ByteImage.empty, ByteImage.source]
  | write previous start image ih =>
    by_cases zero : count = 0
    · simp [snapshot, zero, ByteImage.empty]
    by_cases disjoint : image.size = 0 ∨ address + count ≤ start ∨ start + image.size ≤ address
    · simp [snapshot, zero, disjoint, ih]
    · simp [snapshot, zero, disjoint, ih, ByteImage.size_slice]
      omega

@[simp] theorem get_empty (address : Nat) : ByteStore.empty.get address = none := rfl
@[simp] theorem get_source (read : Nat → Option UInt8) (address : Nat) :
    (ByteStore.source read).get address = read address := rfl

theorem get_write_inside (previous : ByteStore) (start address : Nat) (image : ByteImage)
    (after : start ≤ address) (inside : address - start < image.size) :
    (ByteStore.write previous start image).get address = image.get (address - start) := by
  simp [get, after, inside]

theorem get_write_outside (previous : ByteStore) (start address : Nat) (image : ByteImage)
    (outside : address < start ∨ start + image.size ≤ address) :
    (ByteStore.write previous start image).get address = previous.get address := by
  simp only [get]
  split
  · rename_i h
    rcases outside with before | after <;> omega
  · rfl

/-- A structural snapshot observes every actual byte of its source, including
    holes. No uniformity guess or separate image-history invariant is needed. -/
theorem get_snapshot (store : ByteStore) (address count index : Nat)
    (inside : index < count) :
    (store.snapshot address count).get index = store.get (address + index) := by
  induction store generalizing address count index with
  | empty =>
    have zero : count ≠ 0 := by omega
    simp only [snapshot, if_neg zero, ByteImage.get_fill, if_pos inside, get]
  | source read =>
    have zero : count ≠ 0 := by omega
    unfold snapshot
    rw [if_neg zero]
    simp only [ByteImage.source, ByteImage.get, ByteImage.Tree.get, if_pos inside, get]
  | write previous start image ih =>
    have zero : count ≠ 0 := by omega
    by_cases disjoint : image.size = 0 ∨ address + count ≤ start ∨ start + image.size ≤ address
    · simp only [snapshot, if_neg zero, if_pos disjoint]
      rw [ih address count index inside]
      apply Eq.symm
      apply get_write_outside
      rcases disjoint with empty | before | after <;> omega
    · let first := max address start
      let last := min (address + count) (start + image.size)
      have bounds : address ≤ first ∧ start ≤ first ∧ first < last ∧
          last ≤ address + count ∧ last ≤ start + image.size := by
        dsimp [first, last]
        omega
      have middleSize : (image.slice (first - start) (last - first)).size = last - first := by
        rw [ByteImage.size_slice]
        omega
      simp only [snapshot, if_neg zero, if_neg disjoint]
      change (ByteImage.append (previous.snapshot address (first - address))
        (ByteImage.append (image.slice (first - start) (last - first))
          (previous.snapshot last (address + count - last)))).get index = _
      rw [ByteImage.get_append, size_snapshot]
      by_cases before : index < first - address
      · rw [if_pos before, ih address (first - address) index before]
        apply Eq.symm
        apply get_write_outside
        left
        dsimp [first] at before
        omega
      · rw [if_neg before, ByteImage.get_append, middleSize]
        by_cases within : index - (first - address) < last - first
        · rw [if_pos within, ByteImage.get_slice image (first - start) (last - first)
            (index - (first - address)) within (by omega)]
          rw [get_write_inside previous start (address + index) image (by omega) (by omega)]
          congr 1
          omega
        · rw [if_neg within, ih last (address + count - last)
            (index - (first - address) - (last - first)) (by omega)]
          rw [get_write_outside previous start (address + index) image (by
            right
            dsimp [last] at *
            omega)]
          congr 1
          omega

end ByteStore
end TrustIr
