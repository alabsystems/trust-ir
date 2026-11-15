-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import SemRMemory
import SemRBoolMemory
import TrustIr.Proofs.AllocationLayout

/-! General allocation/provenance byte embedding from the plan-of-record SemR
heap into the existing canonical allocation-aware Memory. No replacement
allocator, byte store or evaluator is defined here. A source allocation's
identity is injected into a target allocation; its complete live byte image
and liveness/bounds/alignment are checked, including uninitialized bytes.

Fresh target-only allocations are compiler-private candidates, not machine
stack certificates. Confinement to their actual fresh footprint preserves
every embedded live source byte. Separation follows from allocation layout
and freshness, never from an arbitrary raw pointer/query being disjoint from
SP. Source pointer-to-integer observations, entry-heap/ABI custody, physical
SP placement, machine instruction effects, lifetime and calls need separate
refinement witnesses. Current compiler packets/grades are unchanged.

This package uses SemR's pinned Lean4.30 with the same canonical Memory source
whose own package pins4.8; Lake keeps those compiled caches separate. The TSL
model's interim status is unchanged. These are SemR input/representation
lemmas, not an extension of TSL into final compiler authority.
-/

namespace SemR.MemoryEmbedding

open TrustIr (Memory Allocation AllocId Addr PermissionMap Permission)

local macro "frame_arith" : tactic =>
  `(tactic| ((try simp only [Addr] at *) <;> (try dsimp only at *) <;> omega))

/-- An initialized source byte must be exactly the target byte, not its
modulo256 truncation. Poison/uninitialized storage stays uninitialized. -/
def ByteImage : AByte → Option UInt8 → Prop
  | .uninit, none => True
  | .init value, some byte => value = byte.toNat
  | _, _ => False

theorem ByteImage.initialized_bounded {value : Nat} {image : Option UInt8}
    (related : ByteImage (.init value) image) : value < 256 := by
  cases image with
  | none => cases related
  | some byte =>
    change value = byte.toNat at related
    rw [related]
    exact byte.toNat_lt

/-- Metadata/provenance image of one whole allocation. Target addresses may
differ: pointer injection below states that translation explicitly. This does
not prove exposed pointer-to-integer/address observations commute. -/
structure AllocationImage (source : Alloc) (target : Allocation) : Prop where
  size : target.size = source.size
  requested : target.requested = source.size
  live : target.alive = source.live
  alignment : source.align ≠ 0 ∧ target.base % source.align = 0
  finite : target.base + target.size ≤ addrSpace

/-- Complete source allocation population, injective provenance, and every
live source byte; target-only allocations are allowed. No source permission
is invented: SemR's current byte slice has no borrow-permission component. -/
structure Embeds (source : Mem) (target : Memory) (ids : Nat → AllocId) : Prop where
  layout : target.layoutWF
  fresh : BoolMemory.Fresh target
  records : ∀ index allocation, nth? source.allocs index = some allocation →
    ∃ record, target.lookup (ids index) = some record ∧ AllocationImage allocation record
  bytes : ∀ index allocation record,
    nth? source.allocs index = some allocation →
    target.lookup (ids index) = some record → allocation.live = true →
    ∀ offset, offset < allocation.size →
      ByteImage (byteAt allocation.data offset) (target.bytes (record.base + offset))
  injective : ∀ first allocation, nth? source.allocs first = some allocation →
    ∀ second other, nth? source.allocs second = some other → ids first = ids second →
      first = second

/-- The exact existing pointer values, including injected allocation
provenance and byte offset. No naked address licenses a dereference. -/
def PointerImage (source : Mem) (target : Memory) (ids : Nat → AllocId) :
    Val → TrustIr.Value → Prop
  | .ptr index offset, .ptr address (some id) =>
      ∃ allocation record, nth? source.allocs index = some allocation ∧
        target.lookup (ids index) = some record ∧ id = ids index ∧
        offset ≤ allocation.size ∧ address = record.base + offset ∧ address < addrSpace
  | .nullPtr, .nullPtr => True
  | _, _ => False

private theorem lookup_record {memory : Memory} {id : AllocId} {record : Allocation}
    (found : memory.lookup id = some record) :
    record ∈ memory.allocations ∧ record.id = id := by
  change memory.allocations.find? (fun allocation => allocation.id == id) = some record at found
  exact ⟨TrustIr.mem_of_find?_some found, by simpa using TrustIr.find?_some_pred found⟩

theorem Embeds.identity_below {source : Mem} {target : Memory} {ids : Nat → AllocId}
    (embedding : Embeds source target ids) (index : Nat) (allocation : Alloc)
    (present : nth? source.allocs index = some allocation) :
    (ids index).id < target.nextAllocId := by
  obtain ⟨record, found, _⟩ := embedding.records index allocation present
  obtain ⟨member, identity⟩ := lookup_record found
  simpa [identity] using embedding.layout.1 record member

theorem empty_embeds (ids : Nat → AllocId) : Embeds Mem.empty Memory.empty ids := by
  refine ⟨TrustIr.empty_layoutWF, BoolMemory.fresh_empty, ?_, ?_, ?_⟩
  · intro index allocation present
    cases index <;> cases present
  · intro index allocation record present
    cases index <;> cases present
  · intro index allocation present
    cases index <;> cases present

theorem write_preserves_fresh (target : Memory) (address : Addr) (data : List UInt8)
    (fresh : BoolMemory.Fresh target) (inside : address + data.length ≤ target.nextAddr) :
    BoolMemory.Fresh (target.writeBytes address data) := by
  intro query later
  rw [Memory.bytes_writeBytes_outside target address query data (Or.inr (Nat.le_trans inside later))]
  exact fresh query later

/-- A target write lies inside one actual allocation footprint. This is an
allocation-relative bound, not disjointness from any arbitrary raw query. -/
def WithinFrame (frame : Allocation) (address : Addr) (data : List UInt8) : Prop :=
  frame.base ≤ address ∧ address + data.length ≤ frame.base + frame.size

/-- All source allocation footprints end before this fresh allocation. -/
def Before (source : Mem) (target : Memory) (ids : Nat → AllocId) (base : Addr) : Prop :=
  ∀ index allocation record, nth? source.allocs index = some allocation →
    target.lookup (ids index) = some record → record.base + record.size ≤ base

theorem Embeds.write_private {source : Mem} {target : Memory} {ids : Nat → AllocId}
    (embedding : Embeds source target ids) (frame : Allocation)
    (separated : Before source target ids frame.base)
    (frameBound : frame.base + frame.size ≤ target.nextAddr)
    (address : Addr) (data : List UInt8) (inside : WithinFrame frame address data) :
    Embeds source (target.writeBytes address data) ids := by
  refine ⟨embedding.layout, write_preserves_fresh target address data embedding.fresh
    (Nat.le_trans inside.2 frameBound), embedding.records, ?_, embedding.injective⟩
  intro index allocation record present found live offset inBounds
  obtain ⟨original, originalFound, related⟩ := embedding.records index allocation present
  have same : original = record := by
    change target.lookup (ids index) = some record at found
    rw [originalFound] at found
    exact Option.some.inj found
  subst original
  have before := separated index allocation record present found
  have queryBefore : record.base + offset < address := by
    have size := related.size
    have start := inside.1
    frame_arith
  change ByteImage (byteAt allocation.data offset) ((target.writeBytes address data).bytes (record.base + offset))
  rw [Memory.bytes_writeBytes_outside target address (record.base + offset) data (Or.inl queryBefore)]
  exact embedding.bytes index allocation record present found live offset inBounds

private theorem allocated_old_lookup (target : Memory) (size align : Nat) (id : AllocId)
    (earlier : id.id < target.nextAllocId) :
    (target.alloc size align 0 .rustStack).snd.lookup id = target.lookup id := by
  have different : (AllocId.mk target.nextAllocId) ≠ id := by
    intro same
    have := congrArg AllocId.id same
    frame_arith
  simp [Memory.alloc, Memory.lookup, different]

private theorem allocated_bytes (target : Memory) (size align : Nat) :
    (target.alloc size align 0 .rustStack).snd.bytes = target.bytes := by
  rfl

private theorem allocated_fresh (target : Memory) (size align : Nat)
    (fresh : BoolMemory.Fresh target) :
    BoolMemory.Fresh (target.alloc size align 0 .rustStack).snd := by
  intro query later
  rw [allocated_bytes]
  apply fresh
  rw [TrustIr.alloc_advances_nextAddr] at later
  have start := TrustIr.le_alignUp target.nextAddr align
  simp only [Nat.add_zero] at later
  frame_arith

/-- Adding a fresh target-only frame leaves the complete source embedding
unchanged. The actual canonical allocator supplies identity and placement. -/
theorem Embeds.allocate_private {source : Mem} {target : Memory} {ids : Nat → AllocId}
    (embedding : Embeds source target ids) (size align : Nat) :
    Embeds source (target.alloc size align 0 .rustStack).snd ids := by
  refine ⟨TrustIr.alloc_preserves_layoutWF target size align 0 .rustStack embedding.layout,
    allocated_fresh target size align embedding.fresh, ?_, ?_, embedding.injective⟩
  · intro index allocation present
    obtain ⟨record, found, related⟩ := embedding.records index allocation present
    refine ⟨record, ?_, related⟩
    rw [allocated_old_lookup target size align (ids index)
      (embedding.identity_below index allocation present)]
    exact found
  · intro index allocation record present found live offset inBounds
    rw [allocated_old_lookup target size align (ids index)
      (embedding.identity_below index allocation present)] at found
    rw [allocated_bytes]
    exact embedding.bytes index allocation record present found live offset inBounds

theorem Embeds.fresh_frame_separation {source : Mem} {target : Memory} {ids : Nat → AllocId}
    (embedding : Embeds source target ids) (size align : Nat) :
    Before source (target.alloc size align 0 .rustStack).snd ids
      (target.allocRecord size align 0 .rustStack).base := by
  intro index allocation record present found
  rw [allocated_old_lookup target size align (ids index)
    (embedding.identity_below index allocation present)] at found
  obtain ⟨member, _⟩ := lookup_record found
  have below := embedding.layout.2.2.1 record member
  exact Nat.le_trans below.1 (TrustIr.le_alignUp target.nextAddr align)

/-- Actual canonical stores confined to this one frame. Metadata/counters
and permission maps are not rewritten by these byte stores. -/
inductive FrameWrites (frame : Allocation) : Memory → Memory → Prop where
  | done (memory : Memory) : FrameWrites frame memory memory
  | store {before current : Memory} (prior : FrameWrites frame before current)
      (address : Addr) (data : List UInt8) (inside : WithinFrame frame address data) :
      FrameWrites frame before (current.writeBytes address data)

theorem FrameWrites.lookup {frame : Allocation} {before after : Memory}
    (writes : FrameWrites frame before after) (id : AllocId) :
    after.lookup id = before.lookup id := by
  induction writes with
  | done => rfl
  | store _ _ _ _ induction => exact induction

theorem FrameWrites.pointer_image {frame : Allocation} {before after : Memory}
    (writes : FrameWrites frame before after) (source : Mem) (ids : Nat → AllocId)
    (index offset address : Nat) (id : AllocId)
    (image : PointerImage source before ids (.ptr index offset) (.ptr address (some id))) :
    PointerImage source after ids (.ptr index offset) (.ptr address (some id)) := by
  obtain ⟨allocation, record, present, found, identity, bound, addressEq, finite⟩ := image
  refine ⟨allocation, record, present, ?_, identity, bound, addressEq, finite⟩
  rw [writes.lookup]
  exact found

theorem Embeds.private_frame_writes {source : Mem} {target : Memory} {ids : Nat → AllocId}
    (embedding : Embeds source target ids) (size align : Nat) (after : Memory)
    (writes : FrameWrites (target.allocRecord size align 0 .rustStack)
      (target.alloc size align 0 .rustStack).snd after) :
    Embeds source after ids := by
  have startBound : (target.allocRecord size align 0 .rustStack).base +
      (target.allocRecord size align 0 .rustStack).size ≤
      (target.alloc size align 0 .rustStack).snd.nextAddr := by
    rw [TrustIr.alloc_advances_nextAddr]
    dsimp [Memory.allocRecord]
    exact Nat.add_le_add_left (Nat.le_max_left _ _) _
  have startEmbedding := embedding.allocate_private size align
  have startSeparated := embedding.fresh_frame_separation size align
  have result : Embeds source after ids ∧
      Before source after ids (target.allocRecord size align 0 .rustStack).base ∧
      after.nextAddr = (target.alloc size align 0 .rustStack).snd.nextAddr := by
    induction writes with
    | done => exact ⟨startEmbedding, startSeparated, rfl⟩
    | store prior address data inside induction =>
      obtain ⟨currentEmbedding, separated, nextAddress⟩ := induction
      refine ⟨currentEmbedding.write_private _ separated ?_ address data inside, separated, nextAddress⟩
      rw [nextAddress]
      exact startBound
  exact result.1

/-- A freshly allocated compiler-private candidate gets the existing owned
permission. This states the exact map update; it is not a borrow proof or an
assertion that existing canonical Load/Store wrappers enforce permissions. -/
theorem private_frame_owned (permissions : PermissionMap) (target : Memory) :
    (permissions.set ⟨target.nextAllocId⟩ .owned).get ⟨target.nextAllocId⟩ = some .owned := by
  simp [PermissionMap.get, PermissionMap.set]

theorem Embeds.private_frame_keeps_source_permissions
    {source : Mem} {target : Memory} {ids : Nat → AllocId}
    (embedding : Embeds source target ids) (permissions : PermissionMap)
    (index : Nat) (allocation : Alloc) (present : nth? source.allocs index = some allocation) :
    (permissions.set ⟨target.nextAllocId⟩ .owned).get (ids index) = permissions.get (ids index) := by
  have below := embedding.identity_below index allocation present
  have different : ids index ≠ ⟨target.nextAllocId⟩ := by
    intro same
    have := congrArg AllocId.id same
    frame_arith
  simp [PermissionMap.get, PermissionMap.set, different]

/-- Exactly the memory update in the successful existing SemR.allocAt and
Allocates.fresh branches, named here only so its representation can be stated.
It neither selects an alternative allocator nor bypasses those branches' checks. -/
def sourceAllocated (source : Mem) (size align : Nat) : Mem :=
  { allocs := source.allocs ++
      [{ base := SemR.alignUp source.nextAddr align, size := size, align := align,
         live := true, data := [] }]
    nextAddr := SemR.alignUp source.nextAddr align + max size 1 }

theorem allocAt_memory {pointerBits : Nat} {before after : Core} {node : Node}
    {size align : Nat} (executed : allocAt pointerBits before node size align = .ok after) :
    after.mem = sourceAllocated before.mem size align := by
  unfold allocAt at executed
  split at executed
  · cases executed
  · split at executed
    · cases executed
    · split at executed
      · cases executed
      · unfold bindResults at executed
        split at executed
        · cases executed
        · cases executed
          rfl

/-- A source allocation receives the fresh target allocation identity. Old
indices retain their identity even when target-only compiler frames exist. -/
def extendIds (source : Mem) (target : Memory) (ids : Nat → AllocId) : Nat → AllocId :=
  fun index => if index = source.allocs.length then ⟨target.nextAllocId⟩ else ids index

private theorem sourceAllocated_old {source : Mem} {size align index : Nat}
    (earlier : index < source.allocs.length) :
    nth? (sourceAllocated source size align).allocs index = nth? source.allocs index := by
  simp [sourceAllocated, nth?_append_one, earlier]

private theorem sourceAllocated_new (source : Mem) (size align : Nat) :
    nth? (sourceAllocated source size align).allocs source.allocs.length =
      some { base := SemR.alignUp source.nextAddr align, size := size, align := align,
             live := true, data := [] } := by
  simp [sourceAllocated, nth?_append_one]

private theorem allocated_new_lookup (target : Memory) (size align : Nat) :
    (target.alloc size align 0 .rustStack).snd.lookup ⟨target.nextAllocId⟩ =
      some (target.allocRecord size align 0 .rustStack) := by
  simp [Memory.alloc, Memory.lookup, Memory.allocRecord]

theorem Embeds.allocate_source {source : Mem} {target : Memory} {ids : Nat → AllocId}
    (embedding : Embeds source target ids) (size align : Nat) (nonzero : align ≠ 0)
    (capacity : TrustIr.alignUp target.nextAddr align + max size 1 < addrSpace) :
    Embeds (sourceAllocated source size align)
      (target.alloc size align 0 .rustStack).snd (extendIds source target ids) := by
  have oldTarget := embedding.allocate_private size align
  have newImage : AllocationImage
      { base := SemR.alignUp source.nextAddr align, size := size, align := align,
        live := true, data := [] }
      (target.allocRecord size align 0 .rustStack) := by
    refine ⟨rfl, rfl, rfl, ⟨nonzero, ?_⟩, ?_⟩
    · exact TrustIr.alignUp_mod target.nextAddr align nonzero
    · dsimp [Memory.allocRecord]
      exact Nat.le_trans (Nat.add_le_add_left (Nat.le_max_left _ _) _) (Nat.le_of_lt capacity)
  refine ⟨oldTarget.layout, oldTarget.fresh, ?_, ?_, ?_⟩
  · intro index allocation present
    by_cases earlier : index < source.allocs.length
    · rw [sourceAllocated_old earlier] at present
      have different : index ≠ source.allocs.length := Nat.ne_of_lt earlier
      simpa [extendIds, different] using oldTarget.records index allocation present
    · rw [sourceAllocated, nth?_append_one] at present
      simp only [earlier, ↓reduceIte] at present
      split at present
      · rename_i equal
        subst index
        cases present
        exact ⟨_, by simpa [extendIds] using allocated_new_lookup target size align, newImage⟩
      · cases present
  · intro index allocation record present found live offset inBounds
    by_cases earlier : index < source.allocs.length
    · rw [sourceAllocated_old earlier] at present
      have different : index ≠ source.allocs.length := Nat.ne_of_lt earlier
      simp only [extendIds, different, ↓reduceIte] at found
      exact oldTarget.bytes index allocation record present found live offset inBounds
    · rw [sourceAllocated, nth?_append_one] at present
      simp only [earlier, ↓reduceIte] at present
      split at present
      · rename_i equal
        subst index
        cases present
        simp only [extendIds, ↓reduceIte] at found
        rw [allocated_new_lookup] at found
        cases found
        rw [allocated_bytes]
        have start := TrustIr.le_alignUp target.nextAddr align
        have unwritten := embedding.fresh
          ((target.allocRecord size align 0 .rustStack).base + offset) (by
            dsimp [Memory.allocRecord]
            frame_arith)
        rw [unwritten]
        change ByteImage (byteAt [] offset) none
        rw [byteAt_nil]
        trivial
      · cases present
  · intro first allocation firstPresent second other secondPresent equal
    have firstBound := nth?_lt _ _ _ firstPresent
    have secondBound := nth?_lt _ _ _ secondPresent
    simp only [sourceAllocated, List.length_append, List.length_cons, List.length_nil] at firstBound secondBound
    by_cases firstNew : first = source.allocs.length
    · by_cases secondNew : second = source.allocs.length
      · exact firstNew.trans secondNew.symm
      · have secondEarlier : second < source.allocs.length := by frame_arith
        rw [sourceAllocated_old secondEarlier] at secondPresent
        have below := embedding.identity_below second other secondPresent
        simp only [extendIds, firstNew, secondNew, ↓reduceIte] at equal
        have same := congrArg AllocId.id equal
        frame_arith
    · have firstEarlier : first < source.allocs.length := by frame_arith
      rw [sourceAllocated_old firstEarlier] at firstPresent
      by_cases secondNew : second = source.allocs.length
      · have below := embedding.identity_below first allocation firstPresent
        simp only [extendIds, firstNew, secondNew, ↓reduceIte] at equal
        have same := congrArg AllocId.id equal
        frame_arith
      · have secondEarlier : second < source.allocs.length := by frame_arith
        rw [sourceAllocated_old secondEarlier] at secondPresent
        simp only [extendIds, firstNew, secondNew, ↓reduceIte] at equal
        exact embedding.injective first allocation firstPresent second other secondPresent equal

/-- The checked bridge consumes an actual successful SemR allocation, including
its existing OOM/arity checks, rather than a fabricated source-allocation row. -/
theorem Embeds.after_allocAt {pointerBits : Nat} {before after : Core} {node : Node}
    {target : Memory} {ids : Nat → AllocId} {size align : Nat}
    (embedding : Embeds before.mem target ids)
    (executed : allocAt pointerBits before node size align = .ok after)
    (nonzero : align ≠ 0)
    (capacity : TrustIr.alignUp target.nextAddr align + max size 1 < addrSpace) :
    Embeds after.mem (target.alloc size align 0 .rustStack).snd
      (extendIds before.mem target ids) := by
  rw [allocAt_memory executed]
  exact embedding.allocate_source size align nonzero capacity

/-- The same bridge consumes SemR's checked relational allocation rule. Its
soundness link supplies the successful equation; no surrogate step replaces it. -/
theorem Embeds.after_allocates {pointerBits : Nat} {before after : Core} {node : Node}
    {target : Memory} {ids : Nat → AllocId} {size align : Nat}
    (embedding : Embeds before.mem target ids)
    (step : Allocates pointerBits before node.results size align (.cont after))
    (nonzero : align ≠ 0)
    (capacity : TrustIr.alignUp target.nextAddr align + max size 1 < addrSpace) :
    Embeds after.mem (target.alloc size align 0 .rustStack).snd
      (extendIds before.mem target ids) := by
  have sound := allocates_sound pointerBits before node size align (.cont after) step
  cases executed : allocAt pointerBits before node size align with
  | stop outcome => simp [executed, ofR] at sound
  | ok state =>
    have same : state = after := by simpa [executed, ofR] using sound
    subst state
    exact embedding.after_allocAt executed nonzero capacity

/-- Necessary allocation-aware input for a finite machine-frame candidate.
The source embedding is checked over the whole allocation population; frame
alignment/capacity are the existing canonical rules. No physical SP placement,
instruction census, lifetime, call authority or serialized token is supplied. -/
structure FrameAllocationInput (source : Mem) (target : Memory) (ids : Nat → AllocId)
    (size align : Nat) : Prop where
  embedding : Embeds source target ids
  alignment : TrustIr.isPow2 align = true
  capacity : TrustIr.alignUp target.nextAddr align + max size 1 < addrSpace
  nonNull : 0 < TrustIr.alignUp target.nextAddr align

theorem FrameAllocationInput.preserves {source : Mem} {target after : Memory}
    {ids : Nat → AllocId} {size align : Nat}
    (input : FrameAllocationInput source target ids size align)
    (writes : FrameWrites (target.allocRecord size align 0 .rustStack)
      (target.alloc size align 0 .rustStack).snd after) : Embeds source after ids :=
  input.embedding.private_frame_writes size align after writes

theorem FrameAllocationInput.alignment_nonzero {source : Mem} {target : Memory}
    {ids : Nat → AllocId} {size align : Nat}
    (input : FrameAllocationInput source target ids size align) : align ≠ 0 := by
  intro zero
  subst align
  have alignment := input.alignment
  change false = true at alignment
  cases alignment

theorem FrameAllocationInput.actual_frame {source : Mem} {target : Memory}
    {ids : Nat → AllocId} {size align : Nat}
    (input : FrameAllocationInput source target ids size align) :
    (target.alloc size align 0 .rustStack).snd.lookup ⟨target.nextAllocId⟩ =
      some (target.allocRecord size align 0 .rustStack) ∧
    (target.allocRecord size align 0 .rustStack).base % align = 0 ∧
    (target.allocRecord size align 0 .rustStack).base + size < addrSpace := by
  refine ⟨allocated_new_lookup target size align,
    TrustIr.alignUp_mod target.nextAddr align input.alignment_nonzero, ?_⟩
  have capacity := input.capacity
  dsimp [Memory.allocRecord]
  have small := Nat.le_max_left size 1
  frame_arith

end SemR.MemoryEmbedding
