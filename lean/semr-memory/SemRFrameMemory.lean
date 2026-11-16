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

/-- Recover the original source record after the existing source byte update.
Only its data prefix changes; population and every metadata field are retained. -/
private theorem written_u8_origin {source : Mem} {index offset : Nat}
    {allocation : Alloc} {byte : UInt8}
    (present : nth? source.allocs index = some allocation)
    (query : Nat) (updated : Alloc)
    (found : nth? (written source index offset allocation [.init byte.toNat]).allocs query =
      some updated) :
    ∃ original, nth? source.allocs query = some original ∧
      updated = { original with data :=
        if query = index then writeBytes original.data offset [.init byte.toNat]
        else original.data } := by
  have bound := nth?_lt source.allocs index allocation present
  by_cases same : query = index
  · subst query
    simp only [written, nth?_setNth, bound, and_self, ↓reduceIte] at found
    cases found
    exact ⟨allocation, present, by simp⟩
  · simp only [written, nth?_setNth, same, false_and, ↓reduceIte] at found
    exact ⟨updated, found, by simp [same]⟩

/-- A legal initialized source-byte update and the same canonical byte write
preserve the COMPLETE allocation embedding. No raw address, source permission,
source execution, entry heap or NoUB witness is manufactured by this lemma. -/
theorem Embeds.written_u8 {source : Mem} {memory : Memory} {ids : Nat → AllocId}
    (embedding : Embeds source memory ids)
    (index offset : Nat) (allocation : Alloc) (record : Allocation)
    (present : nth? source.allocs index = some allocation)
    (found : memory.lookup (ids index) = some record)
    (live : allocation.live = true) (inside : offset + 1 ≤ allocation.size) (byte : UInt8) :
    Embeds (written source index offset allocation [.init byte.toNat])
      (memory.writeBytes (record.base + offset) [byte]) ids := by
  obtain ⟨original, originalFound, related⟩ := embedding.records index allocation present
  have same : original = record := by
    rw [found] at originalFound
    exact (Option.some.inj originalFound).symm
  subst original
  have recordMember := (lookup_record found).1
  have bound := (embedding.layout.2.2.1 record recordMember).1
  have writeBound : record.base + offset + [byte].length ≤ memory.nextAddr := by
    have size := related.size
    simp only [List.length_cons, List.length_nil]
    frame_arith
  refine ⟨embedding.layout,
    write_preserves_fresh memory (record.base + offset) [byte] embedding.fresh writeBound,
    ?_, ?_, ?_⟩
  · intro query updated newPresent
    obtain ⟨old, oldPresent, rfl⟩ := written_u8_origin present query updated newPresent
    obtain ⟨other, otherFound, otherRelated⟩ := embedding.records query old oldPresent
    exact ⟨other, otherFound, ⟨otherRelated.size, otherRelated.requested,
      otherRelated.live, otherRelated.alignment, otherRelated.finite⟩⟩
  · intro query updated other newPresent otherFound updatedLive position positionBound
    change memory.lookup (ids query) = some other at otherFound
    obtain ⟨old, oldPresent, rfl⟩ := written_u8_origin present query updated newPresent
    by_cases atIndex : query = index
    · subst query
      have oldSame : old = allocation := by
        rw [present] at oldPresent
        exact (Option.some.inj oldPresent).symm
      subst old
      have otherSame : other = record := by
        rw [found] at otherFound
        exact (Option.some.inj otherFound).symm
      subst other
      simp only [ite_true] at *
      change ByteImage
        (byteAt (writeBytes allocation.data offset [.init byte.toNat]) position)
        ((memory.writeBytes (record.base + offset) [byte]).bytes (record.base + position))
      by_cases atByte : position = offset
      · subst position
        have stored : (memory.writeBytes (record.base + offset) [byte]).bytes
            (record.base + offset) = some byte := by
          simpa using Memory.bytes_writeBytes_inside memory (record.base + offset) 0 [byte] (by simp)
        simp only [writeBytes, byteAt_setByte_same, stored, ByteImage]
      · have outside : record.base + position < record.base + offset ∨
            record.base + offset + [byte].length ≤ record.base + position := by
          simp only [List.length_cons, List.length_nil]
          frame_arith
        simp only [writeBytes, byteAt_setByte_ne _ offset position _ atByte]
        rw [Memory.bytes_writeBytes_outside memory (record.base + offset)
          (record.base + position) [byte] outside]
        exact embedding.bytes index allocation record present found live position positionBound
    · have dataSame : (if query = index then writeBytes old.data offset [.init byte.toNat]
          else old.data) = old.data := by simp [atIndex]
      change ByteImage (byteAt (if query = index then _ else _) position) _
      rw [dataSame]
      obtain ⟨oldRecord, oldFound, oldRelated⟩ := embedding.records query old oldPresent
      have otherSame : oldRecord = other := by
        rw [otherFound] at oldFound
        exact (Option.some.inj oldFound).symm
      subst oldRecord
      have distinct : record ≠ other := by
        intro equal
        have firstId := (lookup_record found).2
        have otherId := (lookup_record otherFound).2
        rw [← equal] at otherId
        have idEqual : ids query = ids index := otherId.symm.trans firstId
        exact atIndex (embedding.injective query old oldPresent index allocation present idEqual)
      have separate := embedding.layout.2.2.2.1 record recordMember other
        (lookup_record otherFound).1 distinct
      have outside : other.base + position < record.base + offset ∨
          record.base + offset + [byte].length ≤ other.base + position := by
        have firstSize := related.size
        have otherSize := oldRelated.size
        simp only [List.length_cons, List.length_nil]
        rcases separate with before | after
        · right
          frame_arith
        · left
          frame_arith
      rw [Memory.bytes_writeBytes_outside memory (record.base + offset)
        (other.base + position) [byte] outside]
      exact embedding.bytes query old other oldPresent otherFound updatedLive position positionBound
  · intro first updated firstPresent second other secondPresent equal
    obtain ⟨firstOld, firstOldPresent, _⟩ := written_u8_origin present first updated firstPresent
    obtain ⟨secondOld, secondOldPresent, _⟩ := written_u8_origin present second other secondPresent
    exact embedding.injective first firstOld firstOldPresent second secondOld secondOldPresent equal

/-- Successful existing checked access returns the actual source record;
this is not a new pointer checker or a replacement access computation. -/
private theorem accessAt_record {source : Mem} {index offset size align : Nat}
    {allocation accessed : Alloc} {operation : String}
    (present : nth? source.allocs index = some allocation)
    (executed : accessAt source operation index offset size align = .ok accessed) :
    accessed = allocation := by
  simp only [accessAt, present] at executed
  unfold accessAlloc at executed
  repeat' split at executed
  all_goals cases executed <;> rfl

private theorem storeImage_u8 (pointerBits : Nat) (byte : UInt8) :
    storeImage pointerBits (.int .u8) false 1 (.int .u8 byte.toNat) =
      .ok [.init byte.toNat] := by
  have bounded : byte.toNat < modulus (IntTy.u8.bits pointerBits) := byte.toNat_lt
  have typed : expectTy pointerBits (.int .u8 byte.toNat) (.int .u8) = .ok () := by
    simp [expectTy, Val.ty, Ty.beq, IntTy.code, bounded]
  simp [storeImage, typed, encodeVal, IntTy.bytes, leBytes,
    Nat.mod_eq_of_lt byte.toNat_lt]
  rfl

/-- The real source access checks follow from a live finite allocation and
an in-bounds byte offset. Numerical target addresses supply no source access. -/
theorem accessAt_u8 (memory : Mem) (operation : String) (index offset : Nat)
    (allocation : Alloc)
    (present : nth? memory.allocs index = some allocation)
    (live : allocation.live = true)
    (finite : allocation.base + allocation.size < addrSpace)
    (inside : offset + 1 ≤ allocation.size) :
    accessAt memory operation index offset 1 1 = .ok allocation := by
  have address : ¬ addrSpace ≤ allocation.base + offset := by omega
  have range : ¬ addrSpace ≤ offset + 1 := by omega
  have bounds : ¬ allocation.size < offset + 1 := by omega
  simp [accessAt, present, accessAlloc, live, address, range, bounds, Nat.mod_one]

/-- Derive the actual Store computation from its typed SSA operands and live,
finite, in-bounds source allocation. Successful execution is a conclusion,
not an extra premise. This grants no Rust borrow or native entry permission. -/
theorem storeStep_u8 (pointerBits : Nat) (before : Core) (ptr value index offset : Nat)
    (allocation : Alloc) (byte : UInt8)
    (pointer : getV before ptr = .ok (.ptr index offset))
    (stored : getV before value = .ok (.int .u8 byte.toNat))
    (present : nth? before.mem.allocs index = some allocation)
    (live : allocation.live = true)
    (finite : allocation.base + allocation.size < addrSpace)
    (inside : offset + 1 ≤ allocation.size) :
    storeStep pointerBits before
      { inst := .store (.int .u8) ptr value false none, results := [] }
      (.int .u8) ptr value false none =
      .ok { next before with mem := written before.mem index offset allocation [.init byte.toNat] } := by
  have access := accessAt_u8 before.mem "Store" index offset allocation present live finite inside
  have image := storeImage_u8 pointerBits byte
  have aligned : checkAlign 1 = .ok 1 := rfl
  have expected : expectPtr (.ptr index offset) "Store" = .ok (index, offset) := rfl
  simp only [storeStep, pointer, stored, scalarLayout, IntTy.bytes]
  dsimp only [Bind.bind, R.bind]
  simp only [image, Option.getD_none, aligned, expected, access, bindResults,
    List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    List.zip_nil_left, List.reverse_nil, List.nil_append]

/-- A source byte with its exact initialized value is loaded through the real
checked access path. Both plain and volatile loads have this result; poison
and malformed result arity are not silently converted to initialized data. -/
theorem loadStep_u8 (pointerBits : Nat) (before : Core) (ptr result index offset : Nat)
    (allocation : Alloc) (byte : UInt8) (volatile : Bool)
    (pointer : getV before ptr = .ok (.ptr index offset))
    (present : nth? before.mem.allocs index = some allocation)
    (live : allocation.live = true)
    (finite : allocation.base + allocation.size < addrSpace)
    (inside : offset + 1 ≤ allocation.size)
    (initialized : byteAt allocation.data offset = .init byte.toNat) :
    loadStep pointerBits before
      { inst := .load (.int .u8) ptr volatile none, results := [result] }
      (.int .u8) ptr volatile none =
      .ok { next before with env := (result, .int .u8 byte.toNat) :: before.env } := by
  have access := accessAt_u8 before.mem "Load" index offset allocation present live finite inside
  have aligned : checkAlign 1 = .ok 1 := rfl
  have expected : expectPtr (.ptr index offset) "Load" = .ok (index, offset) := rfl
  simp only [loadStep, pointer, scalarLayout, IntTy.bytes]
  dsimp only [Bind.bind, R.bind]
  simp only [Option.getD_none, aligned, expected, access]
  simp [readBytes, initialized, readOut, firstUninit, decodeVal, fromLE,
    bindResults, Bind.bind, R.bind, next]

/-- Derive the actual narrowing cast from its typed source SSA operand. The
result is the source integer's low byte, not a byte selected from an exit. -/
theorem castStep_trunc_u64_u8 (pointerBits : Nat) (before : Core) (input result : Nat)
    (value : UInt64)
    (operand : getV before input = .ok (.int .u64 value.toNat)) :
    castStep pointerBits before
      { inst := .cast .trunc (.int .u64) (.int .u8) input, results := [result] }
      .trunc (.int .u64) (.int .u8) input =
      .ok { next before with
        env := (result, .int .u8 (UInt8.ofNat value.toNat).toNat) :: before.env } := by
  have bounded : value.toNat < modulus (IntTy.u64.bits pointerBits) := value.toNat_lt
  have typed : expectTy pointerBits (.int .u64 value.toNat) (.int .u64) = .ok () := by
    simp [expectTy, Val.ty, Ty.beq, IntTy.code, bounded]
  simp [castStep, operand, evalCast, rejectPoison, typed, castCore, resizeOf,
    bindResults, Bind.bind, R.bind, next, IntTy.bits, modulus]

/-- Widen the previously loaded source byte through the real cast evaluator.
The complete original Core is retained except for pc and the declared result. -/
theorem castStep_zext_u8_u64 (pointerBits : Nat) (before : Core) (input result : Nat)
    (byte : UInt8)
    (operand : getV before input = .ok (.int .u8 byte.toNat)) :
    castStep pointerBits before
      { inst := .cast .zext (.int .u8) (.int .u64) input, results := [result] }
      .zext (.int .u8) (.int .u64) input =
      .ok { next before with env := (result, .int .u64 byte.toNat) :: before.env } := by
  have bounded : byte.toNat < modulus (IntTy.u8.bits pointerBits) := byte.toNat_lt
  have widened : byte.toNat < modulus (IntTy.u64.bits pointerBits) := by
    change byte.toNat < 2 ^ 64
    have small := byte.toNat_lt
    change byte.toNat < 256 at small
    omega
  have typed : expectTy pointerBits (.int .u8 byte.toNat) (.int .u8) = .ok () := by
    simp [expectTy, Val.ty, Ty.beq, IntTy.code, bounded]
  simp [castStep, operand, evalCast, rejectPoison, typed, castCore, resizeOf,
    bindResults, Bind.bind, R.bind, next, Nat.mod_eq_of_lt widened]

/-- Extract the ENTIRE Core of one successful existing nonvolatile U8 Store.
No source metadata, cells, environment or call state is reconstructed from a
raw native post-array. The fetched-node wrapper below binds this computation
to the actual source body rather than a detached instruction. -/
theorem storeStep_u8_core {pointerBits : Nat} {before after : Core} {node : Node}
    {ptr value index offset : Nat} {allocation : Alloc} {byte : UInt8}
    (noResults : node.results = [])
    (pointer : getV before ptr = .ok (.ptr index offset))
    (stored : getV before value = .ok (.int .u8 byte.toNat))
    (present : nth? before.mem.allocs index = some allocation)
    (executed : storeStep pointerBits before node (.int .u8) ptr value false none = .ok after) :
    after = { next before with
      mem := written before.mem index offset allocation [.init byte.toNat] } := by
  have image := storeImage_u8 pointerBits byte
  have aligned : checkAlign 1 = .ok 1 := rfl
  have expected : expectPtr (.ptr index offset) "Store" = .ok (index, offset) := rfl
  simp only [storeStep, pointer, stored, scalarLayout, IntTy.bytes] at executed
  dsimp only [Bind.bind, R.bind] at executed
  simp only [image, Option.getD_none, aligned, expected] at executed
  cases accessed : accessAt before.mem "Store" index offset 1 1 with
  | stop output =>
    rw [accessed] at executed
    cases executed
  | ok record =>
    have same := accessAt_record present accessed
    subst record
    simp only [accessed] at executed
    simp only [bindResults, noResults, List.length_nil, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte, List.zip_nil_left, List.reverse_nil, List.nil_append] at executed
    cases executed
    rfl

/-- A successful Store computation belongs to the actual source transition
only when that exact instruction is fetched at the actual body/pc. -/
theorem step_u8_of_storeStep (module : Module) (before after : Core)
    (ptr value : Nat)
    (fetched : nth? before.block.body before.pc =
      some { inst := .store (.int .u8) ptr value false none, results := [] })
    (executed : storeStep module.pointerBits before
      { inst := .store (.int .u8) ptr value false none, results := [] }
      (.int .u8) ptr value false none = .ok after) :
    Step module before (.cont after) := by
  have actual := step_complete module before
  simpa only [stepCore, fetched, execNode, executed, ofR] using actual

/-- Successful result publication changes exactly the actual SSA environment.
The memory, cells, call state and frame lineages are the original ones. -/
private theorem bindResults_next_core {before after : Core} {node : Node} {value : Val}
    (executed : bindResults (next before) node [value] = .ok after) :
    after = { next before with env := (node.results.zip [value]).reverse ++ before.env } := by
  unfold bindResults at executed
  split at executed
  · cases executed
  · cases executed
    rfl

/-- Both initialized and poison reads preserve the entire source state apart
from the next pc and the declared SSA result. This grants no initialized-byte
image: the later source cast/store must still supply its actual checked value. -/
private theorem readOut_core {before after : Core} {node : Node} {ty : Ty}
    {offset : Nat} {bytes : List AByte}
    (executed : readOut before node ty false offset bytes = .ok after) :
    ∃ value, after =
      { next before with env := (node.results.zip [value]).reverse ++ before.env } := by
  cases uninit : firstUninit bytes with
  | none =>
    simp only [readOut, uninit] at executed
    cases decoded : decodeVal ty bytes with
    | stop output =>
      simp only [decoded, Bind.bind, R.bind] at executed
      cases executed
    | ok value =>
      simp only [decoded, Bind.bind, R.bind] at executed
      exact ⟨value, bindResults_next_core executed⟩
  | some index =>
    simp only [readOut, uninit, Bool.false_eq_true, ↓reduceIte] at executed
    exact ⟨.partialBytes ty bytes, bindResults_next_core executed⟩

/-- Extract a real successful U8 load through its source pointer. In
particular it does not write memory or lose logical cells/caller metadata. -/
theorem loadStep_u8_core {pointerBits : Nat} {before after : Core} {node : Node}
    {ptr index offset : Nat} {allocation : Alloc}
    (pointer : getV before ptr = .ok (.ptr index offset))
    (present : nth? before.mem.allocs index = some allocation)
    (executed : loadStep pointerBits before node (.int .u8) ptr false none = .ok after) :
    ∃ value, after =
      { next before with env := (node.results.zip [value]).reverse ++ before.env } := by
  have aligned : checkAlign 1 = .ok 1 := rfl
  have expected : expectPtr (.ptr index offset) "Load" = .ok (index, offset) := rfl
  simp only [loadStep, pointer, scalarLayout, IntTy.bytes] at executed
  dsimp only [Bind.bind, R.bind] at executed
  simp only [Option.getD_none, aligned, expected] at executed
  cases accessed : accessAt before.mem "Load" index offset 1 1 with
  | stop output =>
    rw [accessed] at executed
    cases executed
  | ok record =>
    have same := accessAt_record present accessed
    subst record
    simp only [accessed, Bind.bind, R.bind] at executed
    exact readOut_core executed

/-- A successful existing cast publishes only its actual SSA result and
advances the pc. It preserves memory, cells, call state and frame lineages. -/
theorem castStep_core {pointerBits : Nat} {before after : Core} {node : Node}
    {operation : CastOp} {source target : Ty} {operand : Nat}
    (executed : castStep pointerBits before node operation source target operand = .ok after) :
    ∃ value, after =
      { next before with env := (node.results.zip [value]).reverse ++ before.env } := by
  cases read : getV before operand with
  | stop output =>
    simp only [castStep, read, Bind.bind, R.bind] at executed
    cases executed
  | ok input =>
    simp only [castStep, read, Bind.bind, R.bind] at executed
    cases cast : evalCast pointerBits operation source target input with
    | stop output =>
      simp only [cast, Bind.bind, R.bind] at executed
      cases executed
    | ok value =>
      simp only [cast, Bind.bind, R.bind] at executed
      exact ⟨value, bindResults_next_core executed⟩

/-- Returning to an actual caller changes its control/environment fields,
but does not manufacture a heap, free cells or change frame lineages. -/
theorem retStep_preserves_data {pointerBits : Nat} {before after : Core}
    {node : Node} {results : List Nat}
    (executed : retStep pointerBits before node results = .ok after) :
    after.mem = before.mem ∧ after.cells = before.cells ∧
    after.nextCell = before.nextCell ∧ after.openFrames = before.openFrames ∧
    after.nextFrame = before.nextFrame := by
  cases values : getVs before results with
  | stop output =>
    simp only [retStep, values, Bind.bind, R.bind] at executed
    cases executed
  | ok returned =>
    simp only [retStep, values, Bind.bind, R.bind] at executed
    cases checked : checkSig pointerBits returned before.sig.returns with
    | stop output =>
      simp only [checked, Bind.bind, R.bind] at executed
      cases executed
    | ok unit =>
      simp only [checked, Bind.bind, R.bind] at executed
      cases callers : before.stack with
      | nil =>
        simp only [returnTo, callers] at executed
        cases executed
      | cons caller rest =>
        simp only [returnTo, callers] at executed
        unfold bindResults at executed
        split at executed
        · cases executed
        · cases executed
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end SemR.MemoryEmbedding
