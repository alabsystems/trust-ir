-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import SemRFrameMemory

/-! Frame input at an actual placement, including below source storage.

The bump-allocation theorem remains unchanged. This interface consumes an
already registered allocation in the same canonical Memory, its checked whole
source embedding, and freshness of its identity relative to source allocations.
Existing layoutWF then derives separation in either address order. It creates
no allocator, source heap, pointer/SP premise, machine trace or compiler grade.
-/

namespace SemR.MemoryEmbedding

open TrustIr (Memory Allocation AllocId Addr PermissionMap Permission)

local macro "frame_arith" : tactic =>
  `(tactic| ((try simp only [Addr] at *) <;> (try dsimp only at *) <;> omega))

private theorem record_of_lookup {memory : Memory} {id : AllocId} {record : Allocation}
    (found : memory.lookup id = some record) :
    record ∈ memory.allocations ∧ record.id = id := by
  change memory.allocations.find? (fun allocation => allocation.id == id) = some record at found
  exact ⟨TrustIr.mem_of_find?_some found, by simpa using TrustIr.find?_some_pred found⟩

/-- A real target record with an identity not used by any source allocation.
No condition compares an arbitrary raw pointer or query with SP. -/
structure FrameRecordInput (source : Mem) (target : Memory) (ids : Nat → AllocId)
    (frame : Allocation) : Prop where
  embedding : Embeds source target ids
  located : target.lookup frame.id = some frame
  freshIdentity : ∀ index allocation, nth? source.allocs index = some allocation →
    ids index ≠ frame.id
  live : frame.alive = true
  origin : frame.origin = .rustStack

/-- All source footprints are disjoint from the registered frame; either
address ordering is possible. This is derived from allocation identity. -/
theorem FrameRecordInput.separates {source : Mem} {target : Memory} {ids : Nat → AllocId}
    {frame : Allocation} (input : FrameRecordInput source target ids frame)
    (index : Nat) (allocation : Alloc) (record : Allocation)
    (present : nth? source.allocs index = some allocation)
    (found : target.lookup (ids index) = some record) :
    record.base + record.size ≤ frame.base ∨ frame.base + frame.size ≤ record.base := by
  obtain ⟨member, identity⟩ := record_of_lookup found
  have frameMember := (record_of_lookup input.located).1
  have different : record ≠ frame := by
    intro same
    subst record
    exact input.freshIdentity index allocation present identity.symm
  obtain ⟨_, _, _, disjoint, _⟩ := input.embedding.layout
  rcases disjoint record member frame frameMember different with before | after
  · exact Or.inl before.1
  · exact Or.inr after.1

/-- One actual canonical byte write preserves the full source embedding,
even when the frame is below a source allocation. -/
theorem FrameRecordInput.write {source : Mem} {target : Memory} {ids : Nat → AllocId}
    {frame : Allocation} (input : FrameRecordInput source target ids frame)
    (address : Addr) (data : List UInt8) (inside : WithinFrame frame address data) :
    FrameRecordInput source (target.writeBytes address data) ids frame := by
  have frameMember := (record_of_lookup input.located).1
  have frameBound := (input.embedding.layout.2.2.1 frame frameMember).1
  have writeBound : address + data.length ≤ target.nextAddr :=
    Nat.le_trans inside.2 frameBound
  refine ⟨?_, input.located, input.freshIdentity, input.live, input.origin⟩
  refine ⟨input.embedding.layout,
    write_preserves_fresh target address data input.embedding.fresh writeBound,
    input.embedding.records, ?_, input.embedding.injective⟩
  intro index allocation record present found live offset inBounds
  obtain ⟨original, originalFound, related⟩ := input.embedding.records index allocation present
  have same : original = record := by
    change target.lookup (ids index) = some record at found
    rw [originalFound] at found
    exact Option.some.inj found
  subst original
  have separation := input.separates index allocation record present found
  change ByteImage (byteAt allocation.data offset)
    ((target.writeBytes address data).bytes (record.base + offset))
  have old := input.embedding.bytes index allocation record present found live offset inBounds
  rcases separation with before | after
  · have queryBefore : record.base + offset < address := by
      have size := related.size
      have start := inside.1
      frame_arith
    rw [Memory.bytes_writeBytes_outside target address (record.base + offset) data (Or.inl queryBefore)]
    exact old
  · have queryAfter : address + data.length ≤ record.base + offset := by
      have stop := inside.2
      frame_arith
    rw [Memory.bytes_writeBytes_outside target address (record.base + offset) data (Or.inr queryAfter)]
    exact old

/-- The complete allocation embedding survives every confined write in the
actual registered frame. No raw-array equality or machine execution is claimed. -/
theorem FrameRecordInput.preserves {source : Mem} {target after : Memory}
    {ids : Nat → AllocId} {frame : Allocation}
    (input : FrameRecordInput source target ids frame)
    (writes : FrameWrites frame target after) : Embeds source after ids := by
  have retained : FrameRecordInput source after ids frame := by
    induction writes with
    | done => exact input
    | store prior address data inside induction => exact induction.write address data inside
  exact retained.embedding

/-- Checked physical placement input. These are proof fields, not a numeric
layout label supplied by a compiler. Entry-heap/ABI custody and all actual
instruction/call/lifetime proofs remain separate required inputs. -/
structure PlacedFrameInput (source : Mem) (target : Memory) (ids : Nat → AllocId)
    (frame : Allocation) (entrySp alignment : Nat) : Prop extends
    FrameRecordInput source target ids frame where
  endAtSp : frame.base + frame.size = entrySp
  positiveSize : 0 < frame.size
  nonNull : 0 < frame.base
  finiteSp : entrySp < addrSpace
  validAlignment : TrustIr.isPow2 alignment = true
  alignedBase : frame.base % alignment = 0
  alignedSp : entrySp % alignment = 0

theorem PlacedFrameInput.preserves {source : Mem} {target after : Memory}
    {ids : Nat → AllocId} {frame : Allocation} {entrySp alignment : Nat}
    (input : PlacedFrameInput source target ids frame entrySp alignment)
    (writes : FrameWrites frame target after) : Embeds source after ids :=
  input.toFrameRecordInput.preserves writes

/-- A checked source access cannot overlap the frame. The premise is an
actual source allocation/bounds proof, never an assumption about a raw pointer. -/
theorem FrameRecordInput.source_access_apart {source : Mem} {target : Memory}
    {ids : Nat → AllocId} {frame : Allocation}
    (input : FrameRecordInput source target ids frame)
    (index : Nat) (allocation : Alloc) (record : Allocation)
    (present : nth? source.allocs index = some allocation)
    (found : target.lookup (ids index) = some record)
    (offset width : Nat) (inBounds : offset + width ≤ allocation.size) :
    record.base + offset + width ≤ frame.base ∨
      frame.base + frame.size ≤ record.base + offset := by
  obtain ⟨original, originalFound, related⟩ := input.embedding.records index allocation present
  have same : original = record := by
    rw [found] at originalFound
    exact (Option.some.inj originalFound).symm
  subst original
  rcases input.separates index allocation record present found with before | after
  · left
    have size := related.size
    frame_arith
  · right
    frame_arith

end SemR.MemoryEmbedding
