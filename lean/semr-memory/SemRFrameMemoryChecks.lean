-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import SemRFrameMemory

/-! Narrow kernel-checked controls. The O0-shaped store pattern below uses the
observed 32-byte frame's offsets16/24 (saved registers) and8 (pointer spill).
It is a theorem for arbitrary source images/register bytes, not a certificate
that the actual compiler has supplied a heap/ABI/physical-SP embedding.
-/

namespace SemR.MemoryEmbedding.Checks

open TrustIr (Memory Allocation AllocId Addr)

local macro "frame_arith" : tactic =>
  `(tactic| ((try simp only [Addr] at *) <;> (try dsimp only at *) <;> omega))

example (byte : UInt8) : ¬ ByteImage .uninit (some byte) := by
  simp [ByteImage]

example (byte : UInt8) : ¬ ByteImage (.init 256) (some byte) := by
  intro image
  have invalid := image.initialized_bounded
  frame_arith

private def twoSourceSlots : Mem :=
  sourceAllocated (sourceAllocated Mem.empty 8 8) 16 8

/-- Two source allocation identities cannot be collapsed onto one target id. -/
example (target : Memory) : ¬ Embeds twoSourceSlots target (fun _ => ⟨0⟩) := by
  intro embedding
  have first : nth? twoSourceSlots.allocs 0 = some
      { base := 1024, size := 8, align := 8, live := true, data := [] } := rfl
  have second : nth? twoSourceSlots.allocs 1 = some
      { base := 1032, size := 16, align := 8, live := true, data := [] } := rfl
  have impossible := embedding.injective 0 _ first 1 _ second rfl
  cases impossible

/-- The entire allocation extent is checked, not just a fitting first byte. -/
example : ¬ AllocationImage
    { base := 1024, size := 8, align := 8, live := true, data := [] }
    { id := ⟨0⟩, base := 2048, size := 16, alive := true, origin := .rustStack,
      requested := 16 } := by
  intro image
  have impossible := image.size
  cases impossible

private def ids : Nat → AllocId := fun id => ⟨id⟩
private def sourceSlot : Mem := sourceAllocated Mem.empty 8 8
private def targetSlot : Memory := (Memory.empty.alloc 8 8 0 .rustStack).snd
private def slotIds : Nat → AllocId := extendIds Mem.empty Memory.empty ids

private theorem slot_embeds : Embeds sourceSlot targetSlot slotIds :=
  (empty_embeds ids).allocate_source 8 8 (by decide) (by decide)

private def frame : Allocation := targetSlot.allocRecord 32 16 0 .rustStack
private def withFrame : Memory := (targetSlot.alloc 32 16 0 .rustStack).snd

example : FrameAllocationInput sourceSlot targetSlot slotIds 32 16 :=
  ⟨slot_embeds, rfl, by decide, by decide⟩

/-- A zero alignment cannot acquire the checked frame input. -/
example : ¬ FrameAllocationInput sourceSlot targetSlot slotIds 32 0 := by
  intro input
  exact input.alignment_nonzero rfl

/-- Finite-u64 exhaustion is not silently treated as allocation freshness. -/
example : ¬ FrameAllocationInput Mem.empty
    { Memory.empty with nextAddr := addrSpace - 16 } ids 32 16 := by
  intro input
  have impossible := input.capacity
  have noRoom : ¬ (TrustIr.alignUp (addrSpace - 16) 16 + max 32 1 < addrSpace) := by decide
  exact noRoom impossible

/-- The actual O0 frame's three store windows, for arbitrary stored bytes and
arbitrary embedded live source allocations/images, preserve the embedding. -/
theorem observed_o0_windows_preserve (source : Mem) (target : Memory) (injection : Nat → AllocId)
    (input : FrameAllocationInput source target injection 32 16)
    (savedFP savedLR pointer : List UInt8)
    (fpWidth : savedFP.length = 8) (lrWidth : savedLR.length = 8)
    (pointerWidth : pointer.length = 8) :
    Embeds source
      ((((target.alloc 32 16 0 .rustStack).snd.writeBytes
        ((target.allocRecord 32 16 0 .rustStack).base + 16) savedFP).writeBytes
        ((target.allocRecord 32 16 0 .rustStack).base + 24) savedLR).writeBytes
        ((target.allocRecord 32 16 0 .rustStack).base + 8) pointer) injection := by
  apply input.preserves
  apply FrameWrites.store
  · apply FrameWrites.store
    · apply FrameWrites.store
      · exact FrameWrites.done _
      · unfold WithinFrame
        simp only [fpWidth, Memory.allocRecord, Nat.add_zero]
        constructor <;> frame_arith
    · unfold WithinFrame
      simp only [lrWidth, Memory.allocRecord, Nat.add_zero]
      constructor <;> frame_arith
  · unfold WithinFrame
    simp only [pointerWidth, Memory.allocRecord, Nat.add_zero]
    constructor <;> frame_arith

example (bytes : List UInt8) (width : bytes.length = 1) :
    ¬ WithinFrame frame (frame.base + 32) bytes := by
  intro outside
  have bound := outside.2
  simp only [width, frame, Memory.allocRecord, Nat.add_zero] at bound
  frame_arith

/-- A stale/source provenance id cannot dereference the new frame, even though
its numeric address is allocated. This exercises the actual access checker. -/
example :
    TrustIr.Sem.run (TrustIr.Sem.checkedAccess "Store" frame.base ⟨0⟩ 1 1)
      { TrustIr.MachineState.empty with memory := withFrame } =
      .error (.ub "Store: access is out of bounds") := rfl

/-- The fresh frame's own provenance admits its in-bounds spill location. -/
example :
    TrustIr.Sem.run (TrustIr.Sem.checkedAccess "Store" (frame.base + 24) ⟨1⟩ 8 8)
      { TrustIr.MachineState.empty with memory := withFrame } =
      .ok (frame.base + 24, { TrustIr.MachineState.empty with memory := withFrame }) := rfl

/-- Raw memory really changes inside the frame. Therefore these lemmas cannot
replace the current unrestricted whole-raw-array CIC equality with a false one. -/
example : (withFrame.writeBytes frame.base [7]).bytes frame.base ≠ withFrame.bytes frame.base := by
  decide

#print axioms Embeds.private_frame_writes
#print axioms Embeds.after_allocAt
#print axioms Embeds.after_allocates
#print axioms Embeds.private_frame_keeps_source_permissions
#print axioms FrameWrites.pointer_image
#print axioms FrameAllocationInput.actual_frame
#print axioms observed_o0_windows_preserve

end SemR.MemoryEmbedding.Checks
