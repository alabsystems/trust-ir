-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import SemRPlacedFrame

namespace SemR.MemoryEmbedding.PlacedChecks

open TrustIr (Memory Allocation AllocId Addr)

private def ids : Nat → AllocId := fun id => ⟨id⟩
private def frameMemory : Memory := (Memory.empty.alloc 16 16 0 .rustStack).snd
private def frame : Allocation := Memory.empty.allocRecord 16 16 0 .rustStack
private def source : Mem := sourceAllocated Mem.empty 8 8
private def target : Memory := (frameMemory.alloc 8 8 0 .rustStack).snd
private def sourceIds : Nat → AllocId := extendIds Mem.empty frameMemory ids

private theorem source_embeds : Embeds source target sourceIds :=
  ((empty_embeds ids).allocate_private 16 16).allocate_source 8 8 (by decide) (by decide)

private theorem frame_input : FrameRecordInput source target sourceIds frame := by
  refine ⟨source_embeds, ?_, ?_, rfl, rfl⟩
  · rfl
  · intro index allocation present
    cases index with
    | zero => decide
    | succ index =>
      change nth? [] index = some allocation at present
      simp [nth?] at present

/-- The target frame lies BELOW live source storage. The old stronger Before
premise is false, but the checked allocation-identity input is inhabited. -/
theorem below_source_is_admitted :
    PlacedFrameInput source target sourceIds frame 1040 16 := by
  exact ⟨frame_input, rfl, by decide, by decide, by decide, by decide, by decide, by decide⟩

example : ¬ Before source target sourceIds frame.base := by
  intro before
  have sourcePresent : nth? source.allocs 0 = some
      { base := 1024, size := 8, align := 8, live := true, data := [] } := rfl
  have targetPresent : target.lookup (sourceIds 0) = some
      { id := ⟨1⟩, base := 1040, size := 8, alive := true, origin := .rustStack,
        requested := 8 } := rfl
  have bad := before 0 _ _ sourcePresent targetPresent
  exact (by decide : ¬ ((1048 : Nat) ≤ 1024)) bad

/-- Actual FP/LR-sized windows, with arbitrary saved register bytes, preserve
the complete source embedding even in the descending address order. -/
theorem lower_frame_pair_preserves (fp lr : List UInt8)
    (fpSize : fp.length = 8) (lrSize : lr.length = 8) :
    Embeds source ((target.writeBytes frame.base fp).writeBytes (frame.base + 8) lr) sourceIds := by
  apply below_source_is_admitted.preserves
  apply FrameWrites.store (data := lr)
  · apply FrameWrites.store (data := fp)
    · exact FrameWrites.done target
    · constructor
      · exact Nat.le_refl _
      · simp [WithinFrame, frame, Memory.allocRecord, fpSize, TrustIr.alignUp]
  · constructor
    · exact Nat.le_add_right _ _
    · simp [frame, Memory.allocRecord, lrSize, TrustIr.alignUp]

example : ¬ PlacedFrameInput source target sourceIds frame 1041 16 := by
  intro input
  have bad := input.endAtSp
  exact (by decide : (1040 : Nat) ≠ 1041) bad

example : ¬ PlacedFrameInput source target sourceIds frame 1040 0 := by
  intro input
  cases input.validAlignment

example : ¬ FrameRecordInput source target sourceIds
    (frameMemory.allocRecord 8 8 0 .rustStack) := by
  intro input
  have sourcePresent : nth? source.allocs 0 = some
      { base := 1024, size := 8, align := 8, live := true, data := [] } := rfl
  have bad := input.freshIdentity 0 _ sourcePresent
  exact bad rfl

example : ¬ WithinFrame frame (frame.base + frame.size) [1] := by
  intro inside
  exact (by decide : ¬ ((1040 : Nat) + 1 ≤ 1040)) inside.2

end SemR.MemoryEmbedding.PlacedChecks

#print axioms SemR.MemoryEmbedding.FrameRecordInput.separates
#print axioms SemR.MemoryEmbedding.FrameRecordInput.write
#print axioms SemR.MemoryEmbedding.FrameRecordInput.preserves
#print axioms SemR.MemoryEmbedding.FrameRecordInput.source_access_apart
#print axioms SemR.MemoryEmbedding.PlacedFrameInput.preserves
#print axioms SemR.MemoryEmbedding.PlacedChecks.below_source_is_admitted
#print axioms SemR.MemoryEmbedding.PlacedChecks.lower_frame_pair_preserves
