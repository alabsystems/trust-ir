-- Copyright 2026 Andrew Yates | Apache-2.0
import SemRFramePair

namespace SemR.MemoryEmbedding.FramePair.Checks

open TrustIr (Memory Allocation AllocId)

private def ids : Nat → AllocId := fun n => ⟨n⟩
private def frameMemory : Memory := (Memory.empty.alloc 16 16 0 .rustStack).snd
private def frame : Allocation := Memory.empty.allocRecord 16 16 0 .rustStack
private def source : Mem := sourceAllocated Mem.empty 8 8
private def target : Memory := (frameMemory.alloc 8 8 0 .rustStack).snd
private def sourceIds : Nat → AllocId := extendIds Mem.empty frameMemory ids

private theorem placed : PlacedFrameInput source target sourceIds frame 1040 16 := by
  refine ⟨⟨((empty_embeds ids).allocate_private 16 16).allocate_source 8 8 (by decide) (by decide),
    rfl, ?_, rfl, rfl⟩, rfl, by decide, by decide, by decide, by decide, by decide, by decide⟩
  intro index allocation present
  cases index with
  | zero => decide
  | succ index =>
    change nth? [] index = some allocation at present
    simp [nth?] at present

private def raw : RawMemory := fun _ => 0

private theorem represented : RawRepresents target raw := by
  intro address byte _ defined
  cases defined

/-- Baseline allocation model with uninitialized live source storage. -/
theorem uninitialized_pair (fp lr : Word) :
    let saved := rawWriteBytes (rawWriteBytes raw frame.base (wordBytes fp))
      (frame.base + 8) (wordBytes lr)
    Embeds source (saveMemory target frame.base fp lr) sourceIds ∧
    rawReadWord saved frame.base = fp ∧ rawReadWord saved (frame.base + 8) = lr :=
  placed_pair_raw_readback placed rfl represented fp lr

-- Initialize two actual source bytes through SemR's existing byte writer,
-- and the same target bytes through canonical Memory.writeBytes. The other
-- six source bytes stay uninitialized; both cases remain in full Embeds.
private def initializedAllocation : Alloc :=
  { base := 1024, size := 8, align := 8, live := true,
    data := writeBytes [] 0 [.init 0x5a, .init 0xc3] }
private def initializedSource : Mem :=
  { source with allocs := setNth source.allocs 0 initializedAllocation }
private def sourceRecord : Allocation :=
  { id := ⟨1⟩, base := 1040, size := 8, alive := true, origin := .rustStack, requested := 8 }
private def initializedTarget : Memory := target.writeBytes 1040 [0x5a, 0xc3]
private def initializedRaw : RawMemory := rawWriteBytes raw 1040 [0x5a, 0xc3]

private theorem initialized_embeds : Embeds initializedSource initializedTarget sourceIds := by
  refine ⟨placed.embedding.layout,
    write_preserves_fresh target 1040 [0x5a, 0xc3] placed.embedding.fresh (by decide),
    ?_, ?_, ?_⟩
  · intro index allocation present
    cases index with
    | zero =>
      change some initializedAllocation = some allocation at present
      cases present
      exact ⟨sourceRecord, rfl, ⟨rfl, rfl, rfl, ⟨by decide, by decide⟩, by decide⟩⟩
    | succ index =>
      change nth? [] index = some allocation at present
      simp [nth?] at present
  · intro index allocation record present found _ offset bounded
    cases index with
    | zero =>
      change some initializedAllocation = some allocation at present
      cases present
      change some sourceRecord = some record at found
      cases found
      change offset < 8 at bounded
      have positions : offset = 0 ∨ offset = 1 ∨ offset = 2 ∨ offset = 3 ∨
          offset = 4 ∨ offset = 5 ∨ offset = 6 ∨ offset = 7 := by omega
      rcases positions with h | h | h | h | h | h | h | h
      all_goals subst offset; first | rfl | exact True.intro
    | succ index =>
      change nth? [] index = some allocation at present
      simp [nth?] at present
  · intro first allocation present second other another _
    cases first with
    | zero =>
      cases second with
      | zero => rfl
      | succ second =>
        change nth? [] second = some other at another
        simp [nth?] at another
    | succ first =>
      change nth? [] first = some allocation at present
      simp [nth?] at present

private theorem initialized_placed :
    PlacedFrameInput initializedSource initializedTarget sourceIds frame 1040 16 := by
  refine ⟨⟨initialized_embeds, rfl, ?_, rfl, rfl⟩,
    rfl, by decide, by decide, by decide, by decide, by decide, by decide⟩
  intro index allocation present
  cases index with
  | zero => decide
  | succ index =>
    change nth? [] index = some allocation at present
    simp [nth?] at present

private theorem initialized_represents : RawRepresents initializedTarget initializedRaw :=
  raw_represents_write represented 1040 [0x5a, 0xc3] (by decide)

/-- An inhabited initialized-source fixture: both initialized bytes, all six
uninitialized bytes, full raw/canonical representation, and all128 saved bits
survive the actual frame pair operations for arbitrary FP/LR values. -/
theorem initialized_pair (fp lr : Word) :
    let memory := saveMemory initializedTarget frame.base fp lr
    let saved := rawWriteBytes (rawWriteBytes initializedRaw frame.base (wordBytes fp))
      (frame.base + 8) (wordBytes lr)
    Embeds initializedSource memory sourceIds ∧ RawRepresents memory saved ∧
    memory.readBytes 1040 2 = some [0x5a, 0xc3] ∧
    rawReadWord saved frame.base = fp ∧ rawReadWord saved (frame.base + 8) = lr := by
  have image := placed_pair_raw_memory initialized_placed rfl initialized_represents fp lr
  have values := placed_pair_raw_readback initialized_placed rfl initialized_represents fp lr
  refine ⟨image.1, image.2.1, ?_, values.2.1, values.2.2⟩
  change ((initializedTarget.writeBytes 1024 (wordBytes fp)).writeBytes 1032 (wordBytes lr)).readBytes
    1040 2 = some [0x5a, 0xc3]
  rw [TrustIr.writeBytes_non_aliasing _ 1040 1032 2 (wordBytes lr)
    (Or.inr (by rw [wordBytes_length]; decide))]
  rw [TrustIr.writeBytes_non_aliasing _ 1040 1024 2 (wordBytes fp)
    (Or.inr (by rw [wordBytes_length]; decide))]
  rfl

example : ((BitVec.ofNat 64 1040) - (BitVec.ofNat 64 16)).toNat = 1024 :=
  pre_index_address placed rfl

example : ((BitVec.ofNat 64 1024) + (BitVec.ofNat 64 16)).toNat = 1040 :=
  post_index_sp placed rfl

example : (BitVec.ofNat 64 8 - BitVec.ofNat 64 16).toNat ≠ 1024 := by decide

example : TrustIr.decodeIntBytes (wordBytes (BitVec.ofNat 64 18446744073709551615)) =
    18446744073709551615 := wordBytes_decode _

/-- Wrong byte order changes the value; it is not an admitted codec. -/
example : TrustIr.decodeIntBytes (wordBytes (BitVec.ofNat 64 0x0123456789abcdef)).reverse ≠
    0x0123456789abcdef := by decide

private def saved : RawMemory :=
  rawWriteBytes (rawWriteBytes raw 1024 (wordBytes 0x0123456789abcdef))
    1032 (wordBytes 0xfedcba9876543210)

/-- A raw alias into saved LR cannot acquire the required callee frame rely. -/
example : ¬ KeepsFrame saved (rawStore saved (BitVec.ofNat 64 1032) 0xaa) 1024 := by
  intro keeps
  have bad := keeps 8 (by decide)
  change (0xaa : BitVec 8) = (0x10 : BitVec 8) at bad
  exact (by decide : (0xaa : BitVec 8) ≠ 0x10) bad

example : rawReadWord (rawStore saved (BitVec.ofNat 64 1032) 0xaa) 1032 ≠
    (0xfedcba9876543210 : Word) := by decide

end SemR.MemoryEmbedding.FramePair.Checks

#print axioms SemR.MemoryEmbedding.FramePair.wordBytes_extract
#print axioms SemR.MemoryEmbedding.FramePair.extracts_reconstruct
#print axioms SemR.MemoryEmbedding.FramePair.raw_represents_write
#print axioms SemR.MemoryEmbedding.FramePair.raw_reads_word
#print axioms SemR.MemoryEmbedding.FramePair.placed_pair_memory
#print axioms SemR.MemoryEmbedding.FramePair.placed_pair_raw_memory
#print axioms SemR.MemoryEmbedding.FramePair.placed_pair_raw_readback
#print axioms SemR.MemoryEmbedding.FramePair.kept_frame_read
#print axioms SemR.MemoryEmbedding.FramePair.Checks.initialized_pair
