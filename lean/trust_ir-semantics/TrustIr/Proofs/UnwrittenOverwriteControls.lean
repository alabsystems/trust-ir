-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.UnwrittenOverwrite

namespace TrustIr.UnwrittenOverwriteControls

private def recorded : Memory := Memory.empty.recordUnwritten ⟨7⟩ 100 [(0,8)]
private def middle : ByteImage := ByteImage.fill 3 none

/-- Absent copied bytes still overwrite and clear previous source-lane facts. -/
theorem absent_copy_clears_old_lane :
    (recorded.writeImage 102 middle).isUnwritten ⟨7⟩ 103 = false := rfl

theorem middle_write_preserves_both_sides :
    ((recorded.writeImage 102 middle).isUnwritten ⟨7⟩ 101,
     (recorded.writeImage 102 middle).isUnwritten ⟨7⟩ 105) = (true,true) := rfl

theorem half_open_endpoints_are_exact :
    ((recorded.writeImage 102 middle).isUnwritten ⟨7⟩ 102,
     (recorded.writeImage 102 middle).isUnwritten ⟨7⟩ 104,
     (recorded.writeImage 102 middle).isUnwritten ⟨7⟩ 105) = (false,false,true) := rfl

theorem complete_overwrite_clears_every_covered_address (query : Nat) (low : 100 ≤ query) (high : query < 108) :
    (recorded.writeImage 100 (ByteImage.fill 8 none)).isUnwritten ⟨7⟩ query = false :=
  recorded.writeImage_unwritten_inside ⟨7⟩ query 100 (ByteImage.fill 8 none) low high

theorem zero_length_write_preserves_lane :
    (recorded.writeImage 103 ByteImage.empty).isUnwritten ⟨7⟩ 103 = true := rfl

theorem adjacent_write_does_not_clip :
    ((recorded.writeImage 108 (ByteImage.fill 1 (some 9))).isUnwritten ⟨7⟩ 107,
     (recorded.writeImage 99 (ByteImage.fill 1 (some 9))).isUnwritten ⟨7⟩ 100) = (true,true) := rfl

theorem write_cannot_create_an_unwritten_claim :
    (recorded.writeImage 200 (ByteImage.fill 8 none)).isUnwritten ⟨7⟩ 200 = false := rfl

theorem distinct_allocation_does_not_gain_coverage :
    (recorded.writeImage 102 middle).isUnwritten ⟨8⟩ 101 = false := rfl

private def overlapping : Memory :=
  Memory.empty.recordUnwritten ⟨7⟩ 100 [(0,8),(2,4),(0,8)]

theorem duplicate_overlapping_records_are_all_clipped :
    (overlapping.writeImage 102 middle).isUnwritten ⟨7⟩ 103 = false := rfl

theorem list_transport_has_same_clipping :
    (recorded.writeBytesMaybeUninit 102 [none,none,none]).isUnwritten ⟨7⟩ 103 = false := rfl

theorem initialized_list_write_has_same_clipping :
    (recorded.writeBytes 102 [1,2,3]).isUnwritten ⟨7⟩ 103 = false := rfl

private def malformed : Memory :=
  { Memory.empty with unwritten := [{ allocation := ⟨7⟩,start := 108,stop := 100 }] }

theorem malformed_old_record_cannot_create_coverage (query : Nat) :
    (malformed.writeImage 102 middle).isUnwritten ⟨7⟩ query = false := by
  apply malformed.writeImage_no_new_unwritten ⟨7⟩ query 102 middle
  simp [Memory.isUnwritten,malformed]
  intro low
  exact Nat.le_trans (by decide : 100 ≤ 108) low

private def byte : AggregateMemory.Plan := .leaf .U8 ⟨1,1⟩
private def stored : AggregateMemory.Image :=
  match AggregateMemory.encode .le64 none byte (.int 8 9) false with
  | .ok image => image
  | .error _ => { bytes := ByteImage.empty }

theorem actual_ordinary_publication_clears_old_record :
    (((recorded.writeImage 103 stored.bytes).recordUnwritten ⟨7⟩ 103 stored.unwritten).isUnwritten ⟨7⟩ 103,
     ((recorded.writeImage 103 stored.bytes).recordUnwritten ⟨7⟩ 103 stored.unwritten).isUnwritten ⟨7⟩ 104) =
      (false,true) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem source_publication_law_uses_actual_extent (memory : Memory) (query : Nat) :
    ((memory.writeImage 103 stored.bytes).recordUnwritten ⟨7⟩ 103 stored.unwritten).isUnwritten ⟨7⟩ query =
      (memory.isUnwritten ⟨7⟩ query && !(103 ≤ query && query < 104)) := by
  trustIrCompilerProof {
    exact AggregateMemory.encode_ordinary_publication_coverage .le64 none byte (.int 8 9) stored rfl memory ⟨7⟩ ⟨7⟩ 103 query
  } {
    exact AggregateMemory.encode_ordinary_publication_coverage .le64 none byte (.int 8 9) stored (by trustIrReduce) memory ⟨7⟩ ⟨7⟩ 103 query
  }

end TrustIr.UnwrittenOverwriteControls
