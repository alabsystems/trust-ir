-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.BlockCheckCompleteness

namespace TrustIr.ByteImage.BlockCheckCompletenessControls

private def first (image : ByteImage) : Except String (Option Nat) :=
  if image.size == 0 then .ok none
  else match image.get 0 with | some _ => .ok none | none => .ok (some 0)
private def refuse (_ : ByteImage) : Except String (Option Nat) := .error "callback refused"
private def errorAfterHole (image : ByteImage) : Except String (Option Nat) :=
  if image.get 0 == some 255 then .error "later callback refused" else first image
private def cycle : ByteImage := (ByteImage.ofList [some 1,some 2]).tile 12
private def holeCycle : ByteImage := (ByteImage.ofList [some 1,some 2,none]).tile 4

private theorem filled_checked (count : Nat) : CheckedBlocks first (ByteImage.fill count (some 1)) 1 count := by
  intro slot inside image extent bytes
  have byte := bytes 0 (by decide)
  simp only [Nat.mul_one,Nat.add_zero,ByteImage.get_fill,if_pos inside] at byte
  simp only [first,extent,beq_iff_eq,Nat.one_ne_zero,ite_false,byte]

theorem logical_custody_drives_actual_check (count : Nat) :
    checkBlocks first (ByteImage.fill count (some 1)) 1 count = .ok none :=
  checkBlocks_none_of_checked first _ 1 count (by simp) (filled_checked count)

theorem bounded_subrange_keeps_callback_authority (count start length : Nat) (bounded : start + length ≤ count) :
    checkBlocks first ((ByteImage.fill count (some 1)).slice start length) 1 length = .ok none := by
  simpa only [Nat.mul_one] using checkBlocks_subrange_none first (ByteImage.fill count (some 1)) 1 count
    (by simp) (filled_checked count) start length bounded

theorem zero_count_does_not_call_a_refusing_callback :
    checkBlocks refuse (ByteImage.ofList [none,some 255]) 1 0 = .ok none := by trustIrReduce

theorem positive_count_zero_width_retains_callback_refusal :
    checkBlocks refuse ByteImage.empty 0 8 = .error "callback refused" := by trustIrReduce

theorem coprime_periodic_phases_are_checked :
    checkBlocks first cycle 3 8 = .ok none := by trustIrReduce

theorem late_hole_in_period_is_not_hidden_by_initialized_prefix :
    checkBlocks first holeCycle 1 12 = .ok (some 2) := by trustIrReduce

theorem later_error_keeps_precedence_over_earlier_hole :
    checkBlocks errorAfterHole (ByteImage.ofList [none,some 255]) 1 2 = .error "later callback refused" := by trustIrReduce

theorem invisible_retained_hole_is_not_a_visible_block :
    checkBlocks first ((ByteImage.ofList [some 1,none]).slice 0 1) 1 1 = .ok none := by trustIrReduce

theorem initialized_prefix_is_not_full_block_custody :
    ¬ CheckedBlocks first (ByteImage.ofList [some 1,none]) 1 2 := by
  intro checked
  have bad := checked 1 (by decide) (ByteImage.ofList [none]) rfl (by
    intro index inside
    have zero : index = 0 := by omega
    subst index
    rfl)
  cases bad

end TrustIr.ByteImage.BlockCheckCompletenessControls
