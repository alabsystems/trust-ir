-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.ByteImageTraversalProps

namespace TrustIr.ByteImage

/-- The original logical checker succeeds when every logical block supplies
    callback authority for every byte-equivalent visible window. The actual
    periodic-window theorem discharges the lower traversal's geometry premise.
    This is not a refinement theorem for the native memoized implementation. -/
theorem checkBlocks_none_of_checked {ε : Type} (check : ByteImage → Except ε (Option Nat))
    (image : ByteImage) (width count : Nat) (extent : image.size = width * count)
    (checked : CheckedBlocks check image width count) :
    checkBlocks check image width count = .ok none :=
  checkBlocksSpec_none_of_checked_of_periods periodicWindow_sound check image width count extent checked

theorem checkBlocks_subrange_none {ε : Type} (check : ByteImage → Except ε (Option Nat))
    (image : ByteImage) (width count : Nat) (extent : image.size = width * count)
    (checked : CheckedBlocks check image width count) (start length : Nat) (bounded : start + length ≤ count) :
    checkBlocks check (image.slice (start * width) (length * width)) width length = .ok none := by
  have bound : start * width + length * width ≤ image.size := by
    rw [← Nat.add_mul,extent,Nat.mul_comm width count]
    exact Nat.mul_le_mul_right width bounded
  have room : length * width ≤ image.size - start * width :=
    Nat.le_sub_of_add_le (by simpa only [Nat.add_comm] using bound)
  apply checkBlocks_none_of_checked
  · rw [size_slice,Nat.min_eq_left room,Nat.mul_comm]
  · exact checked.subrange extent start length bounded

end TrustIr.ByteImage
