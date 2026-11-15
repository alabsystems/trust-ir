-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameMemoryDecodeExits

namespace TrustIr.FrameLifetime

/-- Pure callback errors may refuse but cannot supply an arbitrary throw world. -/
def BlockDecodeError : SemError → Prop
  | .unwinding _ _ => False
  | _ => True

theorem block_result_frame_iff {α : Type} (post : α → Prop) (result : Except SemError α) :
    ByteImage.BlockResult post BlockDecodeError result ↔ DecodeFrameExit post result := by
  cases result with
  | ok value => rfl
  | error error => cases error <;> rfl

/-- Full original compact-array mapping, including its private periodic cache.
The callback contract is explicit for every actual byte image; successful
output lookups inherit the bound and actual errors cannot invent unwind states. -/
theorem map_blocks_frame_exit (bound : Nat) (decode : ByteImage → Except SemError Value)
    (callbacks : ∀ image, DecodeFrameExit (MintedValue bound) (decode image))
    (image : ByteImage) (width count : Nat) :
    DecodeFrameExit (ByteImage.BlockTreeValid (MintedValue bound)) (image.mapBlocks decode width count) := by
  apply (block_result_frame_iff _ _).1
  exact ByteImage.mapBlocks_valid (MintedValue bound) BlockDecodeError decode
    (fun input => (block_result_frame_iff _ _).2 (callbacks input)) image width count

/-- Publishing the computed compact tree as an actual array value preserves
recursive identities at all logical indices, without expanding the array. -/
theorem mapped_array_frame_exit (bound : Nat) (decode : ByteImage → Except SemError Value)
    (callbacks : ∀ image, DecodeFrameExit (MintedValue bound) (decode image))
    (image : ByteImage) (width count : Nat) :
    DecodeFrameExit (MintedValue bound) (do
      let tree ← image.mapBlocks decode width count
      pure (.array ⟨count,tree⟩)) := by
  apply DecodeFrameExit.bind (ByteImage.BlockTreeValid (MintedValue bound)) (MintedValue bound)
    _ _ (map_blocks_frame_exit bound decode callbacks image width count)
  intro tree valid
  apply (mintedValue_iff_shape bound _).2
  intro index value found
  exact valid index value found

end TrustIr.FrameLifetime
