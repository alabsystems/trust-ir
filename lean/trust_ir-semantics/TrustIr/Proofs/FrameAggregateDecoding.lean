-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameBlockDecoding

namespace TrustIr.FrameLifetime

private theorem frame_decode_rules : AggregateMemory.DecodeRules (MintedValue 0) BlockDecodeError where
  typeErrors := fun _ => True.intro
  undefined := fun _ => True.intro
  scalar := fun model order memory ty bytes =>
    (block_result_frame_iff _ _).2 (decode_functions_frame_exit model order memory ty bytes)
  integer := fun _ _ => (mintedValue_iff_shape 0 _).2 True.intro
  uninit := (mintedValue_iff_shape 0 _).2 True.intro
  aggregate := fun _ held => (mintedValue_iff_shape 0 _).2 held
  array := fun _ held => (mintedValue_iff_shape 0 _).2 held

/-- Original covered-byte traversal across arbitrary plans cannot fabricate
an embedded runtime throw state; malformed layouts and tags retain refusals. -/
theorem aggregate_covered_no_unwind (plan : AggregateMemory.Plan) (image : ByteImage) :
    ExceptNoUnwind (AggregateMemory.covered plan image) := by
  have held := AggregateMemory.covered_errors BlockDecodeError (fun _ => True.intro) (fun _ => True.intro) plan image
  exact DecodeFrameExit.no_unwind (fun _ => True) _ ((block_result_frame_iff _ _).1 held)

/-- Strict producer-plan decoding creates no frame identity at any nested
logical index, and actual pure decoder errors never supply a throw world. -/
theorem aggregate_decode_frame_exit (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (plan : AggregateMemory.Plan) (image : ByteImage) :
    DecodeFrameExit (MintedValue 0) (AggregateMemory.decode model order memory plan image) :=
  (block_result_frame_iff _ _).1
    (AggregateMemory.decode_valid (MintedValue 0) BlockDecodeError frame_decode_rules model order memory plan image)

/-- The original explained-unwritten field decoder has the same full exit
law, including nested Uninit reconstruction and original partial-lane errors. -/
theorem aggregate_unwritten_decode_frame_exit (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (plan : AggregateMemory.Plan) (image : ByteImage) :
    DecodeFrameExit (MintedValue 0) (AggregateMemory.decodeUnwritten model order memory plan image) :=
  (block_result_frame_iff _ _).1
    (AggregateMemory.decodeUnwritten_valid (MintedValue 0) BlockDecodeError frame_decode_rules model order memory plan image)

end TrustIr.FrameLifetime
