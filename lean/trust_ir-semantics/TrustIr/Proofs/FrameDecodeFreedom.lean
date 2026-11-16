-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameResultValidity
import TrustIr.Semantics.AggregateDecoding

/-! Pure byte decoding is independent of frame instruction/body preservation.
The original public exit laws live here so contextual casts can use them before
the body-validity and recursive-exit clients. -/

namespace TrustIr.FrameLifetime

/-- Pure validation results may refuse, but cannot invent a runtime throw world. -/
def ExceptNoUnwind {α : Type} (result : Except SemError α) : Prop :=
  ∀ exception after, result ≠ .error (.unwinding exception after)


/-- A pure decoder's actual successful payload and absence of fabricated
runtime unwind states. Ordinary refusals retain their original meaning. -/
def DecodeFrameExit {α : Type} (post : α → Prop) : Except SemError α → Prop
  | .ok value => post value
  | .error (.unwinding _ _) => False
  | .error _ => True

theorem DecodeFrameExit.bind {α β : Type} (post : α → Prop) (nextPost : β → Prop)
    (action : Except SemError α) (next : α → Except SemError β)
    (first : DecodeFrameExit post action)
    (rest : ∀ value, post value → DecodeFrameExit nextPost (next value)) :
    DecodeFrameExit nextPost (action >>= next) := by
  cases action with
  | ok value => exact rest value first
  | error error => cases error <;> exact first

theorem DecodeFrameExit.of_no_unwind {α : Type} (post : α → Prop) (result : Except SemError α)
    (safe : ExceptNoUnwind result) (success : ∀ value, result = .ok value → post value) :
    DecodeFrameExit post result := by
  cases result with
  | ok value => exact success value rfl
  | error error => cases error <;> first | exact True.intro | exact False.elim (safe _ _ rfl)

theorem DecodeFrameExit.no_unwind {α : Type} (post : α → Prop) (result : Except SemError α)
    (valid : DecodeFrameExit post result) : ExceptNoUnwind result := by
  intro exception after same
  rw [same] at valid
  exact valid

private theorem value_leaf (value : Value) (shape : ValueIdentityShape 0 value) : MintedValue 0 value :=
  (mintedValue_iff_shape 0 value).2 shape

local macro "minted_leaf" : tactic => `(tactic|
  trustIrCompilerProof {
    simp [mintedValue_iff_shape,ValueIdentityShape]
  } {
    repeat' (rw [mintedValue_iff_shape]; simp only [ValueIdentityShape])
  })

/-- Width-free scalar byte decoding creates no frame at any depth. -/
theorem decode_value_minted (ty : Ty) (bytes : List UInt8) (value : Value)
    (decoded : decodeValue ty bytes = some value) : MintedValue 0 value := by
  cases ty <;> simp only [decodeValue] at decoded
  all_goals repeat' first
    | (solve | cases decoded)
    | (solve | cases decoded; minted_leaf)
    | split at decoded
    | (dsimp only at decoded; split at decoded)
    | (solve | cases decoded; exact value_leaf _ (fun _ member => by cases member))

/-- Target-width pointer/metadata decoding also creates no frame identity. -/
theorem decode_value_model_minted (model : ByteModel) (ty : Ty) (bytes : List UInt8) (value : Value)
    (decoded : decodeValueAtModel model ty bytes = some value) : MintedValue 0 value := by
  cases ty <;> simp only [decodeValueAtModel,decodePointerWord,bind,pure,Option.bind] at decoded
  all_goals repeat' first
    | exact decode_value_minted _ _ _ decoded
    | (solve | cases decoded)
    | (solve | cases decoded; minted_leaf)
    | split at decoded
    | (dsimp only at decoded; split at decoded)

private theorem ok_exit {α : Type} (post : α → Prop) (value : α) (valid : post value) :
    DecodeFrameExit post (.ok value) := valid
private theorem type_exit {α : Type} (post : α → Prop) (message : String) :
    DecodeFrameExit post (.error (.typeError message) : Except SemError α) := True.intro
private theorem ub_exit {α : Type} (post : α → Prop) (message : String) :
    DecodeFrameExit post (.error (.ub message) : Except SemError α) := True.intro
private theorem unsupported_exit {α : Type} (post : α → Prop) (feature : UnsupportedFeature) (message : String) :
    DecodeFrameExit post (.error (.unsupported feature message) : Except SemError α) := True.intro

local macro "decode_leaves" : tactic => `(tactic|
  repeat' first
    | (solve | apply ok_exit; minted_leaf)
    | exact type_exit _ _
    | exact ub_exit _ _
    | exact unsupported_exit _ _ _
    | split
    | (dsimp only; split))

theorem decode_float_no_unwind (ty : Ty) (bytes : List UInt8) : ExceptNoUnwind (decodeFloatAt ty bytes) := by
  cases ty <;> unfold decodeFloatAt
  all_goals intro exception after run
  all_goals repeat' first | (solve | cases run) | split at run

theorem decode_char_frame_exit (bytes : List UInt8) : DecodeFrameExit (MintedValue 0) (decodeCharImage bytes) := by
  unfold decodeCharImage
  decode_leaves

theorem decode_vector_lane_frame_exit (ty : Ty) (bytes : List UInt8) :
    DecodeFrameExit (MintedValue 0) (decodeVectorLane ty bytes) := by
  unfold decodeVectorLane
  cases vectorScalarByteSize ty with
  | none => exact True.intro
  | some width =>
    simp only
    split
    · exact True.intro
    · split
      · apply DecodeFrameExit.bind (fun _ => True) (MintedValue 0)
        · exact DecodeFrameExit.of_no_unwind _ _ (decode_float_no_unwind ty bytes) (fun _ _ => True.intro)
        · intro value _; apply ok_exit; minted_leaf
      · cases decoded : decodeValue ty bytes with
        | none => exact True.intro
        | some value => exact decode_value_minted ty bytes value decoded

theorem decode_vector_lanes_frame_exit (ty : Ty) (width count : Nat) (bytes : List UInt8) :
    DecodeFrameExit (MintedArgs 0) (decodeVectorLanes ty width count bytes) := by
  induction count generalizing bytes with
  | zero => cases bytes <;> first | exact True.intro | exact (fun _ member => by cases member)
  | succ count ih =>
    apply DecodeFrameExit.bind (MintedValue 0) (MintedArgs 0) _ _ (decode_vector_lane_frame_exit ty _)
    intro value valid
    apply DecodeFrameExit.bind (MintedArgs 0) (MintedArgs 0) _ _ (ih _)
    intro rest minted
    apply ok_exit
    intro child member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact valid
    · exact minted child member

theorem decode_scalar_vector_frame_exit (count : Nat) (ty : Ty) (bytes : List UInt8) :
    DecodeFrameExit (MintedValue 0) (decodeScalarVectorAt count ty bytes) := by
  by_cases zero : count = 0
  · simp [decodeScalarVectorAt,zero,DecodeFrameExit,bind,Except.bind,throw,throwThe,MonadExceptOf.throw]
  · simp only [decodeScalarVectorAt,beq_iff_eq,zero,↓reduceIte,pure_bind]
    cases vectorScalarByteSize ty with
    | none => exact True.intro
    | some width =>
      simp only [pure_bind]
      by_cases length : (bytes.length != count * width) = true
      · simp [length,bind,Except.bind,DecodeFrameExit]
      · simp only [length,↓reduceIte,pure_bind]
        apply DecodeFrameExit.bind (MintedArgs 0) (MintedValue 0) _ _ (decode_vector_lanes_frame_exit ty width count bytes)
        intro values valid
        apply ok_exit
        exact (mintedValue_iff_shape 0 _).2 valid

theorem decode_image_frame_exit (ty : Ty) (bytes : List UInt8) :
    DecodeFrameExit (MintedValue 0) (decodeImageAt ty bytes) := by
  cases ty <;> simp only [decodeImageAt]
  all_goals first
    | exact decode_char_frame_exit bytes
    | exact decode_scalar_vector_frame_exit _ _ bytes
    | (split
       · split
         · apply ok_exit; minted_leaf
         · rename_i error decoded
           cases error <;> first
             | exact True.intro
             | exact False.elim (decode_float_no_unwind _ bytes _ _ decoded)
       · cases decoded : decodeValue _ bytes with
         | none => exact True.intro
         | some value => exact decode_value_minted _ bytes value decoded)

theorem decode_image_model_frame_exit (model : ByteModel) (ty : Ty) (bytes : List UInt8) :
    DecodeFrameExit (MintedValue 0) (decodeImageAtModel model ty bytes) := by
  cases ty <;> simp only [decodeImageAtModel]
  all_goals first
    | exact decode_char_frame_exit bytes
    | exact decode_scalar_vector_frame_exit _ _ bytes
    | (split
       · split
         · apply ok_exit; minted_leaf
         · rename_i error decoded
           cases error <;> first
             | exact True.intro
             | exact False.elim (decode_float_no_unwind _ bytes _ _ decoded)
       · cases decoded : decodeValueAtModel model _ bytes with
         | none => exact True.intro
         | some value => exact decode_value_model_minted model _ bytes value decoded)

/-- Provenance recovery changes only pointer words, never frame identities. -/
theorem resolve_decoded_minted (memory : Memory) (bound : Nat) (value : Value)
    (valid : MintedValue bound value) : MintedValue bound (memory.resolveDecoded value) := by
  have pointer (address : Nat) : MintedValue bound (memory.resolveAddr address) := by
    unfold Memory.resolveAddr
    split <;> simp [mintedValue_iff_shape,ValueIdentityShape]
  cases value
  case ptr address provenance => exact pointer address
  case fatPtr address provenance metadata =>
    have child : MintedValue bound metadata := (mintedValue_iff_shape bound _).1 valid
    cases metadata <;> first
      | exact (mintedValue_iff_shape bound _).2 (pointer _)
      | exact (mintedValue_iff_shape bound _).2 child
  all_goals exact valid

theorem decode_value_at_frame_exit (memory : Memory) (ty : Ty) (bytes : List UInt8) :
    DecodeFrameExit (MintedValue 0) (decodeValueAt memory ty bytes) := by
  have valid := decode_image_frame_exit ty bytes
  unfold decodeValueAt
  cases decoded : decodeImageAt ty bytes with
  | ok value =>
    rw [decoded] at valid
    exact resolve_decoded_minted memory 0 value valid
  | error error =>
    rw [decoded] at valid
    cases error <;> exact valid

theorem decode_typed_model_frame_exit (model : ByteModel) (memory : Memory) (ty : Ty) (bytes : List UInt8) :
    DecodeFrameExit (MintedValue 0) (decodeTypedAtModel model memory ty bytes) := by
  apply DecodeFrameExit.bind (MintedValue 0) (MintedValue 0) _ _ (decode_image_model_frame_exit model ty bytes)
  intro value valid
  exact resolve_decoded_minted memory 0 value valid

theorem decode_memory_frame_exit (model : ByteModel) (memory : Memory) (ty : Ty) (bytes : List UInt8) :
    DecodeFrameExit (MintedValue 0) (decodeMemoryAt model memory ty bytes) := by
  cases model with
  | le64 => exact decode_value_at_frame_exit memory ty bytes
  | le32 => exact decode_typed_model_frame_exit _ memory ty bytes

theorem function_target_no_unwind (model : ByteModel) (order : FunctionAddressOrder) (address : Nat) :
    ExceptNoUnwind (functionTargetAt model order address) := by
  have valid : DecodeFrameExit (fun _ => True) (functionTargetAt model order address) := by
    unfold functionTargetAt
    repeat' first
      | (solve | apply ok_exit; trivial)
      | exact type_exit _ _
      | exact unsupported_exit _ _ _
      | (refine DecodeFrameExit.bind (fun _ => True) (fun _ => True) _ _ ?_ (fun _ _ => ?_) <;> dsimp only)
      | split
  exact valid.no_unwind _ _

/-- The contextual source function table decodes code identities, never
frame identities; unknown code words keep their original refusals. -/
theorem decode_functions_frame_exit (model : ByteModel) (order : FunctionAddressOrder)
    (memory : Memory) (ty : Ty) (bytes : List UInt8) :
    DecodeFrameExit (MintedValue 0) (decodeMemoryWithFunctions model order memory ty bytes) := by
  cases ty <;> simp only [decodeMemoryWithFunctions]
  all_goals first
    | exact True.intro
    | exact decode_memory_frame_exit model memory _ bytes
    | (split
       · split
         · apply ok_exit; minted_leaf
         · apply DecodeFrameExit.bind (fun _ => True) (MintedValue 0)
           · exact DecodeFrameExit.of_no_unwind _ _ (function_target_no_unwind model order _) (fun _ _ => True.intro)
           · intro target _; apply ok_exit; minted_leaf
       · exact True.intro)


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


private theorem frame_decode_rules : AggregateMemory.DecodeRules (MintedValue 0) BlockDecodeError where
  typeErrors := fun _ => True.intro
  undefined := fun _ => True.intro
  scalar := fun model order memory ty bytes =>
    (block_result_frame_iff _ _).2 (decode_functions_frame_exit model order memory ty bytes)
  integer := fun _ _ => (mintedValue_iff_shape 0 _).2 True.intro
  uninit := (mintedValue_iff_shape 0 _).2 True.intro
  aggregate := fun _ held => (mintedValue_iff_shape 0 _).2 held
  array := fun _ held => (mintedValue_iff_shape 0 _).2 held
  fnItem := fun target => mintedValue_fnItem 0 target

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
