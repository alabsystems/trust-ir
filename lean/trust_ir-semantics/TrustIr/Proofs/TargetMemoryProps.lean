-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0

import TrustIr.Semantics.TargetMemory
import TrustIr.Proofs.MemoryProps
import TrustIr.Proofs.FunctionMemoryProps

namespace TrustIr

private theorem optionSomeBind {α β : Type} (value : α) (next : α → Option β) :
    (some value).bind next = next value := rfl

/-- Only the two exact little-endian word representations select a model. -/
theorem byteModel_representation_exact (bytes : Nat) (littleEndian : Bool) (model : ByteModel)
    (h : ByteModel.ofRepresentation bytes littleEndian = some model) :
    littleEndian = true ∧ bytes = model.pointerBytes := by
  cases model <;> unfold ByteModel.ofRepresentation at h <;>
    split at h <;> simp_all [ByteModel.pointerBytes]

theorem byteModel_bits_eq_bytes (model : ByteModel) :
    model.pointerBits = 8 * model.pointerBytes := rfl

theorem wasm32_pointer_representation :
    ByteModel.le32.pointerBytes = 4 ∧ ByteModel.le32.pointerBits = 32 ∧
    Ty.Ptr.byteSizeAtModel .le32 = some 4 ∧
    (Ty.FatPtr .Str).byteSizeAtModel .le32 = some 8 ∧
    FatPtrKind.Str.metadataTyAtModel .le32 = .U32 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem le64_pointer_representation :
    ByteModel.le64.pointerBytes = 8 ∧ ByteModel.le64.pointerBits = 64 ∧
    Ty.Ptr.byteSizeAtModel .le64 = some 8 ∧
    (Ty.FatPtr .Str).byteSizeAtModel .le64 = some 16 ∧
    FatPtrKind.Str.metadataTyAtModel .le64 = .U64 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem byteModel_limit_eq_bits (model : ByteModel) :
    model.addressLimit = 2 ^ model.pointerBits := by
  cases model <;> decide

theorem pointer_layout_at_model (model : ByteModel) :
    Ty.Ptr.bitWidthAtModel model = some model.pointerBits ∧
    Ty.Ptr.byteSizeAtModel model = some model.pointerBytes ∧
    Ty.Ptr.byteAlignAtModel model = some model.pointerBytes := by
  exact ⟨rfl, rfl, rfl⟩

theorem fat_pointer_layout_at_model (model : ByteModel) (kind : FatPtrKind) :
    (Ty.FatPtr kind).byteSizeAtModel model = some (2 * model.pointerBytes) ∧
    (Ty.FatPtr kind).byteAlignAtModel model = some model.pointerBytes := by
  exact ⟨rfl, rfl⟩

theorem pointer_integer_layout_at_model (model : ByteModel) :
    Ty.Isize.bitWidthAtModel model = some model.pointerBits ∧
    Ty.Usize.bitWidthAtModel model = some model.pointerBits ∧
    Ty.Isize.byteSizeAtModel model = some model.pointerBytes ∧
    Ty.Usize.byteSizeAtModel model = some model.pointerBytes := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The selectors actually used by memory accesses give pointer integers
    the target width and Char its fixed four-byte image at both models. -/
theorem scalar_leaf_layout_for (model : ByteModel) :
    Ty.Isize.byteSizeFor model = some model.pointerBytes ∧
    Ty.Usize.byteSizeFor model = some model.pointerBytes ∧
    Ty.Isize.byteAlignFor model = some model.pointerBytes ∧
    Ty.Usize.byteAlignFor model = some model.pointerBytes ∧
    Ty.Char.byteSizeFor model = some 4 ∧ Ty.Char.byteAlignFor model = some 4 := by
  cases model <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Successful Char decoding establishes Unicode validity at the typed
    memory boundary. This says nothing about other SSA Char producers. -/
theorem decodeCharImage_success (bytes : List UInt8) (value : Value)
    (h : decodeCharImage bytes = .ok value) :
    bytes.length = 4 ∧ validChar (decodeIntBytes bytes) ∧
    value = .int 32 (Int.ofNat (decodeIntBytes bytes)) := by
  unfold decodeCharImage at h
  split at h
  · rename_i hLength
    dsimp only at h
    split at h
    · rename_i hValid
      cases h
      exact ⟨by simpa using hLength, hValid, rfl⟩
    · cases h
  · cases h

/-- Both typed memory selectors refuse an initialized invalid Unicode image
    as UB, with no assumption about memory, provenance or later inspection. -/
theorem decodeMemoryAt_char_invalid (model : ByteModel) (mem : Memory)
    (bytes : List UInt8) (hLength : bytes.length = 4)
    (hInvalid : ¬ validChar (decodeIntBytes bytes)) :
    decodeMemoryAt model mem .Char bytes =
      .error (.ub "memory decode: invalid Unicode scalar value") := by
  cases model <;> simp [decodeMemoryAt, decodeValueAt, decodeImageAt,
    decodeTypedAtModel, decodeImageAtModel, decodeCharImage, hLength, hInvalid,
    bind, Except.bind]

theorem decodeMemoryAt_char_valid (model : ByteModel) (mem : Memory)
    (bytes : List UInt8) (hLength : bytes.length = 4)
    (hValid : validChar (decodeIntBytes bytes)) :
    decodeMemoryAt model mem .Char bytes =
      .ok (.int 32 (Int.ofNat (decodeIntBytes bytes))) := by
  cases model <;> simp [decodeMemoryAt, decodeValueAt, decodeImageAt,
    decodeTypedAtModel, decodeImageAtModel, decodeCharImage, hLength, hValid,
    Memory.resolveDecoded, bind, Except.bind, pure, Except.pure]

/-- A wrong-sized Char image is a typed codec error, not a padded/truncated
    scalar or an initialized invalid scalar's UB channel. -/
theorem decodeCharImage_wrong_length (bytes : List UInt8) (h : bytes.length ≠ 4) :
    decodeCharImage bytes =
      .error (.typeError "Char image must contain exactly four bytes") := by
  simp [decodeCharImage, h]

theorem vtable_metadata_is_never_a_length (model : ByteModel) (trait : UInt32) :
    FatPtrKind.ContainerVtable.metadataTyAtModel model = .Ptr ∧
    (FatPtrKind.TraitObject trait).metadataTyAtModel model = .Ptr := by
  exact ⟨rfl, rfl⟩

theorem length_metadata_has_target_width (model : ByteModel) (elem : TyId) :
    (FatPtrKind.Slice elem).metadataTyAtModel model = model.lengthTy ∧
    FatPtrKind.Str.metadataTyAtModel model = model.lengthTy ∧
    FatPtrKind.ContainerLen.metadataTyAtModel model = model.lengthTy := by
  exact ⟨rfl, rfl, rfl⟩

theorem encode_pointer_refuses_overflow (model : ByteModel) (address : Nat)
    (h : model.addressLimit ≤ address) : encodePointerWord model address = none := by
  simp [encodePointerWord, Nat.not_lt.mpr h]

theorem encode_pointer_length (model : ByteModel) (address : Nat) (bytes : List UInt8)
    (h : encodePointerWord model address = some bytes) : bytes.length = model.pointerBytes := by
  unfold encodePointerWord at h
  split at h
  · cases h
    exact encodeIntBytes_length _ _
  · contradiction

/-- The address round trip is symbolic in both the address and word size.
    It is a kernel proof, not a native evaluation of selected addresses. -/
theorem decode_encode_model_address (model : ByteModel) (address : Nat)
    (h : address < model.addressLimit) :
    decodeIntBytes (encodeIntBytes (Int.ofNat address) model.pointerBytes) = address := by
  exact decode_encode_function_address model address h

theorem pointer_word_round_trip (model : ByteModel) (address : Nat)
    (h : address < model.addressLimit) :
    (encodePointerWord model address).bind (decodePointerWord model) = some address := by
  simp only [encodePointerWord, h, ↓reduceIte, optionSomeBind, decodePointerWord,
    encodeIntBytes_length, beq_self_eq_true]
  rw [decode_encode_model_address model address h]

theorem pointer_word_rejects_wrong_length (model : ByteModel) (bytes : List UInt8)
    (h : bytes.length ≠ model.pointerBytes) : decodePointerWord model bytes = none := by
  simp [decodePointerWord, h]

theorem null_pointer_image_at_model (model : ByteModel) :
    decodeValueAtModel model .Ptr (List.replicate model.pointerBytes 0) = some .nullPtr := by
  cases model <;> trustIrReduce

theorem wasm32_rejects_eight_byte_pointer_image (byte : UInt8) :
    decodePointerWord .le32 (List.replicate 8 byte) = none := rfl

theorem le64_rejects_four_byte_pointer_image (byte : UInt8) :
    decodePointerWord .le64 (List.replicate 4 byte) = none := rfl

theorem pointer_image_round_trip (model : ByteModel) (address : Nat) (prov : Option AllocId)
    (h : address < model.addressLimit) :
    (encodeValueAtModel model (.ptr address prov)).bind (decodeValueAtModel model .Ptr) =
      some (if address == 0 then .nullPtr else .ptr address none) := by
  simp only [encodeValueAtModel, encodePointerWord, h, ↓reduceIte, decodeValueAtModel,
    decodePointerWord, encodeIntBytes_length, beq_self_eq_true, optionSomeBind]
  rw [decode_encode_model_address model address h]
  rfl

theorem encode_wrong_length_metadata_refuses (model : ByteModel) (width : Nat) (value : Int)
    (h : width ≠ model.pointerBits) : encodeMetadataWord model (.int width value) = none := by
  simp [encodeMetadataWord, h]

theorem wasm32_rejects_64_bit_length_metadata (value : Int) :
    encodeMetadataWord .le32 (.int 64 value) = none := by
  simp [encodeMetadataWord, ByteModel.pointerBits, ByteModel.pointerBytes]

theorem le64_rejects_32_bit_length_metadata (value : Int) :
    encodeMetadataWord .le64 (.int 32 value) = none := by
  simp [encodeMetadataWord, ByteModel.pointerBits, ByteModel.pointerBytes]

theorem encode_length_word_of_residue (model : ByteModel) (length : Nat)
    (h : length < model.addressLimit) :
    encodeMetadataWord model (.int model.pointerBits (Int.ofNat length)) =
      some (encodeIntBytes (Int.ofNat length) model.pointerBytes) := by
  have hlt : (length : Int) < (2 : Int) ^ model.pointerBits := by
    have hnat : length < 2 ^ model.pointerBits := by
      rwa [← byteModel_limit_eq_bits]
    simpa only [Int.natCast_pow] using Int.ofNat_lt.mpr hnat
  have hmod : (length : Int) % (2 : Int) ^ model.pointerBits = length :=
    Int.emod_eq_of_lt (Int.ofNat_zero_le _) hlt
  simp [encodeMetadataWord, Int.add_emod, hmod]

private theorem take_first_word (first second : List UInt8) :
    (first ++ second).take first.length = first := by
  induction first with
  | nil => rfl
  | cons _ first ih => simp [List.take, ih]

private theorem drop_first_word (first second : List UInt8) :
    (first ++ second).drop first.length = second := by
  induction first with
  | nil => rfl
  | cons _ first ih => simp [List.drop, ih]

/-- Both fat-pointer words decode at the selected width, with the kind
    deciding whether metadata is a length or a vtable pointer. -/
theorem decode_model_fat_pointer_words (model : ByteModel) (kind : FatPtrKind)
    (data metadata : Nat) (hd : data < model.addressLimit) (hm : metadata < model.addressLimit) :
    decodeValueAtModel model (.FatPtr kind)
      (encodeIntBytes (Int.ofNat data) model.pointerBytes ++
        encodeIntBytes (Int.ofNat metadata) model.pointerBytes) =
      some (match kind with
        | .Slice _ | .Str | .ContainerLen =>
          .fatPtr data none (.int model.pointerBits (Int.ofNat metadata))
        | .TraitObject _ | .ContainerVtable =>
          .fatPtr data none (if metadata == 0 then .nullPtr else .ptr metadata none)) := by
  have htake := take_first_word (encodeIntBytes (Int.ofNat data) model.pointerBytes)
    (encodeIntBytes (Int.ofNat metadata) model.pointerBytes)
  have hdrop := drop_first_word (encodeIntBytes (Int.ofNat data) model.pointerBytes)
    (encodeIntBytes (Int.ofNat metadata) model.pointerBytes)
  rw [encodeIntBytes_length] at htake hdrop
  have hsum : model.pointerBytes + model.pointerBytes = 2 * model.pointerBytes := by omega
  simp only [decodeValueAtModel, List.length_append, encodeIntBytes_length, hsum,
    beq_self_eq_true, ↓reduceIte, htake, hdrop,
    decode_encode_model_address model data hd, decode_encode_model_address model metadata hm]
  cases kind <;> rfl

theorem model_str_fat_pointer_round_trip (model : ByteModel) (data length : Nat)
    (prov : Option AllocId) (hd : data < model.addressLimit) (hl : length < model.addressLimit) :
    (encodeValueAtModel model (.fatPtr data prov (.int model.pointerBits (Int.ofNat length)))).bind
      (decodeValueAtModel model (.FatPtr .Str)) =
      some (.fatPtr data none (.int model.pointerBits (Int.ofNat length))) := by
  simp only [encodeValueAtModel, encodePointerWord, hd, ↓reduceIte,
    encode_length_word_of_residue model length hl, optionSomeBind, pure]
  exact decode_model_fat_pointer_words model .Str data length hd hl

theorem model_vtable_fat_pointer_round_trip (model : ByteModel) (data vtable : Nat)
    (prov metaProv : Option AllocId) (hd : data < model.addressLimit)
    (hv : vtable < model.addressLimit) :
    (encodeValueAtModel model (.fatPtr data prov (.ptr vtable metaProv))).bind
      (decodeValueAtModel model (.FatPtr .ContainerVtable)) =
      some (.fatPtr data none (if vtable == 0 then .nullPtr else .ptr vtable none)) := by
  simp only [encodeValueAtModel, encodeMetadataWord, encodePointerWord, hd, hv, ↓reduceIte,
    optionSomeBind, pure]
  exact decode_model_fat_pointer_words model .ContainerVtable data vtable hd hv

/-- The byte image is target-sized and loading it recovers provenance by the
    same address rule at either width. No stored provenance can be laundered. -/
theorem model_pointer_store_load_recovers_inside (model : ByteModel) (mem : Memory)
    (slot address : Addr) (prov : Option AllocId) (alloc : Allocation)
    (hWF : mem.layoutWF) (hMem : alloc ∈ mem.allocations)
    (hBase : alloc.base ≤ address) (hIn : address < alloc.base + alloc.size)
    (hNZ : address ≠ 0) (hLt : address < model.addressLimit) :
    ∃ image,
      encodeTypedAtModel model .Ptr (.ptr address prov) = .ok image ∧
      (mem.writeBytes slot image).readBytes slot model.pointerBytes = some image ∧
      decodeTypedAtModel model (mem.writeBytes slot image) .Ptr image =
        .ok (.ptr address (some alloc.id)) := by
  refine ⟨encodeIntBytes (Int.ofNat address) model.pointerBytes, ?_, ?_, ?_⟩
  · simp [encodeTypedAtModel, fatPtrStoreValueValidAtModel, encodeValueAtModel,
      encodePointerWord, hLt]
  · have h := writeBytes_readBytes_general mem slot
      (encodeIntBytes (Int.ofNat address) model.pointerBytes)
    rwa [encodeIntBytes_length] at h
  · have hProv :
        (mem.writeBytes slot (encodeIntBytes (Int.ofNat address) model.pointerBytes)).provenanceAt
          address = some alloc.id := provenanceAt_inside mem alloc address hWF hMem hBase hIn
    have hDec := pointer_image_round_trip model address prov hLt
    simp only [encodeValueAtModel, encodePointerWord, hLt, ↓reduceIte, optionSomeBind] at hDec
    have hZ : (address == 0) = false := by simpa using hNZ
    rw [hZ] at hDec
    simp only [Bool.false_eq_true, ↓reduceIte] at hDec
    simp only [decodeTypedAtModel, decodeImageAtModel, Ty.isFloat, Bool.false_eq_true,
      ↓reduceIte, hDec]
    change Except.ok
      ((mem.writeBytes slot (encodeIntBytes (Int.ofNat address) model.pointerBytes)).resolveDecoded
        (.ptr address none)) = _
    simp only [Memory.resolveDecoded, Memory.resolveAddr, hZ, Bool.false_eq_true, ↓reduceIte, hProv]

end TrustIr
