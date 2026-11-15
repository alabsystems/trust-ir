-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.FloatStorageProps
import TrustIr.Proofs.SourceReadbackPolicy

namespace TrustIr.FloatStorageControls
open AggregateMemory

-- Pure byte controls exercise the kernel codec, without native Float evaluation.
theorem little_endian_binary16 : natToBytesLE 2 4660 = [52,18] := rfl

theorem little_endian_binary32 : natToBytesLE 4 305419896 = [120,86,52,18] := rfl

theorem little_endian_binary64 : natToBytesLE 8 72623859790382856 = [8,7,6,5,4,3,2,1] := rfl

theorem low_bytes_only : natOfBytesLE (natToBytesLE 2 65537) = 1 := rfl

theorem full_binary16_residue : natOfBytesLE (natToBytesLE 2 65535) = 65535 := rfl

theorem empty_byte_residue (bits : Nat) : natOfBytesLE (natToBytesLE 0 bits) = 0 := rfl

theorem binary16_decode_truncated_refuses : decodeFloatAt .F16 [0] =
    .error (.typeError "F16 image is not 2 bytes") := rfl

theorem binary32_decode_oversized_refuses : decodeFloatAt .F32 [0,0,0,0,0] =
    .error (.typeError "F32 image is not 4 bytes") := rfl

theorem binary64_decode_truncated_refuses : decodeFloatAt .F64 [0,0,0,0] =
    .error (.typeError "F64 image is not 8 bytes") := rfl

theorem binary16_decode_bytes : decodeFloatAt .F16 [52,18] = .ok (decodeBits .binary16 4660) := rfl

theorem binary32_decode_bytes : decodeFloatAt .F32 [120,86,52,18] = .ok (decodeBits .binary32 305419896) := rfl

theorem binary64_decode_bytes : decodeFloatAt .F64 [8,7,6,5,4,3,2,1] =
    .ok (decodeBits .binary64 72623859790382856) := rfl

theorem nan_precedes_untyped_width (value : Float) (nan : value.isNaN = true) :
    encodeFloatAt .Unit value = .error
      (.unsupported .float "NaN byte image unobservable (no Float.toBits in Lean 4.8.0)") :=
  encodeFloatAt_nan_refuses .Unit value nan

theorem nan_precedes_layout_failure (model : ByteModel) (order : FunctionAddressOrder) (value : Float)
    (nan : value.isNaN = true) : encode model order (.leaf .F32 ⟨1,1⟩) (.float value) false =
    .error (.unsupported .float "NaN byte image unobservable (no Float.toBits in Lean 4.8.0)") :=
  encode_float_leaf_nan_refuses .binary32 model order ⟨1,1⟩ value nan

theorem ordinary_f64_layout_refuses (model : ByteModel) (order : FunctionAddressOrder) (value : Float)
    (bytes : List UInt8) (encoded : encodeFloatAt .F64 value = .ok bytes) :
    encode model order (.leaf .F64 ⟨4,4⟩) (.float value) false =
      .error (.typeError "memory image: leaf byte count mismatch") :=
  encode_float_leaf_wrong_extent .binary64 model order ⟨4,4⟩ value bytes encoded (by decide)

theorem ordinary_f16_image (model : ByteModel) (order : FunctionAddressOrder) (value : Float)
    (notNan : value.isNaN = false) (bits : Nat) (view : encodeBits .binary16 value = some bits) :
    encode model order (.leaf .F16 ⟨2,2⟩) (.float value) false =
      .ok { bytes := ByteImage.ofList ((natToBytesLE 2 bits).map some) } :=
  encode_float_leaf_success .binary16 model order ⟨2,2⟩ value (natToBytesLE 2 bits)
    ((FloatStorageFormat.binary16.encode_success_iff value _).mpr ⟨notNan,bits,view,rfl⟩) rfl

theorem ordinary_f32_image (model : ByteModel) (order : FunctionAddressOrder) (value : Float)
    (notNan : value.isNaN = false) (bits : Nat) (view : encodeBits .binary32 value = some bits) :
    encode model order (.leaf .F32 ⟨4,4⟩) (.float value) false =
      .ok { bytes := ByteImage.ofList ((natToBytesLE 4 bits).map some) } :=
  encode_float_leaf_success .binary32 model order ⟨4,4⟩ value (natToBytesLE 4 bits)
    ((FloatStorageFormat.binary32.encode_success_iff value _).mpr ⟨notNan,bits,view,rfl⟩) rfl

theorem ordinary_f64_image (model : ByteModel) (order : FunctionAddressOrder) (value : Float)
    (notNan : value.isNaN = false) (bits : Nat) (view : encodeBits .binary64 value = some bits) :
    encode model order (.leaf .F64 ⟨8,8⟩) (.float value) false =
      .ok { bytes := ByteImage.ofList ((natToBytesLE 8 bits).map some) } :=
  encode_float_leaf_success .binary64 model order ⟨8,8⟩ value (natToBytesLE 8 bits)
    ((FloatStorageFormat.binary64.encode_success_iff value _).mpr ⟨notNan,bits,view,rfl⟩) rfl

theorem successful_f32_store_supplies_byte_view (model : ByteModel) (order : FunctionAddressOrder)
    (layout : MemoryTypeLayout) (value : Float) (stored : Image)
    (encoded : encode model order (.leaf .F32 layout) (.float value) false = .ok stored) :
    ∃ bits, encodeBits .binary32 value = some bits ∧ layout.size = 4 ∧
      stored = { bytes := ByteImage.ofList ((natToBytesLE 4 bits).map some) } ∧
      decodeFloatAt .F32 (natToBytesLE 4 bits) = .ok (decodeBits .binary32 (bits % 256 ^ 4)) :=
  float_leaf_stored_byte_view .binary32 model order layout value stored encoded

theorem ordinary_f16_error_correspondence (model : ByteModel) (order : FunctionAddressOrder)
    (layout : MemoryTypeLayout) (value : Float) (error : SemError) :
    encode model order (.leaf .F16 layout) (.float value) false = .error error ↔
      encodeFloatAt .F16 value = .error error ∨
        ∃ bytes, encodeFloatAt .F16 value = .ok bytes ∧ bytes.length ≠ layout.size ∧
          error = .typeError "memory image: leaf byte count mismatch" :=
  encode_float_leaf_error_iff .binary16 model order layout value error

theorem numeric_readback_policy_not_promoted (source : SourceLayout.Environment) (ctx : EvalContext)
    (layout : MemoryTypeLayout) {ty : Ty} {format : BinaryFormat} {count : Nat}
    (storage : FloatStorageFormat ty format count) :
    sourceReadbackPolicy source ctx (.leaf ty layout) = false := by
  trustIrCompilerProof {
    cases storage <;> rw [sourceReadbackPolicy] <;> rfl
  } {
    cases storage <;> unfold sourceReadbackPolicy <;> rfl
  }

end TrustIr.FloatStorageControls
