-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.ByteMemory
import TrustIr.Semantics.AggregateImages

namespace TrustIr

/-- The three actual typed floating-point storage formats. -/
inductive FloatStorageFormat : Ty → BinaryFormat → Nat → Prop where
  | binary16 : FloatStorageFormat .F16 .binary16 2
  | binary32 : FloatStorageFormat .F32 .binary32 4
  | binary64 : FloatStorageFormat .F64 .binary64 8

/-- The float and integer codecs use the same little-endian byte constructor. -/
theorem natToBytesLE_eq_integer_go (count bits : Nat) :
    natToBytesLE count bits = encodeIntBytes.go count bits := by
  induction count generalizing bits with
  | zero => rfl
  | succ count ih => simp only [natToBytesLE, encodeIntBytes.go, ih]

theorem natToBytesLE_length (count bits : Nat) : (natToBytesLE count bits).length = count := by
  rw [natToBytesLE_eq_integer_go]
  exact encodeIntBytes_length (Int.ofNat bits) count

/-- Reading a byte list at offset zero is the float codec's natural byte value. -/
theorem natOfBytesLE_eq_integer_go (bytes : List UInt8) (shift : Nat) :
    decodeIntBytes.go bytes shift = 256 ^ shift * natOfBytesLE bytes := by
  induction bytes generalizing shift with
  | nil => simp [decodeIntBytes.go, natOfBytesLE]
  | cons first rest ih =>
    simp only [decodeIntBytes.go, natOfBytesLE, ih, Nat.pow_succ]
    rw [Nat.mul_add]
    ac_rfl

/-- Exact byte residue, with no native Float equality or evaluation premise. -/
theorem natOfBytesLE_natToBytesLE (count bits : Nat) :
    natOfBytesLE (natToBytesLE count bits) = bits % 256 ^ count := by
  have same := natOfBytesLE_eq_integer_go (natToBytesLE count bits) 0
  rw [natToBytesLE_eq_integer_go, decode_encode_go] at same
  simpa only [Nat.pow_zero, Nat.one_mul, natToBytesLE_eq_integer_go] using same.symm

/-- NaNs refuse before selecting a width, because their payload is not observable
    in the pinned Lean runtime. This is the exact existing error and precedence. -/
theorem encodeFloatAt_nan_refuses (ty : Ty) (value : Float) (nan : value.isNaN = true) :
    encodeFloatAt ty value = .error
      (.unsupported .float "NaN byte image unobservable (no Float.toBits in Lean 4.8.0)") := by
  simp only [encodeFloatAt, nan, ite_true]

/-- Complete successful-store characterization at every supported width. -/
theorem FloatStorageFormat.encode_success_iff {ty : Ty} {format : BinaryFormat} {count : Nat}
    (storage : FloatStorageFormat ty format count) (value : Float) (bytes : List UInt8) :
    encodeFloatAt ty value = .ok bytes ↔
      value.isNaN = false ∧ ∃ bits, encodeBits format value = some bits ∧ bytes = natToBytesLE count bits := by
  cases storage <;> cases nan : value.isNaN
  all_goals simp only [encodeFloatAt, nan, Bool.false_eq_true, ite_false, ite_true]
  all_goals first
    | (cases bits : encodeBits _ value <;> simp [bits, Eq.comm])
    | simp

/-- Successful typed storage has exactly the format's byte width. -/
theorem FloatStorageFormat.encode_extent {ty : Ty} {format : BinaryFormat} {count : Nat}
    (storage : FloatStorageFormat ty format count) (value : Float) (bytes : List UInt8)
    (encoded : encodeFloatAt ty value = .ok bytes) : bytes.length = count := by
  obtain ⟨_notNan,bits,_view,rfl⟩ := (storage.encode_success_iff value bytes).mp encoded
  exact natToBytesLE_length count bits

private theorem decode_width_iff (count : Nat) (bytes : List UInt8) (decoded output : Float) (message : String) :
    (if bytes.length == count then (Except.ok decoded : Except SemError Float)
      else .error (.typeError message)) = .ok output ↔ bytes.length = count ∧ output = decoded := by
  simp only [beq_iff_eq]
  by_cases size : bytes.length = count
  · rw [if_pos size, Except.ok.injEq]
    exact ⟨fun same => ⟨size,same.symm⟩, fun same => same.2.symm⟩
  · rw [if_neg size]
    constructor
    · intro impossible; cases impossible
    · intro valid; exact False.elim (size valid.1)

/-- The decoder succeeds exactly at its declared byte count and returns the
    concrete IEEE interpretation of those bytes. -/
theorem FloatStorageFormat.decode_success_iff {ty : Ty} {format : BinaryFormat} {count : Nat}
    (storage : FloatStorageFormat ty format count) (bytes : List UInt8) (output : Float) :
    decodeFloatAt ty bytes = .ok output ↔
      bytes.length = count ∧ output = decodeBits format (natOfBytesLE bytes) := by
  cases storage <;> exact decode_width_iff _ bytes _ output _

/-- An actual successful store reloads the exact encoded IEEE residue. This
    does not assert equality of opaque native Float values. -/
theorem FloatStorageFormat.encoded_byte_readback {ty : Ty} {format : BinaryFormat} {count : Nat}
    (storage : FloatStorageFormat ty format count) (value : Float) (bytes : List UInt8)
    (encoded : encodeFloatAt ty value = .ok bytes) :
    ∃ bits, encodeBits format value = some bits ∧ bytes = natToBytesLE count bits ∧
      decodeFloatAt ty bytes = .ok (decodeBits format (bits % 256 ^ count)) := by
  obtain ⟨_notNan,bits,view,image⟩ := (storage.encode_success_iff value bytes).mp encoded
  refine ⟨bits,view,image,(storage.decode_success_iff bytes _).mpr ⟨storage.encode_extent value bytes encoded,?_⟩⟩
  rw [image, natOfBytesLE_natToBytesLE]

namespace AggregateMemory
open SourceLayout

/-- The real ordinary leaf encoder delegates float values to the typed codec,
    then enforces the source layout's byte count. -/
theorem encode_float_leaf_result {ty : Ty} {format : BinaryFormat} {count : Nat}
    (storage : FloatStorageFormat ty format count) (model : ByteModel) (order : FunctionAddressOrder)
    (layout : MemoryTypeLayout) (value : Float) :
    encode model order (.leaf ty layout) (.float value) false =
      (encodeFloatAt ty value).bind (fun bytes =>
        if bytes.length != layout.size then .error (.typeError "memory image: leaf byte count mismatch")
        else .ok { bytes := ByteImage.ofList (bytes.map some) }) := by
  cases storage <;> exact encode_float_leaf_of_type model order _ layout value rfl

theorem encode_float_leaf_nan_refuses {ty : Ty} {format : BinaryFormat} {count : Nat}
    (storage : FloatStorageFormat ty format count) (model : ByteModel) (order : FunctionAddressOrder)
    (layout : MemoryTypeLayout) (value : Float) (nan : value.isNaN = true) :
    encode model order (.leaf ty layout) (.float value) false = .error
      (.unsupported .float "NaN byte image unobservable (no Float.toBits in Lean 4.8.0)") := by
  rw [encode_float_leaf_result storage, encodeFloatAt_nan_refuses ty value nan]
  rfl

theorem encode_float_leaf_wrong_extent {ty : Ty} {format : BinaryFormat} {count : Nat}
    (storage : FloatStorageFormat ty format count) (model : ByteModel) (order : FunctionAddressOrder)
    (layout : MemoryTypeLayout) (value : Float) (bytes : List UInt8)
    (encoded : encodeFloatAt ty value = .ok bytes) (wrong : layout.size ≠ count) :
    encode model order (.leaf ty layout) (.float value) false =
      .error (.typeError "memory image: leaf byte count mismatch") := by
  rw [encode_float_leaf_result storage, encoded]
  simp [Except.bind, storage.encode_extent value bytes encoded, Ne.symm wrong]

theorem encode_float_leaf_success {ty : Ty} {format : BinaryFormat} {count : Nat}
    (storage : FloatStorageFormat ty format count) (model : ByteModel) (order : FunctionAddressOrder)
    (layout : MemoryTypeLayout) (value : Float) (bytes : List UInt8)
    (encoded : encodeFloatAt ty value = .ok bytes) (size : layout.size = count) :
    encode model order (.leaf ty layout) (.float value) false =
      .ok { bytes := ByteImage.ofList (bytes.map some) } := by
  rw [encode_float_leaf_result storage, encoded]
  simp [Except.bind, storage.encode_extent value bytes encoded, size]

/-- Complete ordinary-leaf failure correspondence: the typed codec error is
    retained exactly, or successful typed bytes fail the actual layout extent. -/
theorem encode_float_leaf_error_iff {ty : Ty} {format : BinaryFormat} {count : Nat}
    (storage : FloatStorageFormat ty format count) (model : ByteModel) (order : FunctionAddressOrder)
    (layout : MemoryTypeLayout) (value : Float) (error : SemError) :
    encode model order (.leaf ty layout) (.float value) false = .error error ↔
      encodeFloatAt ty value = .error error ∨
        ∃ bytes, encodeFloatAt ty value = .ok bytes ∧ bytes.length ≠ layout.size ∧
          error = .typeError "memory image: leaf byte count mismatch" := by
  rw [encode_float_leaf_result storage]
  cases run : encodeFloatAt ty value with
  | error failure => simp [Except.bind]
  | ok bytes =>
    by_cases size : bytes.length = layout.size
    · simp [Except.bind, size]
    · simp [Except.bind, size]
      exact eq_comm

/-- Actual successful aggregate storage supplies the byte-view witness and
    source extent, without a separate Float-format or decoder certificate. -/
theorem float_leaf_stored_byte_view {ty : Ty} {format : BinaryFormat} {count : Nat}
    (storage : FloatStorageFormat ty format count) (model : ByteModel) (order : FunctionAddressOrder)
    (layout : MemoryTypeLayout) (value : Float) (stored : Image)
    (encoded : encode model order (.leaf ty layout) (.float value) false = .ok stored) :
    ∃ bits, encodeBits format value = some bits ∧ layout.size = count ∧
      stored = { bytes := ByteImage.ofList ((natToBytesLE count bits).map some) } ∧
      decodeFloatAt ty (natToBytesLE count bits) = .ok (decodeBits format (bits % 256 ^ count)) := by
  obtain ⟨bytes,memory,size,_image⟩ := encode_leaf_memory_success model order ty layout (.float value) stored encoded
  have floatRun : encodeFloatAt ty value = .ok bytes := by
    cases storage <;> cases model <;> exact memory
  obtain ⟨bits,view,byteShape,decoded⟩ := storage.encoded_byte_readback value bytes floatRun
  refine ⟨bits,view,size.symm.trans (storage.encode_extent value bytes floatRun),?_,?_⟩
  · have success := encode_float_leaf_success storage model order layout value bytes floatRun
      (size.symm.trans (storage.encode_extent value bytes floatRun))
    have shape := Except.ok.inj (encoded.symm.trans success)
    simpa only [byteShape] using shape
  · simpa only [byteShape] using decoded

end AggregateMemory
end TrustIr
