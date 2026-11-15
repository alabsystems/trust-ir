-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- One integer representation: the binding sites of an integer constant make
-- a residue, the switch case scan compares residues, and the sign-reading
-- consumers read a residue signed.

import TrustIr.Semantics.Eval
import TrustIr.Proofs.MemoryProps
import TrustIr.Proofs.ByteMemory

namespace TrustIr

/-!
# One integer representation

The Lean model keeps an integer as `Value.int w v` with no signedness. Its
invariant is `0 ≤ v < 2^w`: parameters (`TrustIrEval/Run.lean` `argValue`)
and operation results (`wrap`, `truncateUnsigned`) satisfy it, and so does
every place where a `Constant.int` becomes a model value, because each goes
through `Value.intAt`. This module proves that for the binding sites, the
switch comparison, and the signed reading the GEP index takes.

The theorems state the model; they do not relate it to the reference
interpreter. That tie is the Lean-execution differential
(`crates/trust-ir-conformance/tests/lean_exec_differential.rs`,
`negative_literal_constants_agree_across_engines`), which is TEST evidence.
-/

/-- `2^w` is positive. -/
theorem two_pow_pos_int (w : Nat) : (0 : Int) < 2 ^ w := by
  induction w with
  | zero => decide
  | succ k ih =>
    rw [Int.pow_succ]
    exact Int.mul_pos ih (by decide)

theorem truncateUnsigned_nonneg (i : Int) (w : Nat) : 0 ≤ truncateUnsigned i w :=
  Int.emod_nonneg i (Int.ne_of_gt (two_pow_pos_int w))

theorem truncateUnsigned_lt (i : Int) (w : Nat) : truncateUnsigned i w < 2 ^ w :=
  Int.emod_lt_of_pos i (two_pow_pos_int w)

/-- A residue is its own residue. -/
theorem truncateUnsigned_of_residue {v : Int} {w : Nat} (h0 : 0 ≤ v) (h1 : v < 2 ^ w) :
    truncateUnsigned v w = v :=
  Int.emod_eq_of_lt h0 h1

/-- Zero is its own residue at every width. -/
theorem intAt_zero (w : Nat) : Value.intAt w 0 = .int w 0 := by
  simp only [Value.intAt, truncateUnsigned, Int.zero_emod]

/-- Every integer `Value.intAt` makes is a residue at its width. -/
theorem intAt_residue {w w' : Nat} {i v : Int} (h : Value.intAt w i = .int w' v) :
    0 ≤ v ∧ v < 2 ^ w' := by
  simp only [Value.intAt, Value.int.injEq] at h
  obtain ⟨hw, hv⟩ := h
  subst hw
  subst hv
  exact ⟨truncateUnsigned_nonneg i w, truncateUnsigned_lt i w⟩

/-- Binding site (bare `Const` step, scalar and tuple / vector leaves): an
    integer constant lowered at its declared type is a residue. -/
theorem constValueAt_int_residue {ty : Ty} {i : Int} {w : Nat} {v : Int}
    (h : constValueAt ty (.int i) = .int w v) : 0 ≤ v ∧ v < 2 ^ w := by
  trustIrCompilerProof { simp only [constValueAt] at h } { unfold constValueAt at h }
  split at h
  · split at h
    · cases h
    · exact intAt_residue h
  · split at h
    · exact intAt_residue h
    · exact intAt_residue h

/-- Binding site (a global initializer, `semGlobalAddrWithCtx`). -/
theorem valueOfConstAtTy_int_residue {ty : Ty} {i : Int} {w : Nat} {v : Int}
    (h : valueOfConstAtTy ty (.int i) = .int w v) : 0 ≤ v ∧ v < 2 ^ w := by
  exact constValueAt_int_residue h

/-- Binding site (the untyped lowering `Value.ofConstant`, the 64-bit default). -/
theorem ofConstant_int_residue {i : Int} {w : Nat} {v : Int}
    (h : Value.ofConstant (.int i) = .int w v) : 0 ≤ v ∧ v < 2 ^ w := by
  simp only [Value.ofConstant] at h
  exact intAt_residue h

/-- The switch case scan compares RESIDUES at the scrutinee's width, on both
    sides, which is the reference interpreter's conversion of the case at the
    scrutinee's type. -/
theorem switchCaseMatches_int (w : Nat) (v c : Int) :
    switchCaseMatches (.int w v) (.int c) = (v % 2 ^ w == c % 2 ^ w) := rfl

/-- A residue scrutinee matches a case exactly when the case's residue is it. -/
theorem switchCaseMatches_residue {w : Nat} {v c : Int} (h0 : 0 ≤ v) (h1 : v < 2 ^ w) :
    switchCaseMatches (.int w v) (.int c) = (v == truncateUnsigned c w) := by
  rw [switchCaseMatches_int, ← truncateUnsigned, ← truncateUnsigned,
      truncateUnsigned_of_residue h0 h1]

/-- `2^(w-1) ≤ 2^w`. -/
theorem two_pow_pred_le (w : Nat) : (2 : Int) ^ (w - 1) ≤ 2 ^ w := by
  cases w with
  | zero => exact Int.le_refl _
  | succ k =>
    have hk := two_pow_pos_int k
    have h2 : (2 : Int) ^ (k + 1) = 2 ^ k * 2 := Int.pow_succ 2 k
    simp only [Nat.add_sub_cancel]
    rw [h2]
    omega

/-- The signed reading of a non-negative value below the sign bit is itself. -/
theorem toSigned_of_lt_half {i : Int} {w : Nat} (h0 : 0 ≤ i) (h1 : i < 2 ^ (w - 1)) :
    toSigned i w = i := by
  have hlt : i < 2 ^ w := Int.lt_of_lt_of_le h1 (two_pow_pred_le w)
  have hmod : i % 2 ^ w = i := Int.emod_eq_of_lt h0 hlt
  simp only [toSigned, hmod]
  have : ¬ (i ≥ 2 ^ (w - 1)) := Int.not_le.mpr h1
  simp [this]

/-- The signed reading of a residue at or above the sign bit is negative. -/
theorem toSigned_neg_of_ge_half {i : Int} {w : Nat} (h0 : 2 ^ (w - 1) ≤ i) (h1 : i < 2 ^ w) :
    toSigned i w < 0 := by
  have hnn : 0 ≤ i := Int.le_trans (Int.le_of_lt (two_pow_pos_int (w - 1))) h0
  have hmod : i % 2 ^ w = i := Int.emod_eq_of_lt hnn h1
  simp only [toSigned, hmod]
  have : i ≥ 2 ^ (w - 1) := h0
  simp only [this, ite_true]
  omega

/-- Reading an admitted signed residue preserves its bounded GEP offset.
    The actual instruction obtains signedness from its source declaration. -/
theorem gepByteOffset_signed {ty : Ty} {i : Int} {w size : Nat}
    (h0 : 0 ≤ i) (h1 : i < 2 ^ (w - 1)) (hs : ty.byteSize = some size)
    (h64 : i ≤ (word64Max : Int)) (hMul : i.toNat * size ≤ word64Max) :
    gepByteOffset ty (toSigned i w) = .ok (i.toNat * size) := by
  rw [toSigned_of_lt_half h0 h1]
  exact gepByteOffset_bounded ty size i hs h0 h64 hMul

/-- A negative signed operand is refused before multiplication. -/
theorem gepByteOffset_signed_negative {ty : Ty} {i : Int} {w size : Nat}
    (h0 : 2 ^ (w - 1) ≤ i) (h1 : i < 2 ^ w) (hs : ty.byteSize = some size) :
    gepByteOffset ty (toSigned i w) = .error
      (.ub "GEP: integer operand is outside its nonnegative/positive domain") := by
  have hneg := toSigned_neg_of_ge_half h0 h1
  simp [gepByteOffset, scalarMemoryLayout_of_byteSize ty size hs,
    checkedWord64Operand, hneg, bind, Except.bind]
  rfl

/-- The byte encoder's double-mod spelling is exactly the canonical residue,
including negative literals and inputs wider than the declared integer. -/
theorem integer_encoding_residue (raw : Int) (width : Nat) :
    ((raw % (2 ^ width)) + (2 ^ width)) % (2 ^ width) = truncateUnsigned raw width := by
  simp only [truncateUnsigned,Int.add_emod,Int.emod_self,Int.add_zero,Int.emod_emod]

/-- The real little-endian byte codec preserves every byte-aligned residue;
no nonnegativity or fit premise is imposed on the original integer literal. -/
theorem decode_encode_integer_residue (raw : Int) (count : Nat) :
    Int.ofNat (decodeIntBytes (encodeIntBytes (truncateUnsigned raw (8 * count)) count)) =
      truncateUnsigned raw (8 * count) := by
  have natural : (256 : Nat) ^ count = 2 ^ (8 * count) := by
    rw [Nat.pow_mul]
  have capacity : Int.ofNat ((256 : Nat) ^ count) = (2 : Int) ^ (8 * count) := by
    rw [natural]
    exact Int.natCast_pow _ _
  have cast := Int.toNat_of_nonneg (truncateUnsigned_nonneg raw (8 * count))
  have small : (truncateUnsigned raw (8 * count)).toNat < 256 ^ count := by
    apply Int.ofNat_lt.mp
    change Int.ofNat (truncateUnsigned raw (8 * count)).toNat < Int.ofNat (256 ^ count)
    rw [show Int.ofNat (truncateUnsigned raw (8 * count)).toNat = truncateUnsigned raw (8 * count) from cast,capacity]
    exact truncateUnsigned_lt raw (8 * count)
  change Int.ofNat (decodeIntBytes.go (encodeIntBytes.go count (truncateUnsigned raw (8 * count)).toNat) 0) = _
  rw [decode_encode_go,Nat.pow_zero,Nat.one_mul,Nat.mod_eq_of_lt small]
  exact cast

/-- Every actual integer/Char width, with target-sized integers interpreted
at the selected 32- or 64-bit model, occupies a whole number of bytes. -/
theorem integer_memory_width_aligned (model : ByteModel) (ty : Ty) (width : Nat)
    (integer : ty.isInteger = true) (typed : ty.bitWidthFor model = some width) : 8 * (width / 8) = width := by
  cases model <;> cases ty <;> simp [Ty.isInteger,Ty.bitWidthFor,Ty.bitWidthAtModel,Ty.bitWidth,
    Ty.bitWidthAtPointerBits,ByteModel.pointerBits,ByteModel.pointerBytes] at integer typed ⊢ <;>
    subst width <;> decide

/-- The actual contextual store normalizes its supplied integer carrier.
Agreement with the declared type's width is a separate boundary condition. -/
theorem encodeMemory_integer_residue (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (width : Nat) (raw : Int)
    (integer : ty.isInteger = true) :
    encodeMemoryWithFunctions model order ty (.int width raw) =
      .ok (encodeIntBytes (truncateUnsigned raw width) (width / 8)) := by
  cases model <;> cases ty <;>
    simp only [Ty.isInteger] at integer <;> try cases integer
  all_goals simp only [encodeMemoryWithFunctions,encodeMemoryAt,checkPointerImageWords,
    encodeValueAt,encodeTypedAtModel,fatPtrStoreValueValidAtModel,encodeValueAtModel,encodeValue,
    Except.bind,integer_encoding_residue]
  all_goals rfl

/-- Integer loads return the residue represented by the actual bytes. Char
retains its top-level Unicode validity guard and its original UB result. -/
theorem decodeMemory_integer_bytes (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (width : Nat) (bytes : List UInt8)
    (integer : ty.isInteger = true) (typed : ty.bitWidthFor model = some width)
    (size : bytes.length = width / 8) :
    decodeMemoryWithFunctions model order memory ty bytes =
      match ty with
      | .Char => if validChar (decodeIntBytes bytes) then .ok (.int width (Int.ofNat (decodeIntBytes bytes)))
        else .error (.ub "memory decode: invalid Unicode scalar value")
      | _ => .ok (.int width (Int.ofNat (decodeIntBytes bytes))) := by
  cases model <;> cases ty <;>
    simp only [Ty.isInteger] at integer <;> try cases integer
  all_goals simp only [Ty.bitWidthFor,Ty.bitWidthAtModel,Ty.bitWidth,Ty.bitWidthAtPointerBits,
    ByteModel.pointerBits,ByteModel.pointerBytes] at typed
  all_goals cases typed
  all_goals simp only [decodeMemoryWithFunctions,decodeMemoryAt,decodeValueAt,decodeTypedAtModel,
    decodeImageAt,decodeImageAtModel,decodeValueAtModel,decodeValue,Ty.isFloat,decodeCharImage,size,
    beq_self_eq_true,ite_true,Bool.false_eq_true,ite_false,Except.bind,Except.pure,Memory.resolveDecoded]
  all_goals by_cases good : validChar (decodeIntBytes bytes) <;> simp [good]
  all_goals rfl

/-- One law for all signed/unsigned integer families and both target widths.
Char's Unicode refusal is explicit; every other integer round-trips exactly
to the model's canonical residue for arbitrary original Int literals. -/
theorem integer_memory_roundtrip (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (width : Nat) (raw : Int)
    (integer : ty.isInteger = true) (typed : ty.bitWidthFor model = some width) :
    (encodeMemoryWithFunctions model order ty (.int width raw)).bind
      (decodeMemoryWithFunctions model order memory ty) =
      match ty with
      | .Char => if validChar (truncateUnsigned raw width).toNat then .ok (Value.intAt width raw)
        else .error (.ub "memory decode: invalid Unicode scalar value")
      | _ => .ok (Value.intAt width raw) := by
  rw [encodeMemory_integer_residue model order ty width raw integer]
  simp only [Except.bind]
  rw [decodeMemory_integer_bytes model order memory ty width _ integer typed (encodeIntBytes_length _ _)]
  have decoded := decode_encode_integer_residue raw (width / 8)
  rw [integer_memory_width_aligned model ty width integer typed] at decoded
  have normalized := Int.toNat_of_nonneg (truncateUnsigned_nonneg raw width)
  have same : decodeIntBytes (encodeIntBytes (truncateUnsigned raw width) (width / 8)) =
      (truncateUnsigned raw width).toNat := by
    apply Int.ofNat_inj.mp
    exact decoded.trans normalized.symm
  rw [same]
  change (show Except SemError Value from match ty with
    | .Char => if validChar (truncateUnsigned raw width).toNat then
        .ok (.int width (Int.ofNat (truncateUnsigned raw width).toNat))
      else .error (.ub "memory decode: invalid Unicode scalar value")
    | _ => .ok (.int width (Int.ofNat (truncateUnsigned raw width).toNat))) = _
  rw [show Int.ofNat (truncateUnsigned raw width).toNat = truncateUnsigned raw width from normalized]
  rfl

/-- Scalar boolean storage uses its real 0/1 image on either target. -/
theorem boolean_memory_roundtrip (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) (value : Bool) :
    (encodeMemoryWithFunctions model order .Bool (.bool value)).bind
      (decodeMemoryWithFunctions model order memory .Bool) = .ok (.bool value) := by
  cases model <;> cases value <;> rfl

/-- Well-typed integer lanes round-trip exactly, with the actual Unicode
validity premise required only when the source type is Char. -/
theorem integer_memory_roundtrip_valid (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (width : Nat) (raw : Int)
    (integer : ty.isInteger = true) (typed : ty.bitWidthFor model = some width)
    (character : ty = .Char → validChar (truncateUnsigned raw width).toNat) :
    (encodeMemoryWithFunctions model order ty (.int width raw)).bind
      (decodeMemoryWithFunctions model order memory ty) = .ok (Value.intAt width raw) := by
  rw [integer_memory_roundtrip model order memory ty width raw integer typed]
  cases ty <;> try rfl
  exact if_pos (character rfl)

/-- The real aggregate leaf image and decoder obey the same typed integer
law. A source-layout-sized image is produced, with Char validity checked by
the actual top-level decoder, and no caller-supplied byte round-trip premise. -/
theorem integer_aggregate_leaf_roundtrip (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (width : Nat) (raw : Int)
    (integer : ty.isInteger = true) (typed : ty.bitWidthFor model = some width)
    (extent : layout.size = width / 8) :
    (AggregateMemory.encode model order (.leaf ty layout) (.int width raw) false).bind
      (fun image => AggregateMemory.decode model order memory (.leaf ty layout) image.bytes) =
      match ty with
      | .Char => if validChar (truncateUnsigned raw width).toNat then .ok (Value.intAt width raw)
        else .error (.ub "memory decode: invalid Unicode scalar value")
      | _ => .ok (Value.intAt width raw) := by
  have size := (encodeIntBytes_length (truncateUnsigned raw width) (width / 8)).trans extent.symm
  rw [AggregateMemory.encode_integer_leaf_of_memory model order ty layout width raw _ integer typed size
    (encodeMemory_integer_residue model order ty width raw integer)]
  simp only [Except.bind]
  rw [AggregateMemory.decode_leaf_of_bytes model order memory ty layout _ size]
  have scalar := integer_memory_roundtrip model order memory ty width raw integer typed
  rw [encodeMemory_integer_residue model order ty width raw integer] at scalar
  exact scalar

/-- The ordinary boolean leaf also round-trips through actual byte images. -/
theorem boolean_aggregate_leaf_roundtrip (model : ByteModel) (order : FunctionAddressOrder)
    (memory : Memory) (value : Bool) :
    (AggregateMemory.encode model order (.leaf .Bool ⟨1,1⟩) (.bool value) false).bind
      (fun image => AggregateMemory.decode model order memory (.leaf .Bool ⟨1,1⟩) image.bytes) = .ok (.bool value) := by
  cases model <;> cases value <;> trustIrReduce

/-- Strict nested integer leaves decode their real stored bytes to the
    canonical residue. Nested Char intentionally retains its raw-word rule. -/
theorem integer_child_leaf_bytes (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (width : Nat) (raw : Int)
    (integer : ty.isInteger = true) (typed : ty.bitWidthFor model = some width)
    (extent : layout.size = width / 8) :
    AggregateMemory.ChildDecoded model order memory (.leaf ty layout)
      (ByteImage.ofList ((encodeIntBytes (truncateUnsigned raw width) (width / 8)).map some))
      (Value.intAt width raw) := by
  rw [AggregateMemory.ChildDecoded.leaf_bytes_iff model order memory ty layout _
    ((encodeIntBytes_length _ _).trans extent.symm)]
  have normalized := decode_encode_integer_residue raw (width / 8)
  rw [integer_memory_width_aligned model ty width integer typed] at normalized
  by_cases character : ty = .Char
  · subst ty
    have widthEq : width = 32 := by
      cases model <;> simp only [Ty.bitWidthFor,Ty.bitWidthAtModel,Ty.bitWidth,Ty.bitWidthAtPointerBits] at typed
      all_goals exact (Option.some.inj typed).symm
    subst width
    exact congrArg (fun value => (Except.ok (Value.int 32 value) : Except SemError Value)) normalized
  · have scalar := decodeMemory_integer_bytes model order memory ty width
      (encodeIntBytes (truncateUnsigned raw width) (width / 8)) integer typed (encodeIntBytes_length _ _)
    cases ty <;> try exact False.elim (character rfl)
    all_goals simpa only [Value.intAt,normalized] using scalar

/-- Complete observed child bytes from an actual successful integer store
    suffice for strict nested readback; decoder success is a conclusion. -/
theorem integer_child_readback_of_encoded (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (width : Nat) (raw : Int)
    (integer : ty.isInteger = true) (typed : ty.bitWidthFor model = some width)
    (extent : layout.size = width / 8) (stored : AggregateMemory.Image) (loaded : ByteImage)
    (encoded : AggregateMemory.encode model order (.leaf ty layout) (.int width raw) false = .ok stored)
    (loadedSize : loaded.size = layout.size) (bytes : ∀ index, loaded.get index = stored.bytes.get index) :
    AggregateMemory.ChildDecoded model order memory (.leaf ty layout) loaded (Value.intAt width raw) := by
  have storedRun := AggregateMemory.encode_integer_leaf_of_memory model order ty layout width raw _ integer typed
    ((encodeIntBytes_length _ _).trans extent.symm) (encodeMemory_integer_residue model order ty width raw integer)
  rw [storedRun] at encoded
  cases encoded
  apply (AggregateMemory.ChildDecoded.leaf_iff_of_observations model order memory ty layout loaded _
    (by rw [ByteImage.size_ofList,List.length_map,encodeIntBytes_length,loadedSize,extent]) bytes _).mpr
  exact integer_child_leaf_bytes model order memory ty layout width raw integer typed extent

namespace ScalarCodecControls

/-- Negative signed literals return their canonical residue, not a negative
raw Int, at every supported machine-integer width. -/
theorem negative_i128 (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) :
    (encodeMemoryWithFunctions model order .I128 (.int 128 (-1))).bind
      (decodeMemoryWithFunctions model order memory .I128) = .ok (Value.intAt 128 (-1)) :=
  integer_memory_roundtrip model order memory .I128 128 (-1) rfl (by cases model <;> rfl)

theorem target_sized_32 (order : FunctionAddressOrder) (memory : Memory) (raw : Int) :
    (encodeMemoryWithFunctions .le32 order .Isize (.int 32 raw)).bind
      (decodeMemoryWithFunctions .le32 order memory .Isize) = .ok (Value.intAt 32 raw) :=
  integer_memory_roundtrip .le32 order memory .Isize 32 raw rfl rfl

theorem target_sized_64 (order : FunctionAddressOrder) (memory : Memory) (raw : Int) :
    (encodeMemoryWithFunctions .le64 order .Usize (.int 64 raw)).bind
      (decodeMemoryWithFunctions .le64 order memory .Usize) = .ok (Value.intAt 64 raw) :=
  integer_memory_roundtrip .le64 order memory .Usize 64 raw rfl rfl

theorem oversized_u8 (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) :
    (AggregateMemory.encode model order (.leaf .U8 ⟨1,1⟩) (.int 8 513) false).bind
      (fun image => AggregateMemory.decode model order memory (.leaf .U8 ⟨1,1⟩) image.bytes) = .ok (.int 8 1) :=
  integer_aggregate_leaf_roundtrip model order memory .U8 ⟨1,1⟩ 8 513 rfl (by cases model <;> rfl) rfl

theorem char_surrogate_refuses (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) :
    (AggregateMemory.encode model order (.leaf .Char ⟨4,4⟩) (.int 32 55296) false).bind
      (fun image => AggregateMemory.decode model order memory (.leaf .Char ⟨4,4⟩) image.bytes) =
      .error (.ub "memory decode: invalid Unicode scalar value") := by
  have run := integer_aggregate_leaf_roundtrip model order memory .Char ⟨4,4⟩ 32 55296 rfl (by cases model <;> rfl) rfl
  simpa only [truncateUnsigned,show (55296 : Int) % 2 ^ 32 = 55296 from rfl,
    show ¬ validChar 55296 from (by decide),if_neg] using run

theorem valid_char (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) :
    (AggregateMemory.encode model order (.leaf .Char ⟨4,4⟩) (.int 32 128512) false).bind
      (fun image => AggregateMemory.decode model order memory (.leaf .Char ⟨4,4⟩) image.bytes) = .ok (.int 32 128512) := by
  have run := integer_aggregate_leaf_roundtrip model order memory .Char ⟨4,4⟩ 32 128512 rfl (by cases model <;> rfl) rfl
  simpa only [Value.intAt,truncateUnsigned,show (128512 : Int) % 2 ^ 32 = 128512 from rfl,
    show validChar 128512 from (by decide),if_pos] using run

theorem wrong_leaf_width_refuses (model : ByteModel) (order : FunctionAddressOrder) (raw : Int) :
    AggregateMemory.encode model order (.leaf .U16 ⟨2,2⟩) (.int 8 raw) false =
      .error (.typeError "memory image: integer lane width does not match its source type") := by
  cases model <;> trustIrReduce

theorem wrong_leaf_extent_refuses (model : ByteModel) (order : FunctionAddressOrder) :
    AggregateMemory.encode model order (.leaf .U16 ⟨1,1⟩) (.int 16 7) false =
      .error (.typeError "memory image: leaf byte count mismatch") := by
  cases model <;> trustIrReduce

end ScalarCodecControls

end TrustIr
