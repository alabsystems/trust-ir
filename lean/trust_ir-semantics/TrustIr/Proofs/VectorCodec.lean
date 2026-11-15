-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.IntResidue
import TrustIr.Proofs.SourceValueMembership

namespace TrustIr

/-- Packed vector lanes with proved logical readback. Float formats retain
    their separate numerical-refinement obligation. -/
inductive VectorReadbackLane : Ty → Prop where
  | boolean : VectorReadbackLane .Bool
  | i8 : VectorReadbackLane .I8
  | u8 : VectorReadbackLane .U8
  | i16 : VectorReadbackLane .I16
  | u16 : VectorReadbackLane .U16
  | i32 : VectorReadbackLane .I32
  | u32 : VectorReadbackLane .U32
  | i64 : VectorReadbackLane .I64
  | u64 : VectorReadbackLane .U64

def vectorReadbackLane : Ty → Bool
  | .Bool | .I8 | .U8 | .I16 | .U16 | .I32 | .U32 | .I64 | .U64 => true
  | _ => false

def VectorLaneReady (ty : Ty) (value : Value) : Prop :=
  match ty, value with
  | .Bool, .bool _ => True
  | _, .int width _ => ty.isInteger = true ∧ ty.bitWidth = some width
  | _, _ => False

def vectorLaneResult : Value → Value
  | .int width raw => Value.intAt width raw
  | value => value

theorem VectorReadbackLane.byte_size {ty : Ty} (lane : VectorReadbackLane ty) :
    ∃ size, vectorScalarByteSize ty = some size ∧ 0 < size := by
  cases lane <;> first | exact ⟨1,rfl,by decide⟩ | exact ⟨2,rfl,by decide⟩ | exact ⟨4,rfl,by decide⟩ | exact ⟨8,rfl,by decide⟩

theorem vectorReadbackLane_iff (ty : Ty) : vectorReadbackLane ty = true ↔ VectorReadbackLane ty := by
  cases ty <;> simp only [vectorReadbackLane]
  all_goals constructor
  all_goals first | (intro _; constructor) | (intro impossible; cases impossible)

theorem vector_integer_lane_bytes (ty : Ty) (width : Nat) (raw : Int)
    (lane : VectorReadbackLane ty) (integer : ty.isInteger = true) (typed : ty.bitWidth = some width) :
    encodeVectorLane ty (.int width raw) = .ok (encodeIntBytes (truncateUnsigned raw width) (width / 8)) := by
  cases lane <;> simp only [Ty.isInteger] at integer <;> try cases integer
  all_goals have same := Option.some.inj typed; subst width
  all_goals simp [encodeVectorLane,vectorScalarByteSize,Ty.isInteger,Ty.bitWidth,Ty.bitWidthAtPointerBits,
    encodeValue,integer_encoding_residue,truncateUnsigned,encodeIntBytes_length,Bind.bind,Except.bind,Pure.pure,Except.pure]

theorem vector_integer_lane_decodes (ty : Ty) (width : Nat) (raw : Int)
    (lane : VectorReadbackLane ty) (integer : ty.isInteger = true) (typed : ty.bitWidth = some width) :
    decodeVectorLane ty (encodeIntBytes (truncateUnsigned raw width) (width / 8)) = .ok (Value.intAt width raw) := by
  have scalar := integer_memory_roundtrip .le64 none Memory.empty ty width raw integer typed
  have encoded := encodeMemory_integer_residue .le64 none ty width raw integer
  rw [encoded] at scalar
  simp only [Except.bind] at scalar
  cases lane <;> simp only [Ty.isInteger] at integer <;> try cases integer
  all_goals have same := Option.some.inj typed; subst width
  all_goals simpa [decodeVectorLane,vectorScalarByteSize,Ty.isFloat,decodeMemoryWithFunctions,
    decodeMemoryAt,decodeValueAt,decodeImageAt,decodeValue,Memory.resolveDecoded,encodeIntBytes_length,
    Bind.bind,Except.bind,Pure.pure,Except.pure] using scalar

theorem vector_lane_roundtrip (ty : Ty) (input : Value) (bytes : List UInt8)
    (lane : VectorReadbackLane ty) (ready : VectorLaneReady ty input)
    (encoded : encodeVectorLane ty input = .ok bytes) :
    decodeVectorLane ty bytes = .ok (vectorLaneResult input) := by
  cases input with
  | int width raw =>
    have shape : ty.isInteger = true ∧ ty.bitWidth = some width := by cases ty <;> exact ready
    rw [vector_integer_lane_bytes ty width raw lane shape.1 shape.2] at encoded
    cases encoded
    exact vector_integer_lane_decodes ty width raw lane shape.1 shape.2
  | bool value =>
    cases lane <;> try cases ready
    cases value <;> simp [encodeVectorLane,vectorScalarByteSize,Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded
    all_goals cases encoded
    all_goals rfl
  | _ => cases lane <;> cases ready

/-- Every successful actual lane write has its declared byte extent. -/
theorem encodeVectorLane_extent (ty : Ty) (input : Value) (bytes : List UInt8) (size : Nat)
    (typed : vectorScalarByteSize ty = some size) (encoded : encodeVectorLane ty input = .ok bytes) :
    bytes.length = size := by
  unfold encodeVectorLane at encoded
  rw [typed] at encoded
  dsimp only at encoded
  repeat' first
    | (simp only [Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded)
    | split at encoded
    | (dsimp only at encoded; split at encoded)
  all_goals first
    | (solve | cases encoded)
    | (have same := Except.ok.inj encoded; subst bytes; simp_all)

private theorem vector_take_append {α : Type} (first rest : List α) :
    (first ++ rest).take first.length = first := by
  induction first with
  | nil => rfl
  | cons head tail ih => simp [List.take, ih]

private theorem vector_drop_append {α : Type} (first rest : List α) :
    (first ++ rest).drop first.length = rest := by
  induction first with
  | nil => rfl
  | cons _head tail ih => simp [List.drop, ih]

/-- Packed decoding follows exactly the lane boundaries of actual encoding. -/
theorem vector_lanes_roundtrip (ty : Ty) (inputs : List Value) (bytes : List UInt8) (size : Nat)
    (lane : VectorReadbackLane ty) (typed : vectorScalarByteSize ty = some size)
    (ready : ∀ input ∈ inputs, VectorLaneReady ty input)
    (encoded : encodeVectorLanes ty inputs = .ok bytes) :
    bytes.length = inputs.length * size ∧
      decodeVectorLanes ty size inputs.length bytes = .ok (inputs.map vectorLaneResult) := by
  induction inputs generalizing bytes with
  | nil => cases encoded; exact ⟨by simp,rfl⟩
  | cons first rest ih =>
    rw [encodeVectorLanes] at encoded
    cases firstRun : encodeVectorLane ty first with
    | error error => simp [firstRun,Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded
    | ok firstBytes =>
      cases restRun : encodeVectorLanes ty rest with
      | error error => simp [firstRun,restRun,Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded
      | ok restBytes =>
        simp only [firstRun,restRun,Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded
        cases encoded
        have firstSize := encodeVectorLane_extent ty first firstBytes size typed firstRun
        obtain ⟨restSize,decodedRest⟩ := ih restBytes (fun input member => ready input (List.mem_cons_of_mem first member)) restRun
        refine ⟨by simp only [List.length_append,List.length_cons,firstSize,restSize,Nat.succ_mul]; omega,?_⟩
        simp only [List.length_cons, List.map_cons]
        rw [decodeVectorLanes]
        have take : (firstBytes ++ restBytes).take size = firstBytes := by rw [← firstSize]; exact vector_take_append firstBytes restBytes
        have drop : (firstBytes ++ restBytes).drop size = restBytes := by rw [← firstSize]; exact vector_drop_append firstBytes restBytes
        rw [take,drop,vector_lane_roundtrip ty first firstBytes lane (ready first ((trustIrListMemConsSelf _ _))) firstRun,decodedRest]
        rfl

theorem vector_lane_ready_of_checked (ty : Ty) (lane : VectorReadbackLane ty)
    (ctx : EvalContext) (fuel : Nat) (input : Value)
    (checked : checkClosureValueAt ctx fuel ty input = .ok ()) : VectorLaneReady ty input := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
    cases lane <;> cases input
    all_goals first
      | trivial
      | (simp [VectorLaneReady,checkClosureValueAt,Value.isPoison,Value.isUninit,Ty.isInteger,
          Bind.bind,Except.bind,Pure.pure,Except.pure] at checked ⊢)
    all_goals cases model : ctx.byteModel
    all_goals simp [model,Ty.bitWidthFor,Ty.bitWidthAtModel,Ty.bitWidth,Ty.bitWidthAtPointerBits] at checked ⊢
    all_goals repeat' first | split at checked | (solve | cases checked)
    all_goals simp_all

theorem vector_source_checked (ctx : EvalContext) (fuel count : Nat) (ty : Ty) (input : Value)
    (lane : VectorReadbackLane ty) (checked : checkClosureValueAt ctx fuel (.Vector count ty) input = .ok ()) :
    ∃ values, input = .vector values ∧ values.length = count ∧ count ≠ 0 ∧
      ∀ value ∈ values, VectorLaneReady ty value := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
    cases input with
    | vector values =>
      have run : (if count == 0 || count != values.length then
          Except.error (SemError.typeError "closure value does not match its declared type")
        else values.forM (checkClosureValueAt ctx fuel ty)) = .ok () := checked
      by_cases zero : count = 0
      · simp [zero] at run
      · by_cases census : count = values.length
        · have children : values.forM (checkClosureValueAt ctx fuel ty) = .ok () := by
            have nonempty : values.length ≠ 0 := by omega
            simpa [census,nonempty] using run
          refine ⟨values,rfl,census.symm,zero,?_⟩
          intro value member
          exact vector_lane_ready_of_checked ty lane ctx fuel value
            (SourceValueMembership.forM_checked_member _ _ children value member)
        · simp [zero,census] at run
    | _ => simp [checkClosureValueAt,Value.isPoison,Value.isUninit,Ty.isInteger,
        Bind.bind,Except.bind,Pure.pure,Except.pure] at checked

/-- Success supplies the actual lane list, element size, counts and child run. -/
theorem encodeScalarVectorAt_steps (count : Nat) (ty : Ty) (input : Value) (bytes : List UInt8)
    (encoded : encodeScalarVectorAt count ty input = .ok bytes) :
    ∃ size values, count ≠ 0 ∧ vectorScalarByteSize ty = some size ∧ input = .vector values ∧
      values.length = count ∧ encodeVectorLanes ty values = .ok bytes ∧ bytes.length = count * size := by
  by_cases zero : count = 0
  · simp [encodeScalarVectorAt,zero,Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded
  · cases sizeRow : vectorScalarByteSize ty with
    | none => simp [encodeScalarVectorAt,zero,sizeRow,Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded
    | some size =>
      cases input with
      | vector values =>
        by_cases census : values.length = count
        · simp only [encodeScalarVectorAt,show (count == 0) = false by simp [zero],Bool.false_eq_true,
            ite_false,sizeRow,Bind.bind,Except.bind,Pure.pure,Except.pure,
            show (values.length != count) = false by simp [census]] at encoded
          cases laneRun : encodeVectorLanes ty values with
          | error error => simp [laneRun,Except.bind] at encoded
          | ok actual =>
            simp only [laneRun,Except.bind] at encoded
            split at encoded
            · cases encoded
            · rename_i fits
              cases encoded
              exact ⟨size,values,zero,rfl,rfl,census,laneRun,by simpa using fits⟩
        · simp [encodeScalarVectorAt,zero,sizeRow,census,Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded
      | _ => simp [encodeScalarVectorAt,zero,sizeRow,Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded

/-- The actual supported lane encoder enforces carrier shape and static width. -/
theorem vector_lane_ready_of_encoded (ty : Ty) (lane : VectorReadbackLane ty)
    (input : Value) (bytes : List UInt8) (encoded : encodeVectorLane ty input = .ok bytes) :
    VectorLaneReady ty input := by
  cases lane <;> cases input
  all_goals first
    | trivial
    | (rename_i value; cases nan : value.isNaN <;>
        simp [encodeVectorLane,vectorScalarByteSize,encodeFloatAt,nan,
          Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded)
    | (simp [VectorLaneReady,encodeVectorLane,vectorScalarByteSize,Ty.isInteger,Ty.bitWidth,
        Ty.bitWidthAtPointerBits,encodeFloatAt,Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded ⊢)
  all_goals repeat' first | split at encoded | (solve | cases encoded)
  all_goals simp_all

theorem vector_lanes_ready_of_encoded (ty : Ty) (lane : VectorReadbackLane ty)
    (inputs : List Value) (bytes : List UInt8) (encoded : encodeVectorLanes ty inputs = .ok bytes) :
    ∀ input ∈ inputs, VectorLaneReady ty input := by
  induction inputs generalizing bytes with
  | nil => intro input member; cases member
  | cons first rest ih =>
    rw [encodeVectorLanes] at encoded
    cases firstRun : encodeVectorLane ty first with
    | error error => simp [firstRun,Bind.bind,Except.bind] at encoded
    | ok firstBytes =>
      cases restRun : encodeVectorLanes ty rest with
      | error error => simp [firstRun,restRun,Bind.bind,Except.bind] at encoded
      | ok restBytes =>
        intro input member
        cases member with
        | head => exact vector_lane_ready_of_encoded ty lane first firstBytes firstRun
        | tail _ present => exact ih restBytes restRun input present

/-- Every successful supported vector store has exact logical readback. -/
theorem vector_codec_readback_of_encoded (count : Nat) (ty : Ty) (input : Value) (bytes : List UInt8)
    (lane : VectorReadbackLane ty) (encoded : encodeScalarVectorAt count ty input = .ok bytes) :
    ∃ values, input = .vector values ∧ values.length = count ∧
      (∀ value ∈ values, VectorLaneReady ty value) ∧
      decodeScalarVectorAt count ty bytes = .ok (.vector (values.map vectorLaneResult)) := by
  obtain ⟨size,values,nonzero,sizeRow,rfl,census,run,extent⟩ := encodeScalarVectorAt_steps count ty input bytes encoded
  have ready := vector_lanes_ready_of_encoded ty lane values bytes run
  obtain ⟨_length,decoded⟩ := vector_lanes_roundtrip ty values bytes size lane sizeRow ready run
  refine ⟨values,rfl,census,ready,?_⟩
  have nonempty : values.length ≠ 0 := by omega
  simp [decodeScalarVectorAt,nonzero,nonempty,sizeRow,extent,← census,decoded,Bind.bind,Except.bind,Pure.pure,Except.pure]

/-- Packed logical readback from the actual value checker and successful codec. -/
theorem checked_vector_codec_readback (ctx : EvalContext) (fuel count : Nat) (ty : Ty) (input : Value)
    (lane : VectorReadbackLane ty) (bytes : List UInt8)
    (checked : checkClosureValueAt ctx fuel (.Vector count ty) input = .ok ())
    (encoded : encodeScalarVectorAt count ty input = .ok bytes) :
    ∃ values, input = .vector values ∧ values.length = count ∧
      decodeScalarVectorAt count ty bytes = .ok (.vector (values.map vectorLaneResult)) := by
  obtain ⟨values,rfl,census,nonzero,ready⟩ := vector_source_checked ctx fuel count ty input lane checked
  obtain ⟨size,actual,_positive,sizeRow,shape,_actualCount,run,extent⟩ := encodeScalarVectorAt_steps count ty (.vector values) bytes encoded
  cases shape
  obtain ⟨_length,decoded⟩ := vector_lanes_roundtrip ty values bytes size lane sizeRow ready run
  refine ⟨values,rfl,census,?_⟩
  have nonempty : values.length ≠ 0 := by omega
  simp [decodeScalarVectorAt,nonzero,nonempty,sizeRow,extent,← census,decoded,Bind.bind,Except.bind,Pure.pure,Except.pure]

theorem checked_immediate_vector_shape (model : ByteModel) (count : Nat) (ty : Ty) (input : Value)
    (checked : checkAggregateLane model (.Vector count ty) input = .ok ()) :
    ∃ values, input = .vector values := by
  cases input with
  | vector values => exact ⟨values,rfl⟩
  | _ => simp [checkAggregateLane,Value.isPoison,Value.isUninit,
      Bind.bind,Except.bind,Pure.pure,Except.pure] at checked

end TrustIr
