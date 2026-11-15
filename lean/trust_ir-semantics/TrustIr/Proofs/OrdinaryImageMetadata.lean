-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceCheckedAdmission

namespace TrustIr.AggregateMemory

/-- Ordinary field calls preserve exactly the incoming unwritten records when
    each actual child store contributes no records. Byte overwrites do not
    manufacture lane metadata. -/
theorem FieldsEncoded.unwritten_preserved {model : ByteModel} {order : FunctionAddressOrder}
    {fields : List (Nat × Plan)} {values : List Value} {before after : Image}
    (children : ∀ offset child, (offset,child) ∈ fields → ∀ value image,
      encode model order child value false = .ok image → image.unwritten = [])
    (run : FieldsEncoded model order fields values false before after) :
    after.unwritten = before.unwritten := by
  induction fields generalizing values before with
  | nil =>
    obtain ⟨_,rfl⟩ := FieldsEncoded.nil_iff.mp run
    rfl
  | cons field rest ih =>
    obtain ⟨offset,plan⟩ := field
    obtain ⟨value,later,child,bytes,rfl,encoded,_written,remaining⟩ := run.head
    have empty := children offset plan (by simp) value child encoded
    have tail := ih (by
      intro offset child member
      exact children offset child (List.mem_cons_of_mem _ member)) remaining
    simpa only [empty,List.map_nil,List.append_nil] using tail

/-- A successful ordinary leaf never records an unwritten range. -/
theorem encode_leaf_unwritten_empty (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (value : Value) (image : Image)
    (run : encode model order (.leaf ty layout) value false = .ok image) : image.unwritten = [] := by
  have initialized := encode_ordinary_not_uninit model order (.leaf ty layout) value image run
  rw [encode] at run
  simp only [initialized,Bool.false_eq_true,ite_false,Bind.bind,Except.bind] at run
  split at run
  · cases run
  · simp only [Pure.pure,Except.pure] at run
    split at run
    · cases run
    · split at run
      · cases run
      · cases run
        rfl

/-- Arrays discard child metadata and return their checked byte image. Every
    actual element call is ordinary, independently of the parent store flag. -/
theorem encode_array_unwritten_empty (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (value : Value) (image : Image)
    (run : encode model order (.array ty layout count element) value false = .ok image) :
    image.unwritten = [] := by
  obtain ⟨values,rfl,_census,_encoded⟩ := encode_array_steps model order ty layout count element value image run
  rw [encode] at run
  simp only [Value.isUninit,Bool.false_eq_true,ite_false,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
  repeat' first
    | (solve | cases run; rfl)
    | (solve | contradiction)
    | (simp only [Bind.bind,Except.bind,Pure.pure,Except.pure] at run)
    | split at run

/-- Every successful ordinary aggregate encoding has no explicit unwritten
    ranges. Padding bytes may still be absent; this is a lane-metadata law,
    independent of source typing or layout/readback admissibility. -/
theorem encode_ordinary_unwritten_empty (model : ByteModel) (order : FunctionAddressOrder)
    (plan : Plan) (value : Value) (image : Image)
    (run : encode model order plan value false = .ok image) : image.unwritten = [] := by
  cases plan with
  | leaf ty layout => exact encode_leaf_unwritten_empty model order ty layout value image run
  | fields ty layout fields =>
    obtain ⟨values,rfl,encoded⟩ := encode_fields_steps model order ty layout fields value image run
    apply encoded.unwritten_preserved
    intro offset child _member input stored encoded
    exact encode_ordinary_unwritten_empty model order child input stored encoded
  | array ty layout count element =>
    exact encode_array_unwritten_empty model order ty layout count element value image run
  | enumeration ty layout info variants =>
    have original := run
    have initialized := encode_ordinary_not_uninit model order (.enumeration ty layout info variants) value image run
    rw [encode] at run
    simp only [initialized,Bool.false_eq_true,ite_false,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
    cases value <;> try cases run
    rename_i values
    cases values with
    | nil => cases run
    | cons tag values =>
      obtain ⟨position,bytes,_selection,_prefix,payload,_niche⟩ :=
        encode_enumeration_steps model order ty layout info variants tag values false image original
      obtain ⟨fields,_found,encoded⟩ := payload.fields
      apply encoded.unwritten_preserved
      intro offset child _member input stored encoded
      exact encode_ordinary_unwritten_empty model order child input stored encoded
termination_by sizeOf plan
decreasing_by
  trustIrCompilerProof {
    all_goals simp_wf
    · have inside := List.sizeOf_lt_of_mem _member
      simp_all
      omega
    · have row : some fields ∈ variants := by
        obtain ⟨inside,same⟩ := List.get?_eq_some.mp _found
        exact List.mem_iff_get.mpr ⟨⟨position,inside⟩,same⟩
      have rowSize := List.sizeOf_lt_of_mem row
      have childSize := List.sizeOf_lt_of_mem _member
      simp_all
      omega
  } {
    all_goals simp_wf
    · have inside := List.sizeOf_lt_of_mem _member
      simp_all
      omega
    · have row : some fields ∈ variants := by
        exact CompilerCompat.listGetConstructive_mem _found
      have rowSize := List.sizeOf_lt_of_mem row
      have childSize := List.sizeOf_lt_of_mem _member
      simp_all
      omega
  }

/-- The only whole-value unwritten path retains both the absent bytes and
    the explicit lane record, even for a zero-sized plan. -/
theorem encode_uninit_exact (model : ByteModel) (order : FunctionAddressOrder)
    (plan : Plan) (allowUnwritten : Bool) :
    encode model order plan .uninit allowUnwritten =
      if allowUnwritten then
        .ok { bytes := ByteImage.fill plan.layout.size none, unwritten := [(0,plan.layout.size)] }
      else .error (.ub "memory image: inspecting an unwritten lane") := by
  cases plan <;> cases allowUnwritten <;> rw [encode] <;> rfl

/-- Ordinary successful images cannot register an unwritten lane at any
    destination allocation/address. Existing memory records are retained by
    this registration step; the preceding byte write has its own clipping. -/
theorem encode_ordinary_recordUnwritten (model : ByteModel) (order : FunctionAddressOrder)
    (plan : Plan) (value : Value) (image : Image)
    (run : encode model order plan value false = .ok image)
    (memory : Memory) (allocation : AllocId) (address : Nat) :
    memory.recordUnwritten allocation address image.unwritten = memory := by
  rw [encode_ordinary_unwritten_empty model order plan value image run]
  rfl

end TrustIr.AggregateMemory
