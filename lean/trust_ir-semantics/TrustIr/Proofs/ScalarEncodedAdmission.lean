-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.FunctionEncodedAdmission

namespace TrustIr.AggregateMemory
open SourceLayout

/-- The actual immediate aggregate-lane checker authenticates integer carrier
    shape and declared width, including the nested raw Char carrier. -/
theorem checked_integer_lane_shape (model : ByteModel) (ty : Ty) (input : Value)
    (integer : ty.isInteger = true) (checked : checkAggregateLane model ty input = .ok ()) :
    ∃ width raw, input = .int width raw ∧ ty.bitWidthFor model = some width := by
  cases ty <;> simp only [Ty.isInteger] at integer <;> try cases integer
  all_goals cases input <;> simp [checkAggregateLane,Value.isPoison,Value.isUninit,Bind.bind,Except.bind,Pure.pure,Except.pure] at checked
  all_goals try cases checked
  all_goals exact ⟨_,_,rfl,by cases model <;> rfl⟩

theorem checked_pointer_lane_shape (model : ByteModel) (ty : Ty) (input : Value)
    (pointer : ty.isPointerLike = true) (checked : checkAggregateLane model ty input = .ok ()) :
    (∃ address provenance, input = .ptr address provenance) ∨ input = .nullPtr := by
  cases ty <;> simp only [Ty.isPointerLike,Ty.isReference] at pointer <;> try cases pointer
  all_goals cases input <;> simp [checkAggregateLane,Value.isPoison,Value.isUninit,Bind.bind,Except.bind,Pure.pure,Except.pure] at checked
  all_goals try cases checked
  all_goals first | exact Or.inl ⟨_,_,rfl⟩ | exact Or.inr rfl

theorem ScalarReadbackInput.integer_of_checked_encoded (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (input : Value) (stored : Image)
    (integer : ty.isInteger = true) (checked : checkAggregateLane model ty input = .ok ())
    (encoded : encode model order (.leaf ty layout) input false = .ok stored) :
    ScalarReadbackInput model (.leaf ty layout) input := by
  obtain ⟨width,raw,shape,typed⟩ := checked_integer_lane_shape model ty input integer checked
  subst input
  obtain ⟨bytes,memoryRun,size,imageShape⟩ := encode_leaf_memory_success model order ty layout (.int width raw) stored encoded
  rw [encodeMemory_integer_residue model order ty width raw integer] at memoryRun
  have byteShape := Except.ok.inj memoryRun
  exact .integer ty layout width raw integer typed (by rw [← size,← byteShape,encodeIntBytes_length])

theorem ScalarReadbackInput.pointer_of_checked_encoded (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (input : Value) (stored : Image)
    (pointer : ty.isPointerLike = true) (checked : checkAggregateLane model ty input = .ok ())
    (encoded : encode model order (.leaf ty layout) input false = .ok stored) :
    ScalarReadbackInput model (.leaf ty layout) input := by
  obtain ⟨bytes,memoryRun,size,imageShape⟩ := encode_leaf_memory_success model order ty layout input stored encoded
  rcases checked_pointer_lane_shape model ty input pointer checked with ⟨address,provenance,rfl⟩ | rfl
  · have direct : encodeMemoryAt model ty (.ptr address provenance) = .ok bytes := by
      cases ty <;> simp only [Ty.isPointerLike,Ty.isReference] at pointer <;> try cases pointer
      all_goals exact memoryRun
    have bound := encodeMemoryAt_pointer_address_bound model ty address provenance bytes direct
    rw [encodeMemory_pointer_word model order ty address provenance pointer bound] at memoryRun
    have byteShape := Except.ok.inj memoryRun
    exact .pointer ty layout address provenance pointer bound (by rw [← size,← byteShape,encodeIntBytes_length])
  · have nullEncoded : encodeMemoryWithFunctions model order ty .nullPtr = .ok (List.replicate model.pointerBytes 0) := by
      cases model <;> cases ty <;> simp only [Ty.isPointerLike,Ty.isReference] at pointer <;> try cases pointer
      all_goals rfl
    rw [nullEncoded] at memoryRun
    have byteShape := Except.ok.inj memoryRun
    exact .null ty layout pointer (by rw [← size,← byteShape,List.length_replicate])

theorem ScalarReadbackInput.boolean_of_checked (model : ByteModel) (input : Value)
    (checked : checkAggregateLane model .Bool input = .ok ()) :
    ScalarReadbackInput model (.leaf .Bool ⟨1,1⟩) input := by
  cases input <;> simp [checkAggregateLane,Value.isPoison,Value.isUninit,Bind.bind,Except.bind,Pure.pure,Except.pure] at checked
  all_goals try cases checked
  exact .boolean _

theorem ScalarReadbackInput.unit_of_checked (model : ByteModel) (input : Value)
    (checked : checkAggregateLane model .Unit input = .ok ()) :
    ScalarReadbackInput model (.leaf .Unit ⟨0,1⟩) input := by
  cases input <;> try cases checked
  rename_i values
  cases values with
  | nil => exact .unit
  | cons value rest => cases checked

theorem metadata_length64_shape (metadata : Value) (valid : metadataInhabits .U64 metadata = true) :
    ∃ raw, metadata = .int 64 raw := by
  cases metadata <;> try cases valid
  rename_i width raw
  by_cases same : width = 64
  · subst width; exact ⟨raw,rfl⟩
  · simp [metadataInhabits,same] at valid

theorem metadata_length32_shape (metadata : Value) (valid : metadataInhabitsAtModel .le32 .U32 metadata = true) :
    ∃ raw, metadata = .int 32 raw := by
  cases metadata <;> try cases valid
  rename_i width raw
  by_cases same : width = 32
  · subst width; exact ⟨raw,rfl⟩
  · simp [metadataInhabitsAtModel,same] at valid

theorem metadata_pointer64_shape (metadata : Value) (valid : metadataInhabits .Ptr metadata = true) :
    (∃ address provenance, metadata = .ptr address provenance) ∨ metadata = .nullPtr := by
  cases metadata <;> try cases valid
  all_goals first | exact Or.inl ⟨_,_,rfl⟩ | exact Or.inr rfl

theorem metadata_pointer32_shape (metadata : Value) (valid : metadataInhabitsAtModel .le32 .Ptr metadata = true) :
    (∃ address provenance, metadata = .ptr address provenance) ∨ metadata = .nullPtr := by
  cases metadata <;> try cases valid
  all_goals first | exact Or.inl ⟨_,_,rfl⟩ | exact Or.inr rfl

/-- The actual metadata predicate determines both kind and target-width carrier. -/
theorem checked_fat_metadata_shape (model : ByteModel) (kind : FatPtrKind) (metadata : Value)
    (valid : metadataInhabitsFor model kind metadata = true) :
    (∃ raw, metadata = .int model.pointerBits raw ∧ kind.metadataTy = .U64) ∨
      (kind.metadataTy = .Ptr ∧ ((∃ address provenance, metadata = .ptr address provenance) ∨ metadata = .nullPtr)) := by
  cases model <;> cases kind
  all_goals first
    | (obtain ⟨raw,rfl⟩ := metadata_length64_shape metadata valid; exact Or.inl ⟨raw,rfl,rfl⟩)
    | (obtain ⟨raw,rfl⟩ := metadata_length32_shape metadata valid; exact Or.inl ⟨raw,rfl,rfl⟩)
    | exact Or.inr ⟨rfl,metadata_pointer64_shape metadata valid⟩
    | exact Or.inr ⟨rfl,metadata_pointer32_shape metadata valid⟩

theorem fat_store_guard_shape (model : ByteModel) (kind : FatPtrKind) (input : Value)
    (valid : fatPtrStoreValueValidFor model (.FatPtr kind) input = true) :
    ∃ data provenance metadata, input = .fatPtr data provenance metadata := by
  cases input <;> cases model <;> try cases valid
  all_goals exact ⟨_,_,_,rfl⟩

theorem ScalarReadbackInput.fat_of_encoded (model : ByteModel) (order : FunctionAddressOrder)
    (kind : FatPtrKind) (layout : MemoryTypeLayout) (input : Value) (stored : Image)
    (encoded : encode model order (.leaf (.FatPtr kind) layout) input false = .ok stored) :
    ScalarReadbackInput model (.leaf (.FatPtr kind) layout) input := by
  trustIrCompilerProof {
    have valid := encode_leaf_fat_valid model order (.FatPtr kind) layout input stored encoded
    obtain ⟨data,provenance,metadata,shape⟩ := fat_store_guard_shape model kind input valid
    subst input
    obtain ⟨bytes,memoryRun,size,imageShape⟩ := encode_leaf_memory_success model order (.FatPtr kind) layout _ stored encoded
    have dataBound : data < model.addressLimit := by
      by_cases bound : data < model.addressLimit
      · exact bound
      · rw [fat_pointer_memory_refuses_data model order kind data provenance metadata bound] at memoryRun
        cases memoryRun
    have metadataGuard : metadataInhabitsFor model kind metadata = true := by
      cases model with
      | le64 => exact valid
      | le32 => exact ((Bool.and_eq_true_iff _ _).mp valid).2
    rcases checked_fat_metadata_shape model kind metadata metadataGuard with
      ⟨raw,rfl,lengthLane⟩ | ⟨pointerLane,⟨address,metadataProvenance,rfl⟩ | rfl⟩
    · rw [encodeMemory_fat_length_words model order kind data provenance raw lengthLane dataBound] at memoryRun
      have lengths := congrArg List.length (Except.ok.inj memoryRun)
      simp only [List.length_append,encodeIntBytes_length] at lengths
      exact .fatLength kind layout data provenance raw lengthLane dataBound (by omega)
    · have direct : encodeMemoryAt model (.FatPtr kind) (.fatPtr data provenance (.ptr address metadataProvenance)) = .ok bytes := memoryRun
      have metadataBound := (encodeMemoryAt_fat_pointer_address_bounds model (.FatPtr kind) data address provenance metadataProvenance bytes direct).2
      rw [encodeMemory_fat_vtable_words model order kind data address provenance metadataProvenance pointerLane dataBound metadataBound] at memoryRun
      have lengths := congrArg List.length (Except.ok.inj memoryRun)
      simp only [List.length_append,encodeIntBytes_length] at lengths
      exact .fatVtable kind layout data address provenance metadataProvenance pointerLane dataBound metadataBound (by omega)
    · rw [fat_null_metadata_image,encodeMemory_fat_vtable_words model order kind data 0 provenance none pointerLane dataBound
        (by cases model <;> decide)] at memoryRun
      have lengths := congrArg List.length (Except.ok.inj memoryRun)
      simp only [List.length_append,encodeIntBytes_length] at lengths
      exact .fatNull kind layout data provenance pointerLane dataBound (by omega)
  } {
    have valid := encode_leaf_fat_valid model order (.FatPtr kind) layout input stored encoded
    obtain ⟨data,provenance,metadata,shape⟩ := fat_store_guard_shape model kind input valid
    subst input
    obtain ⟨bytes,memoryRun,size,imageShape⟩ := encode_leaf_memory_success model order (.FatPtr kind) layout _ stored encoded
    have dataBound : data < model.addressLimit := by
      by_cases bound : data < model.addressLimit
      · exact bound
      · rw [fat_pointer_memory_refuses_data model order kind data provenance metadata bound] at memoryRun
        cases memoryRun
    have metadataGuard : metadataInhabitsFor model kind metadata = true := by
      cases model with
      | le64 => exact valid
      | le32 => exact (Bool.and_eq_true_iff.mp valid).2
    rcases checked_fat_metadata_shape model kind metadata metadataGuard with
      ⟨raw,rfl,lengthLane⟩ | ⟨pointerLane,⟨address,metadataProvenance,rfl⟩ | rfl⟩
    · rw [encodeMemory_fat_length_words model order kind data provenance raw lengthLane dataBound] at memoryRun
      have lengths := congrArg List.length (Except.ok.inj memoryRun)
      simp only [List.length_append,encodeIntBytes_length] at lengths
      exact .fatLength kind layout data provenance raw lengthLane dataBound (by omega)
    · have direct : encodeMemoryAt model (.FatPtr kind) (.fatPtr data provenance (.ptr address metadataProvenance)) = .ok bytes := memoryRun
      have metadataBound := (encodeMemoryAt_fat_pointer_address_bounds model (.FatPtr kind) data address provenance metadataProvenance bytes direct).2
      rw [encodeMemory_fat_vtable_words model order kind data address provenance metadataProvenance pointerLane dataBound metadataBound] at memoryRun
      have lengths := congrArg List.length (Except.ok.inj memoryRun)
      simp only [List.length_append,encodeIntBytes_length] at lengths
      exact .fatVtable kind layout data address provenance metadataProvenance pointerLane dataBound metadataBound (by omega)
    · rw [fat_null_metadata_image,encodeMemory_fat_vtable_words model order kind data 0 provenance none pointerLane dataBound
        (by cases model <;> decide)] at memoryRun
      have lengths := congrArg List.length (Except.ok.inj memoryRun)
      simp only [List.length_append,encodeIntBytes_length] at lengths
      exact .fatNull kind layout data provenance pointerLane dataBound (by omega)
  }

/-- Plan-side scalar families whose actual lane check and successful store
    supply readback admission. Bool/Unit retain canonical source layouts. -/
inductive ScalarReadbackPlan : Plan → Prop where
  | integer (ty : Ty) (layout : MemoryTypeLayout) (integer : ty.isInteger = true) : ScalarReadbackPlan (.leaf ty layout)
  | pointer (ty : Ty) (layout : MemoryTypeLayout) (pointer : ty.isPointerLike = true) : ScalarReadbackPlan (.leaf ty layout)
  | boolean : ScalarReadbackPlan (.leaf .Bool ⟨1,1⟩)
  | unit : ScalarReadbackPlan (.leaf .Unit ⟨0,1⟩)
  | fat (kind : FatPtrKind) (layout : MemoryTypeLayout) : ScalarReadbackPlan (.leaf (.FatPtr kind) layout)
  | vector (count : Nat) (ty : Ty) (layout : MemoryTypeLayout) (lane : VectorReadbackLane ty)
      (nonzero : count ≠ 0) : ScalarReadbackPlan (.leaf (.Vector count ty) layout)
  | function (signature : FuncTyId) (layout : MemoryTypeLayout) : ScalarReadbackPlan (.leaf (.Func signature) layout)

theorem ScalarReadbackPlan.input_certificate {plan : Plan} (shape : ScalarReadbackPlan plan)
    (model : ByteModel) (order : FunctionAddressOrder) (input : Value) (stored : Image)
    (checked : checkAggregateLane model plan.ty input = .ok ())
    (encoded : encode model order plan input false = .ok stored) :
    ScalarReadbackInput model plan input ∨ FunctionReadbackInput model order plan input := by
  cases shape with
  | integer ty layout integer => exact Or.inl (.integer_of_checked_encoded model order ty layout input stored integer checked encoded)
  | pointer ty layout pointer => exact Or.inl (.pointer_of_checked_encoded model order ty layout input stored pointer checked encoded)
  | boolean => exact Or.inl (.boolean_of_checked model input checked)
  | unit => exact Or.inl (.unit_of_checked model input checked)
  | fat kind layout => exact Or.inl (.fat_of_encoded model order kind layout input stored encoded)
  | vector count ty layout lane _nonzero =>
    obtain ⟨values,rfl⟩ := checked_immediate_vector_shape model count ty input checked
    obtain ⟨size,typed,positive,census,extent,ready⟩ := vector_leaf_admission_of_encoded model order count ty layout values lane stored encoded
    exact Or.inl (.vector count ty layout values lane size typed positive census extent ready)
  | function signature layout => exact Or.inr (.of_encoded model order signature layout input stored encoded)

theorem ScalarReadbackPlan.admit {plan : Plan} (shape : ScalarReadbackPlan plan)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) (input : Value) (stored : Image)
    (checked : checkAggregateLane model plan.ty input = .ok ())
    (encoded : encode model order plan input false = .ok stored) :
    ReadbackInput model order memory plan input := by
  rcases shape.input_certificate model order input stored checked encoded with scalar | function
  · exact .scalar scalar
  · exact .function function

theorem ScalarReadbackPlan.readback {plan : Plan} (shape : ScalarReadbackPlan plan)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) (input : Value) (stored : Image)
    (checked : checkAggregateLane model plan.ty input = .ok ())
    (encoded : encode model order plan input false = .ok stored)
    (loaded : ByteImage) (extent : loaded.size = plan.layout.size)
    (bytes : ∀ index, loaded.get index = stored.bytes.get index) (character : TopCharReady plan input) :
    ∃ output, decode model order memory plan loaded = .ok output ∧ ValueReadback model memory input output := by
  rcases shape.input_certificate model order input stored checked encoded with scalar | function
  · exact scalar.top_readback order memory stored loaded encoded extent bytes character
  · cases function with
    | registered ids signature target index layout lookup bounded size =>
      exact ⟨_,encoded_function_readback model (some ids) memory signature layout _ stored encoded loaded extent bytes⟩
    | null order signature layout size =>
      exact ⟨_,encoded_function_readback model order memory signature layout _ stored encoded loaded extent bytes⟩

/-- The real recursive value checker supplies ordinary Char readiness; the
    immediate aggregate-lane checker alone intentionally does not. -/
theorem top_char_ready_of_checked_closure (ctx : EvalContext) (fuel : Nat) (plan : Plan) (input : Value)
    (checked : checkClosureValueAt ctx fuel plan.ty input = .ok ()) : TopCharReady plan input := by
  intro layout width raw planShape inputShape
  subst plan input
  cases fuel with
  | zero => cases checked
  | succ fuel =>
    change (if width != 32 then Except.error (SemError.typeError "closure value does not match its declared type")
      else if raw < 0 || !(decide (validChar raw.toNat)) then
        Except.error (SemError.ub "closure boundary: invalid Unicode scalar value")
      else Except.ok ()) = Except.ok () at checked
    by_cases typed : width = 32
    · subst width
      by_cases nonnegative : 0 ≤ raw
      · have notNegative : ¬ raw < 0 := by omega
        by_cases valid : validChar raw.toNat
        · have charBound : Int.ofNat raw.toNat < Int.ofNat 1114112 := Int.ofNat_lt.mpr valid.1
          have natural : Int.ofNat raw.toNat = raw := Int.toNat_of_nonneg nonnegative
          rw [natural] at charBound
          change raw < 1114112 at charBound
          clear natural
          have bound : raw < 2 ^ 32 := by change raw < 4294967296; omega
          rw [truncateUnsigned_of_residue nonnegative bound]
          exact valid
        · simp [notNegative,valid] at checked
      · have negative : raw < 0 := by omega
        simp [negative] at checked
    · simp [typed] at checked

/-- Real recursive Char validation discharges ordinary readiness. The immediate
    lane check and successful store still supply the distinct admission facts. -/
theorem ScalarReadbackPlan.readback_of_checked_closure {plan : Plan} (shape : ScalarReadbackPlan plan)
    (ctx : EvalContext) (fuel : Nat) (order : FunctionAddressOrder) (memory : Memory) (input : Value) (stored : Image)
    (lane : checkAggregateLane ctx.byteModel plan.ty input = .ok ())
    (checked : checkClosureValueAt ctx fuel plan.ty input = .ok ())
    (encoded : encode ctx.byteModel order plan input false = .ok stored)
    (loaded : ByteImage) (extent : loaded.size = plan.layout.size)
    (bytes : ∀ index, loaded.get index = stored.bytes.get index) :
    ∃ output, decode ctx.byteModel order memory plan loaded = .ok output ∧ ValueReadback ctx.byteModel memory input output :=
  shape.readback ctx.byteModel order memory input stored lane encoded loaded extent bytes
    (top_char_ready_of_checked_closure ctx fuel plan input checked)

end TrustIr.AggregateMemory
