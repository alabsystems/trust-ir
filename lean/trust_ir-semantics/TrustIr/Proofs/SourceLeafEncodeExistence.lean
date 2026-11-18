-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceRecursiveReadback

namespace TrustIr.AggregateMemory
open SourceLayout

/-- A genuine successful composition cannot have started with an encoder error. -/
private theorem encode_exists_of_bind (model : ByteModel) (order : FunctionAddressOrder)
    (plan : Plan) (input : Value) (next : Image → Except SemError Value) (output : Value)
    (passed : (encode model order plan input false).bind next = .ok output) :
    ∃ image, encode model order plan input false = .ok image := by
  cases run : encode model order plan input false with
  | error error => simp [run,Except.bind] at passed
  | ok image => exact ⟨image,rfl⟩

private theorem vector_lane_encode_exists (ty : Ty) (input : Value)
    (lane : VectorReadbackLane ty) (ready : VectorLaneReady ty input) :
    ∃ bytes, encodeVectorLane ty input = .ok bytes := by
  cases input with
  | int width raw =>
      have shape : ty.isInteger = true ∧ ty.bitWidth = some width := by
        cases ty <;> exact ready
      exact ⟨_,vector_integer_lane_bytes ty width raw lane shape.1 shape.2⟩
  | bool value =>
      cases lane <;> try cases ready
      cases value <;> exact ⟨_,rfl⟩
  | _ => cases lane <;> cases ready

/-- Traverse the actual finite supplied lanes, retaining arbitrary integer
residues; no claimed vector encoder success is an input. -/
private theorem vector_lanes_encode_exists (ty : Ty) (lane : VectorReadbackLane ty)
    (laneBytes : Nat) (typed : vectorScalarByteSize ty = some laneBytes) :
    ∀ inputs : List Value, (∀ input ∈ inputs, VectorLaneReady ty input) →
      ∃ bytes, encodeVectorLanes ty inputs = .ok bytes ∧ bytes.length = inputs.length * laneBytes := by
  intro inputs
  induction inputs with
  | nil => intro _; exact ⟨[],rfl,by simp⟩
  | cons first rest ih =>
      intro ready
      obtain ⟨head,headRun⟩ := vector_lane_encode_exists ty first lane (ready first (by simp))
      obtain ⟨tail,tailRun,tailSize⟩ := ih (by
        intro input member
        exact ready input (List.mem_cons_of_mem first member))
      refine ⟨head ++ tail,?_,?_⟩
      · simp only [encodeVectorLanes,headRun,tailRun,Bind.bind,Except.bind,Pure.pure,Except.pure]
      · rw [List.length_append,encodeVectorLane_extent ty first head laneBytes typed headRun,tailSize]
        simpa only [List.length_cons,Nat.succ_mul] using
          (Nat.add_comm laneBytes (rest.length * laneBytes))

/-- Every constructor of the existing scalar readback domain constructs an
actual successful store. Char remains a raw32-bit nested carrier; no Unicode
or canonical-integer-value premise is added to this store theorem. -/
theorem ScalarReadbackInput.encode_exists {model : ByteModel} {plan : Plan} {input : Value}
    (admitted : ScalarReadbackInput model plan input) (order : FunctionAddressOrder) :
    ∃ image, encode model order plan input false = .ok image := by
  cases admitted with
  | integer ty layout width raw integer typed extent =>
      let bytes := encodeIntBytes (truncateUnsigned raw width) (width / 8)
      refine ⟨{ bytes := ByteImage.ofList (bytes.map some) },?_⟩
      exact encode_integer_leaf_of_memory model order ty layout width raw _ integer typed
        ((encodeIntBytes_length _ _).trans extent.symm)
        (encodeMemory_integer_residue model order ty width raw integer)
  | boolean value =>
      exact encode_exists_of_bind model order _ _ _ _
        (boolean_aggregate_leaf_roundtrip model order Memory.empty value)
  | vector count ty layout inputs lane laneBytes typed nonzero census extent ready =>
      obtain ⟨bytes,lanesRun,byteCount⟩ := vector_lanes_encode_exists ty lane laneBytes typed inputs ready
      have countBytes : bytes.length = count * laneBytes := byteCount.trans (congrArg (fun n => n * laneBytes) census)
      have encoded : encodeScalarVectorAt count ty (.vector inputs) = .ok bytes := by
        simp [encodeScalarVectorAt,nonzero,typed,census,lanesRun,countBytes,
          Bind.bind,Except.bind,Pure.pure,Except.pure]
      refine ⟨{ bytes := ByteImage.ofList (bytes.map some) },?_⟩
      exact encode_vector_leaf_of_scalar model order count ty layout inputs bytes encoded
        (countBytes.trans extent.symm)
  | unit =>
      have codec : (encode model order (.leaf .Unit ⟨0,1⟩) (.aggregate []) false).bind
          (fun image => decode model order Memory.empty (.leaf .Unit ⟨0,1⟩) image.bytes) = .ok (.aggregate []) := by
        cases model <;> trustIrReduce
      exact encode_exists_of_bind model order _ _ _ _ codec
  | pointer ty layout address provenance pointer bound extent =>
      exact encode_exists_of_bind model order _ _ _ _
        (pointer_aggregate_leaf_roundtrip model order Memory.empty ty layout address provenance pointer bound extent)
  | null ty layout pointer extent =>
      exact encode_exists_of_bind model order _ _ _ _
        (null_pointer_aggregate_leaf_roundtrip model order Memory.empty ty layout pointer extent)
  | fatLength kind layout data provenance raw lengthLane bound extent =>
      exact encode_exists_of_bind model order _ _ _ _
        (fat_length_aggregate_leaf_roundtrip model order Memory.empty kind layout data provenance raw lengthLane bound extent)
  | fatVtable kind layout data metadata dataProv metadataProv pointerLane dataBound metaBound extent =>
      exact encode_exists_of_bind model order _ _ _ _
        (fat_vtable_aggregate_leaf_roundtrip model order Memory.empty kind layout data metadata dataProv metadataProv
          pointerLane dataBound metaBound extent)
  | fatNull kind layout data provenance pointerLane bound extent =>
      exact encode_exists_of_bind model order _ _ _ _
        (fat_null_vtable_aggregate_leaf_roundtrip model order Memory.empty kind layout data provenance pointerLane bound extent)

/-- Registered and null function-word inputs construct real successful images;
this neither changes nominal function-item semantics nor grants call authority. -/
theorem FunctionReadbackInput.encode_exists {model : ByteModel} {order : FunctionAddressOrder}
    {plan : Plan} {input : Value} (admitted : FunctionReadbackInput model order plan input) :
    ∃ image, encode model order plan input false = .ok image :=
  encode_exists_of_bind model order plan input _ input (admitted.codec Memory.empty)

/-- Prepared scalar and function-word inputs construct their stored image and
    read it back. The caller supplies neither bytes nor successful encoding.
    Nested Char carriers retain their raw-word policy. -/
theorem prepared_leaf_store_child_readback (source : Environment) (roots : List Ty)
    (ty : Ty) (plan : Plan) (prepared : (prepare source roots).query ty = .ok plan)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) (input : Value)
    (admitted : ScalarReadbackInput model plan input ∨ FunctionReadbackInput model order plan input) :
    ∃ image output, encode model order plan input false = .ok image ∧
      ChildDecoded model order memory plan image.bytes output ∧ ValueReadback model memory input output := by
  have existsImage : ∃ image, encode model order plan input false = .ok image := by
    rcases admitted with scalar | function
    · exact scalar.encode_exists order
    · exact function.encode_exists
  obtain ⟨image,encoded⟩ := existsImage
  have ready : ReadbackInput model order memory plan input := by
    rcases admitted with scalar | function
    · exact .scalar scalar
    · exact .function function
  obtain ⟨output,decoded,related⟩ :=
    prepared_recursive_child_readback source roots ty plan prepared model order memory input ready image encoded
  exact ⟨image,output,encoded,decoded,related⟩

namespace LeafStoreExistenceControls

/-- Negative literals remain supported without a canonical-value premise. -/
theorem negative_integer_child (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) :
    ∃ image, encode model order (.leaf .I8 ⟨1,1⟩) (.int 8 (-1)) false = .ok image ∧
      ChildDecoded model order memory (.leaf .I8 ⟨1,1⟩) image.bytes (Value.intAt 8 (-1)) := by
  have admitted : ScalarReadbackInput model (.leaf .I8 ⟨1,1⟩) (.int 8 (-1)) :=
    .integer .I8 ⟨1,1⟩ 8 (-1) rfl (by cases model <;> rfl) rfl
  obtain ⟨image,encoded⟩ := admitted.encode_exists order
  refine ⟨image,encoded,?_⟩
  exact integer_child_readback_of_encoded model order memory .I8 ⟨1,1⟩ 8 (-1) rfl
    (by cases model <;> rfl) rfl image image.bytes encoded
    (encode_extent model order (.leaf .I8 ⟨1,1⟩) (.int 8 (-1)) false image encoded) (fun _ => rfl)

/-- A Unicode surrogate remains supported as a raw nested Char carrier. -/
theorem surrogate_child (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) :
    ∃ image, encode model order (.leaf .Char ⟨4,4⟩) (.int 32 55296) false = .ok image ∧
      ChildDecoded model order memory (.leaf .Char ⟨4,4⟩) image.bytes (Value.intAt 32 55296) := by
  have admitted : ScalarReadbackInput model (.leaf .Char ⟨4,4⟩) (.int 32 55296) :=
    .integer .Char ⟨4,4⟩ 32 55296 rfl (by cases model <;> rfl) rfl
  obtain ⟨image,encoded⟩ := admitted.encode_exists order
  refine ⟨image,encoded,?_⟩
  exact integer_child_readback_of_encoded model order memory .Char ⟨4,4⟩ 32 55296 rfl
    (by cases model <;> rfl) rfl image image.bytes encoded
    (encode_extent model order (.leaf .Char ⟨4,4⟩) (.int 32 55296) false image encoded) (fun _ => rfl)

end LeafStoreExistenceControls
end TrustIr.AggregateMemory

-- New subjects admit only the Lean-core axiom ceiling. The audit logs retain
-- each compiler's actual dependency list; existing exact audits are unchanged.
#trustIrAxioms TrustIr.AggregateMemory.ImageOverwrite.exists_of_fits <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.AggregateMemory.encode_fields_of_components <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.AggregateMemory.FieldsEncoded.exists_of_children <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.AggregateMemory.encode_fields_exists_of_children <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.AggregateMemory.encode_vector_leaf_of_scalar <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.AggregateMemory.ScalarReadbackInput.encode_exists <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.AggregateMemory.FunctionReadbackInput.encode_exists <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.AggregateMemory.prepared_leaf_store_child_readback <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.AggregateMemory.LeafStoreExistenceControls.negative_integer_child <= [propext, Classical.choice, Quot.sound]
#trustIrAxioms TrustIr.AggregateMemory.LeafStoreExistenceControls.surrogate_child <= [propext, Classical.choice, Quot.sound]
