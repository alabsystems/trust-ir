-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceRecursiveReadback

namespace TrustIr.AggregateMemory
open SourceLayout

/-- A successful contextual lookup authenticates the actual first-match table
    position and address bound. Numeric function ids are not code addresses. -/
theorem functionAddressOf_success (model : ByteModel) (order : FunctionAddressOrder)
    (target : FuncId) (address : Nat) (run : functionAddressOf model order target = .ok address) :
    ∃ ids index, order = some ids ∧ functionAddressIndex target ids = some index ∧
      index + 1 < model.addressLimit ∧ address = index + 1 := by
  cases order with
  | none => simp [functionAddressOf,Bind.bind,Except.bind] at run
  | some ids =>
    cases lookup : functionAddressIndex target ids with
    | none => simp [functionAddressOf,lookup,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
    | some index =>
      by_cases bounded : index + 1 < model.addressLimit
      · have same : index + 1 = address := by
          simpa [functionAddressOf,lookup,checkedFunctionAddress,bounded,Bind.bind,Except.bind,Pure.pure,Except.pure] using run
        exact ⟨ids,index,rfl,lookup,bounded,same.symm⟩
      · simp [functionAddressOf,lookup,checkedFunctionAddress,bounded,Bind.bind,Except.bind,Pure.pure,Except.pure] at run

/-- Function admission is a consequence of the actual successful contextual
    memory encoder and byte extent, not a table certificate supplied by a caller. -/
theorem FunctionReadbackInput.of_memory_success (model : ByteModel) (order : FunctionAddressOrder)
    (signature : FuncTyId) (layout : MemoryTypeLayout) (input : Value) (bytes : List UInt8)
    (run : encodeMemoryWithFunctions model order (.Func signature) input = .ok bytes)
    (extent : bytes.length = layout.size) :
    FunctionReadbackInput model order (.leaf (.Func signature) layout) input := by
  cases input <;> simp only [encodeMemoryWithFunctions] at run <;> try cases run
  case nullPtr =>
    exact .null order signature layout (by simpa using extent.symm)
  case fnDef held target =>
    by_cases same : held = signature
    · subst held
      simp only [if_pos rfl] at run
      cases found : functionAddressOf model order target with
      | error error => simp [found,Bind.bind,Except.bind] at run
      | ok address =>
        have byteShape : encodeIntBytes (Int.ofNat address) model.pointerBytes = bytes := by
          simpa [found,Bind.bind,Except.bind,Pure.pure,Except.pure] using run
        obtain ⟨ids,index,orderShape,lookup,bounded,addressShape⟩ := functionAddressOf_success model order target address found
        subst order
        exact .registered ids signature target index layout lookup bounded
          (by rw [← extent,← byteShape,encodeIntBytes_length])
    · simp [same] at run

theorem FunctionReadbackInput.of_encoded (model : ByteModel) (order : FunctionAddressOrder)
    (signature : FuncTyId) (layout : MemoryTypeLayout) (input : Value) (stored : Image)
    (encoded : encode model order (.leaf (.Func signature) layout) input false = .ok stored) :
    FunctionReadbackInput model order (.leaf (.Func signature) layout) input := by
  obtain ⟨bytes,memoryRun,extent,imageShape⟩ := encode_leaf_memory_success model order (.Func signature) layout input stored encoded
  exact .of_memory_success model order signature layout input bytes memoryRun extent

theorem ReadbackInput.function_of_encoded (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (signature : FuncTyId) (layout : MemoryTypeLayout) (input : Value) (stored : Image)
    (encoded : encode model order (.leaf (.Func signature) layout) input false = .ok stored) :
    ReadbackInput model order memory (.leaf (.Func signature) layout) input :=
  .function (.of_encoded model order signature layout input stored encoded)

/-- Successful ordinary function storage alone discharges contextual admission;
    every complete image with the same observations decodes to the actual input. -/
theorem encoded_function_readback (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (signature : FuncTyId) (layout : MemoryTypeLayout) (input : Value) (stored : Image)
    (encoded : encode model order (.leaf (.Func signature) layout) input false = .ok stored)
    (loaded : ByteImage) (extent : loaded.size = layout.size) (bytes : ∀ index, loaded.get index = stored.bytes.get index) :
    decode model order memory (.leaf (.Func signature) layout) loaded = .ok input ∧
      ValueReadback model memory input input := by
  have admitted := FunctionReadbackInput.of_encoded model order signature layout input stored encoded
  have codec := admitted.codec memory
  rw [encoded] at codec
  have run : decode model order memory (.leaf (.Func signature) layout) stored.bytes = .ok input := codec
  refine ⟨?_,?_⟩
  · exact (decode_leaf_eq_of_observations model order memory (.Func signature) layout loaded stored.bytes
      (extent.trans (encode_extent model order (.leaf (.Func signature) layout) input false stored encoded).symm) bytes).trans run
  · cases admitted with
    | registered ids signature target index layout lookup bounded extent => exact .function signature target
    | null order signature layout extent => exact .null

/-- Successful field traversal supplies every actual child store, so admission
    can be assembled from child store laws without caller-supplied value pairs. -/
theorem FieldsEncoded.readback_inputs {model : ByteModel} {order : FunctionAddressOrder} {memory : Memory}
    {fields : List (Nat × Plan)} {inputs : List Value} {before after : Image}
    (run : FieldsEncoded model order fields inputs false before after)
    (children : ∀ offset child, (offset,child) ∈ fields → ∀ input stored,
      encode model order child input false = .ok stored → ReadbackInput model order memory child input) :
    FieldReadbackInputs model order memory fields inputs := by
  induction fields generalizing inputs before with
  | nil =>
    obtain ⟨empty,same⟩ := FieldsEncoded.nil_iff.mp run
    subst inputs
    exact .nil
  | cons pair rest ih =>
    obtain ⟨offset,child⟩ := pair
    obtain ⟨input,later,stored,bytes,shape,encoded,written,suffix⟩ := run.head
    subst inputs
    exact .cons (children offset child (.head _) input stored encoded)
      (ih suffix (fun offset child member => children offset child (.tail _ member)))

theorem ReadbackInput.fields_of_encoded (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan)) (input : Value) (stored : Image)
    (encoded : encode model order (.fields ty layout fields) input false = .ok stored)
    (children : ∀ offset child, (offset,child) ∈ fields → ∀ input stored,
      encode model order child input false = .ok stored → ReadbackInput model order memory child input) :
    ReadbackInput model order memory (.fields ty layout fields) input := by
  obtain ⟨inputs,shape,run⟩ := encode_fields_steps model order ty layout fields input stored encoded
  subst input
  exact .fields_of_pairs ty layout fields inputs (run.readback_inputs children)

theorem ReadbackInput.array_of_encoded (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan) (input : Value) (stored : Image)
    (encoded : encode model order (.array ty layout count element) input false = .ok stored)
    (child : ∀ input stored, encode model order element input false = .ok stored → ReadbackInput model order memory element input) :
    ReadbackInput model order memory (.array ty layout count element) input := by
  obtain ⟨inputs,shape,census,run⟩ := encode_array_steps model order ty layout count element input stored encoded
  subst input
  apply ReadbackInput.array ty layout count element inputs census
  intro position value inside found
  obtain ⟨actual,encodedChild,lane⟩ := encode_array_slot model order ty layout count element inputs stored encoded position value
    (by rw [census]; exact inside) found
  exact child value actual encodedChild

/-- Plan-only admission for recursively stored function words. It imposes no
    separate table, bound, extent, value-shape or child-count certificates;
    successful ordinary storage supplies those. Source geometry is still needed
    by aggregate readback. Other leaf families and enums are separate work. -/
inductive FunctionReadbackPlan : Plan → Prop where
  | function (signature : FuncTyId) (layout : MemoryTypeLayout) : FunctionReadbackPlan (.leaf (.Func signature) layout)
  | fields (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan))
      (children : ∀ offset child, (offset,child) ∈ fields → FunctionReadbackPlan child) :
      FunctionReadbackPlan (.fields ty layout fields)
  | array (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
      (child : FunctionReadbackPlan element) : FunctionReadbackPlan (.array ty layout count element)

theorem FunctionReadbackPlan.admit {plan : Plan} (shape : FunctionReadbackPlan plan)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) :
    ∀ input stored, encode model order plan input false = .ok stored → ReadbackInput model order memory plan input := by
  induction shape with
  | function signature layout => exact ReadbackInput.function_of_encoded model order memory signature layout
  | fields ty layout fields children ih =>
    intro input stored encoded
    exact ReadbackInput.fields_of_encoded model order memory ty layout fields input stored encoded ih
  | array ty layout count element child ih =>
    intro input stored encoded
    exact ReadbackInput.array_of_encoded model order memory ty layout count element input stored encoded ih

theorem prepared_function_plan_readback (source : Environment) (roots : List Ty) (ty : Ty) (plan : Plan)
    (prepared : (prepare source roots).query ty = .ok plan) (shape : FunctionReadbackPlan plan)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory) (input : Value) (stored : Image)
    (encoded : encode model order plan input false = .ok stored) :
    ∃ output, decode model order memory plan stored.bytes = .ok output ∧ ValueReadback model memory input output := by
  have notChar : ∀ layout, plan ≠ .leaf .Char layout := by
    intro layout impossible
    subst plan
    cases shape
  exact prepared_recursive_readback source roots ty plan prepared model order memory input
    (shape.admit model order memory input stored encoded)
    (by intro layout width raw impossible; exact False.elim (notChar layout impossible)) stored encoded

end TrustIr.AggregateMemory
