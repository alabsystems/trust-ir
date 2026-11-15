-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.VectorCodec
import TrustIr.Semantics.AggregateDecoding

namespace TrustIr.AggregateMemory

/-- The actual store establishes every input-side vector admission fact. -/
theorem vector_leaf_admission_of_encoded (model : ByteModel) (order : FunctionAddressOrder)
    (count : Nat) (ty : Ty) (layout : MemoryTypeLayout) (inputs : List Value)
    (lane : VectorReadbackLane ty) (stored : Image)
    (encoded : encode model order (.leaf (.Vector count ty) layout) (.vector inputs) false = .ok stored) :
    ∃ size, vectorScalarByteSize ty = some size ∧ count ≠ 0 ∧ inputs.length = count ∧
      layout.size = count * size ∧ ∀ input ∈ inputs, VectorLaneReady ty input := by
  obtain ⟨bytes,memoryRun,size,_image⟩ := encode_leaf_memory_success model order (.Vector count ty) layout (.vector inputs) stored encoded
  have vectorRun : encodeScalarVectorAt count ty (.vector inputs) = .ok bytes := by
    cases model <;> exact memoryRun
  obtain ⟨laneBytes,actual,positive,typed,shape,census,run,extent⟩ := encodeScalarVectorAt_steps count ty (.vector inputs) bytes vectorRun
  cases shape
  exact ⟨laneBytes,typed,positive,census,size.symm.trans extent,vector_lanes_ready_of_encoded ty lane inputs bytes run⟩

/-- Actual successful packed storage supplies lane readiness and exact nested
    readback through every complete byte-equivalent receiving window. -/
theorem vector_child_readback_of_encoded (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (count : Nat) (ty : Ty) (layout : MemoryTypeLayout) (inputs : List Value)
    (lane : VectorReadbackLane ty) (stored : Image) (loaded : ByteImage)
    (encoded : encode model order (.leaf (.Vector count ty) layout) (.vector inputs) false = .ok stored)
    (extent : loaded.size = layout.size) (observed : ∀ index, loaded.get index = stored.bytes.get index) :
    ChildDecoded model order memory (.leaf (.Vector count ty) layout) loaded (.vector (inputs.map vectorLaneResult)) ∧
      ∀ input ∈ inputs, VectorLaneReady ty input := by
  obtain ⟨bytes,memoryRun,size,image⟩ := encode_leaf_memory_success model order (.Vector count ty) layout (.vector inputs) stored encoded
  have vectorRun : encodeScalarVectorAt count ty (.vector inputs) = .ok bytes := by
    cases model <;> exact memoryRun
  obtain ⟨actual,shape,_census,ready,decoded⟩ := vector_codec_readback_of_encoded count ty (.vector inputs) bytes lane vectorRun
  cases shape
  have memoryDecoded : decodeMemoryWithFunctions model order memory (.Vector count ty) bytes =
      .ok (.vector (inputs.map vectorLaneResult)) := by
    cases model <;> simp [decodeMemoryWithFunctions,decodeMemoryAt,decodeValueAt,decodeImageAt,
      decodeTypedAtModel,decodeImageAtModel,decoded,Memory.resolveDecoded,Bind.bind,Except.bind,Pure.pure,Except.pure]
  have own : decode model order memory (.leaf (.Vector count ty) layout) stored.bytes =
      .ok (.vector (inputs.map vectorLaneResult)) := by
    rw [image,decode_leaf_of_bytes model order memory (.Vector count ty) layout bytes size]
    exact memoryDecoded
  have nested := (ChildDecoded.leaf_iff_decode model order memory (.Vector count ty) layout stored.bytes
    (.vector (inputs.map vectorLaneResult)) (by intro impossible; cases impossible)).mpr own
  refine ⟨(ChildDecoded.leaf_iff_of_observations model order memory (.Vector count ty) layout loaded stored.bytes
    (extent.trans (encode_extent model order (.leaf (.Vector count ty) layout) (.vector inputs) false stored encoded).symm)
    observed _).mpr nested,ready⟩

end TrustIr.AggregateMemory
