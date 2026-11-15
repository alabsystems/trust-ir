-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.FunctionMemoryProps
import TrustIr.Semantics.AggregateDecoding

namespace TrustIr.AggregateMemory
open SourceLayout

/-- Registered code words recover the stored signature and target. This is
    independent of the target's executable body or indirect-call contract. -/
theorem function_aggregate_leaf_roundtrip (model : ByteModel) (ids : List FuncId) (memory : Memory)
    (signature : FuncTyId) (target : FuncId) (index : Nat) (layout : MemoryTypeLayout)
    (registered : functionAddressIndex target ids = some index)
    (bounded : index + 1 < model.addressLimit) (extent : layout.size = model.pointerBytes) :
    (encode model (some ids) (.leaf (.Func signature) layout) (.fnDef signature target) false).bind
      (fun image => decode model (some ids) memory (.leaf (.Func signature) layout) image.bytes) =
      .ok (.fnDef signature target) := by
  have size := (encodeIntBytes_length (Int.ofNat (index + 1)) model.pointerBytes).trans extent.symm
  rw [encode_function_leaf_of_memory model (some ids) signature layout _ _ (Or.inl ⟨target,rfl⟩) size
    (encodeFunctionWord model ids signature target index registered bounded)]
  simp only [Except.bind]
  rw [decode_leaf_of_bytes model (some ids) memory (.Func signature) layout _ size]
  exact decodeFunctionWord model ids memory signature target index registered bounded

theorem null_function_aggregate_leaf_roundtrip (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (signature : FuncTyId) (layout : MemoryTypeLayout) (extent : layout.size = model.pointerBytes) :
    (encode model order (.leaf (.Func signature) layout) .nullPtr false).bind
      (fun image => decode model order memory (.leaf (.Func signature) layout) image.bytes) = .ok .nullPtr := by
  trustIrCompilerProof {
    have size := (List.length_replicate model.pointerBytes (0 : UInt8)).trans extent.symm
    rw [encode_function_leaf_of_memory model order signature layout _ _ (Or.inr rfl) size
      (encodeFunctionNull model order signature)]
    simp only [Except.bind]
    rw [decode_leaf_of_bytes model order memory (.Func signature) layout _ size]
    exact decodeFunctionNull model order memory signature
  } {
    have size := (List.length_replicate (n := model.pointerBytes) (a := (0 : UInt8))).trans extent.symm
    rw [encode_function_leaf_of_memory model order signature layout _ _ (Or.inr rfl) size
      (encodeFunctionNull model order signature)]
    simp only [Except.bind]
    rw [decode_leaf_of_bytes model order memory (.Func signature) layout _ size]
    exact decodeFunctionNull model order memory signature
  }

/-- Admission binds the actual contextual table, first-match position, width
    and layout. A null function word requires no table. -/
inductive FunctionReadbackInput (model : ByteModel) : FunctionAddressOrder → Plan → Value → Prop where
  | registered (ids : List FuncId) (signature : FuncTyId) (target : FuncId) (index : Nat) (layout : MemoryTypeLayout)
      (lookup : functionAddressIndex target ids = some index)
      (bounded : index + 1 < model.addressLimit) (extent : layout.size = model.pointerBytes) :
      FunctionReadbackInput model (some ids) (.leaf (.Func signature) layout) (.fnDef signature target)
  | null (order : FunctionAddressOrder) (signature : FuncTyId) (layout : MemoryTypeLayout)
      (extent : layout.size = model.pointerBytes) :
      FunctionReadbackInput model order (.leaf (.Func signature) layout) .nullPtr

theorem FunctionReadbackInput.codec {model : ByteModel} {order : FunctionAddressOrder} {plan : Plan} {input : Value}
    (admitted : FunctionReadbackInput model order plan input) (memory : Memory) :
    (encode model order plan input false).bind (fun image => decode model order memory plan image.bytes) = .ok input := by
  cases admitted with
  | registered ids signature target index layout lookup bounded extent =>
    exact function_aggregate_leaf_roundtrip model ids memory signature target index layout lookup bounded extent
  | null order signature layout extent => exact null_function_aggregate_leaf_roundtrip model order memory signature layout extent

end TrustIr.AggregateMemory
