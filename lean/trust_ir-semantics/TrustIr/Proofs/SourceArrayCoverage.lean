-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceLeafCoverage
import TrustIr.Proofs.ByteImageTraversalProps

namespace TrustIr.ByteImage

/-- Every byte inside the actual image is present. Padding does not satisfy this. -/
def FullyInitialized (image : ByteImage) : Prop :=
  ∀ index, index < image.size → ∃ byte, image.get index = some byte

theorem FullyInitialized.empty : FullyInitialized ByteImage.empty := by
  intro index inside
  change index < 0 at inside
  omega

theorem FullyInitialized.append (left right : ByteImage)
    (leftValid : FullyInitialized left) (rightValid : FullyInitialized right) :
    FullyInitialized (left.append right) := by
  intro index inside
  rw [get_append]
  by_cases before : index < left.size
  · rw [if_pos before]
    exact leftValid index before
  · rw [if_neg before]
    apply rightValid
    rw [size_append] at inside
    omega

theorem FullyInitialized.tile (unit : ByteImage) (count : Nat)
    (valid : FullyInitialized unit) : FullyInitialized (unit.tile count) := by
  trustIrCompilerProof {
    intro index inside
    rw [size_tile] at inside
    rw [get_tile_inside unit count index inside]
    apply valid
    have positive : 0 < unit.size := by
      by_cases zero : unit.size = 0
      · simp [zero] at inside
        omega
      · omega
    exact Nat.mod_lt _ positive
  } {
    intro index inside
    rw [size_tile] at inside
    rw [get_tile_inside unit count index inside]
    apply valid
    have positive : 0 < unit.size := by
      by_cases zero : unit.size = 0
      · simp [zero] at inside
      · omega
    exact Nat.mod_lt _ positive
  }

end TrustIr.ByteImage

namespace TrustIr.AggregateMemory
open SourceLayout

/-- Successful ordinary leaf encodings contain no absent byte. -/
theorem encode_leaf_fully_initialized (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (value : Value) (image : Image)
    (run : encode model order (.leaf ty layout) value false = .ok image) :
    ByteImage.FullyInitialized image.bytes := by
  trustIrCompilerProof {
    obtain ⟨bytes,materialized,_⟩ := encode_leaf_materialized model order ty layout value image run
    rw [materialized]
    intro index inside
    have bounded : index < bytes.length := by simpa using inside
    refine ⟨bytes.get ⟨index,bounded⟩,?_⟩
    rw [ByteImage.get_ofList]
    change ((trustIrListGet? (bytes.map some) index)).getD none = _
    rw [List.get?_map,List.get?_eq_get bounded]
    rfl
  } {
    obtain ⟨bytes,materialized,_⟩ := encode_leaf_materialized model order ty layout value image run
    rw [materialized]
    intro index inside
    have bounded : index < bytes.length := by simpa using inside
    refine ⟨bytes.get ⟨index,bounded⟩,?_⟩
    rw [ByteImage.get_ofList]
    change ((trustIrListGet? (bytes.map some) index)).getD none = _
    rw [CompilerCompat.listGetConstructive_map,CompilerCompat.listGet?_eq_get bounded]
    rfl
  }

/-- Actual array folding preserves initialization when every successful element
encoding supplies it. Padded elements require a weaker lane property instead. -/
theorem encode_array_fully_initialized (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (safe : ∀ value image, encode model order element value false = .ok image →
      ByteImage.FullyInitialized image.bytes)
    (value : Value) (image : Image)
    (run : encode model order (.array ty layout count element) value false = .ok image) :
    ByteImage.FullyInitialized image.bytes := by
  obtain ⟨values,_,_,fold⟩ := encode_array_steps model order ty layout count element value image run
  apply ArrayImageEncoded.preserves ByteImage.FullyInitialized ByteImage.FullyInitialized.empty
    ByteImage.FullyInitialized.append ByteImage.FullyInitialized.tile _ _ values.tree image.bytes fold
  intro child bytes encoded
  cases result : encode model order element child false with
  | error failure => simp [result,Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded
  | ok childImage =>
    simp [result,Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded
    cases encoded
    exact safe child childImage result

/-- Plans whose storage consists entirely of leaf bytes and nested arrays. -/
inductive Plan.LeafArrays : Plan → Prop
  | leaf (ty : Ty) (layout : MemoryTypeLayout) : LeafArrays (.leaf ty layout)
  | array (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
      (child : LeafArrays element) : LeafArrays (.array ty layout count element)

/-- Arbitrarily nested arrays of leaves initialize every emitted byte on success.
No source-kind or source-layout validity is inferred from this byte fact. -/
theorem Plan.LeafArrays.fully_initialized {plan : Plan} (shape : plan.LeafArrays)
    (model : ByteModel) (order : FunctionAddressOrder) (value : Value) (image : Image)
    (run : encode model order plan value false = .ok image) :
    ByteImage.FullyInitialized image.bytes := by
  induction shape generalizing value image with
  | leaf ty layout => exact encode_leaf_fully_initialized model order ty layout value image run
  | array ty layout count element child ih =>
    exact encode_array_fully_initialized model order ty layout count element
      (fun value image encoded => ih value image encoded) value image run

/-- An absent padding byte cannot satisfy full initialization. -/
theorem fully_initialized_padding_refusal :
    ¬ ByteImage.FullyInitialized (ByteImage.fill 1 none) := by
  intro valid
  obtain ⟨byte,present⟩ := valid 0 (by decide)
  cases present

/-- Empty storage has no byte to initialize, even when repeated. -/
theorem fully_initialized_empty_tile (count : Nat) :
    ByteImage.FullyInitialized (ByteImage.empty.tile count) :=
  ByteImage.FullyInitialized.tile _ count ByteImage.FullyInitialized.empty

end TrustIr.AggregateMemory
