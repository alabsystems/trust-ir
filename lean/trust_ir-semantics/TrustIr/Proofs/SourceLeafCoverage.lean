-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceByteCoverage

namespace TrustIr.AggregateMemory
open SourceLayout

/-- Every successful ordinary leaf encoding emits exactly initialized bytes.
    The actual leaf encoder supplies the bytes and the actual extent guard
    supplies their size; no logical-value initialization premise is needed. -/
theorem encode_leaf_materialized (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (value : Value) (image : Image)
    (run : encode model order (.leaf ty layout) value false = .ok image) :
    ∃ bytes : List UInt8, image.bytes = ByteImage.ofList (bytes.map some) ∧
      bytes.length = layout.size := by
  rw [encode] at run
  by_cases uninit : value.isUninit = true
  · simp only [uninit,ite_true,Bool.false_eq_true,ite_false] at run
    cases run
  · have initialized : value.isUninit = false := by
      cases flag : value.isUninit with
      | false => rfl
      | true => exact False.elim (uninit flag)
    simp only [initialized,Bool.false_eq_true,ite_false,Bind.bind,Except.bind,
      Pure.pure,Except.pure] at run
    split at run
    · cases run
    · rename_i bytes leafRun
      by_cases fits : bytes.length = layout.size
      · simp [fits] at run
        cases run
        exact ⟨bytes,rfl,fits⟩
      · simp [fits] at run
        cases run

/-- Every bounded subrange of materialized initialized bytes is readable. -/
theorem initialized_ofList_range (bytes : List UInt8) (offset count : Nat)
    (bounded : offset + count ≤ bytes.length) :
    ∃ selected : List UInt8, selected.length = count ∧
      InitializedLane (ByteImage.ofList (bytes.map some)) offset count selected := by
  trustIrCompilerProof {
    let selected := (List.range count).map (fun index => ((trustIrListGet? bytes (offset + index))).getD 0)
    -- The bound below proves every selected index exists; the totalizing default
    -- cannot supply a missing byte and does not initialize any padding.
    have length : selected.length = count := by
      simp only [selected,List.length_map,metadata_range_length]
    have lane : ByteLane (ByteImage.ofList (bytes.map some)) offset
        (ByteImage.ofList (selected.map some)) := by
      refine ⟨by simpa [ByteImage.size_ofList,List.length_map,length] using bounded,?_⟩
      intro index inside
      have inCount : index < count := by
        simpa [ByteImage.size_ofList,List.length_map,length] using inside
      have sourceInside : offset + index < bytes.length := by omega
      have selectedAt : (trustIrListGet? selected index) = some (((trustIrListGet? bytes (offset + index))).getD 0) := by
        dsimp only [selected]
        rw [List.get?_map,numbered_range_lookup,if_pos inCount]
        rfl
      rw [ByteImage.get_ofList,ByteImage.get_ofList]
      change ((trustIrListGet? (bytes.map some) (offset + index))).getD none =
        ((trustIrListGet? (selected.map some) index)).getD none
      rw [List.get?_map,List.get?_map,selectedAt,List.get?_eq_get sourceInside]
      rfl
    refine ⟨selected,length,?_⟩
    simpa [length] using lane.initialized selected
  } {
    let selected := (List.range count).map (fun index => ((trustIrListGet? bytes (offset + index))).getD 0)
    -- The bound below proves every selected index exists; the totalizing default
    -- cannot supply a missing byte and does not initialize any padding.
    have length : selected.length = count := by
      simp only [selected,List.length_map,metadata_range_length]
    have lane : ByteLane (ByteImage.ofList (bytes.map some)) offset
        (ByteImage.ofList (selected.map some)) := by
      refine ⟨by simpa [ByteImage.size_ofList,List.length_map,length] using bounded,?_⟩
      intro index inside
      have inCount : index < count := by
        simpa [ByteImage.size_ofList,List.length_map,length] using inside
      have sourceInside : offset + index < bytes.length := by omega
      have selectedAt : (trustIrListGet? selected index) = some (((trustIrListGet? bytes (offset + index))).getD 0) := by
        dsimp only [selected]
        rw [CompilerCompat.listGetConstructive_map,numbered_range_lookup,if_pos inCount]
        rfl
      rw [ByteImage.get_ofList,ByteImage.get_ofList]
      change ((trustIrListGet? (bytes.map some) (offset + index))).getD none =
        ((trustIrListGet? (selected.map some) index)).getD none
      rw [CompilerCompat.listGetConstructive_map,CompilerCompat.listGetConstructive_map,selectedAt,CompilerCompat.listGet?_eq_get sourceInside]
      rfl
    refine ⟨selected,length,?_⟩
    simpa [length] using lane.initialized selected
  }

/-- The actual successful leaf encoder establishes every bounded carrier read. -/
theorem encode_leaf_range_initialized (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (value : Value) (image : Image)
    (run : encode model order (.leaf ty layout) value false = .ok image)
    (offset count : Nat) (bounded : offset + count ≤ layout.size) :
    ∃ bytes : List UInt8, bytes.length = count ∧ InitializedLane image.bytes offset count bytes := by
  obtain ⟨bytes,materialized,length⟩ := encode_leaf_materialized model order ty layout value image run
  rw [materialized]
  exact initialized_ofList_range bytes offset count (by omega)

/-- Actual successful leaf encoding, placement and remaining field writes
    establish coverage without a caller-supplied initialized child read. -/
theorem FieldsEncoded.retains_encoded_leaf
    {model : ByteModel} {order : FunctionAddressOrder} {ty : Ty}
    {layout : MemoryTypeLayout} {value : Value} {child placed after : Image}
    {before : ByteImage} {base offset count : Nat}
    {fields : List (Nat × Plan)} {values : List Value} {allowUnwritten : Bool}
    (encoded : encode model order (.leaf ty layout) value false = .ok child)
    (written : ImageOverwrite before base child.bytes placed.bytes)
    (bounded : offset + count ≤ layout.size)
    (run : FieldsEncoded model order fields values allowUnwritten placed after)
    (separated : FieldsAvoidLane fields (base + offset) count) :
    ∃ bytes : List UInt8, bytes.length = count ∧
      InitializedLane after.bytes (base + offset) count bytes := by
  obtain ⟨bytes,length,read⟩ := encode_leaf_range_initialized model order ty layout value child encoded offset count bounded
  have extent := encode_extent model order (.leaf ty layout) value false child encoded
  refine ⟨bytes,length,?_⟩
  exact run.retains_initialized_child written (by simpa [extent] using bounded) read separated

/-- Successful leaf encodings discharge a retained default niche carrier after
    actual placement and remaining disjoint payload writes. -/
theorem EnumUntaggedCarrierReady.of_encoded_leaf
    {model : ByteModel} {order : FunctionAddressOrder} {ty : Ty}
    {layout : MemoryTypeLayout} {value : Value} {child placed after : Image}
    {before : ByteImage} {base offset : Nat}
    {fields : List (Nat × Plan)} {values : List Value} {allowUnwritten : Bool}
    (info : Enumeration) (position untagged start stop first : Nat) (repr : EnumTagRepr)
    (encoding : info.encoding = .niche untagged start stop first (base + offset) repr)
    (encoded : encode model order (.leaf ty layout) value false = .ok child)
    (written : ImageOverwrite before base child.bytes placed.bytes)
    (bounded : offset + tagBits repr / 8 ≤ layout.size)
    (run : FieldsEncoded model order fields values allowUnwritten placed after)
    (separated : FieldsAvoidLane fields (base + offset) (tagBits repr / 8)) :
    EnumUntaggedCarrierReady info position after.bytes := by
  obtain ⟨bytes,length,read⟩ := run.retains_encoded_leaf encoded written bounded separated
  rw [EnumUntaggedCarrierReady,encoding]
  intro _
  exact ⟨bytes,read⟩

end TrustIr.AggregateMemory

namespace TrustIr.AggregateMemory.LeafCoverageControls

private def leaf : Image := { bytes := ByteImage.ofList [some 1,some 7] }
private def parent : ByteImage := ByteImage.fill 4 none
private def placed : Image :=
  { bytes := (parent.slice 0 1).append (leaf.bytes.append (parent.slice 3 1)) }

/-- A real leaf call supplies an interior carrier after nonzero placement. -/
theorem encoded_leaf_carrier_survives :
    ∃ bytes : List UInt8, bytes.length = 1 ∧ InitializedLane placed.bytes 2 1 bytes := by
  trustIrCompilerProof {
    apply FieldsEncoded.retains_encoded_leaf
      (model := .le64) (order := none) (ty := .U16) (layout := ⟨2,2⟩)
      (value := .int 16 1793) (child := leaf) (before := parent) (placed := placed)
      (base := 1) (offset := 1) (fields := []) (values := []) (allowUnwritten := false)
      (by rfl) (by rfl) (by decide) (by rfl)
    intro field member
    cases member
  } {
    apply FieldsEncoded.retains_encoded_leaf
      (model := .le64) (order := none) (ty := .U16) (layout := ⟨2,2⟩)
      (value := .int 16 1793) (child := leaf) (before := parent) (placed := placed)
      (base := 1) (offset := 1) (fields := []) (values := []) (allowUnwritten := false)
      (by trustIrReduce) (by trustIrReduce) (by decide) (by trustIrReduce)
    intro field member
    cases member
  }

theorem interior_byte_is_actual : InitializedLane placed.bytes 2 1 [7] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem wrong_leaf_extent_refuses :
    encode .le64 none (.leaf .U16 ⟨3,2⟩) (.int 16 1793) false =
      .error (.typeError "memory image: leaf byte count mismatch") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem ordinary_unwritten_refuses :
    encode .le64 none (.leaf .U8 ⟨1,1⟩) .uninit false =
      .error (.ub "memory image: inspecting an unwritten lane") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

/-- The special unwritten path cannot support a general initialized-leaf law. -/
theorem allowed_unwritten_does_not_initialize :
    encode .le64 none (.leaf .U8 ⟨1,1⟩) .uninit true =
      .ok { bytes := ByteImage.fill 1 none, unwritten := [(0,1)] } ∧
    ¬ ∃ bytes, InitializedLane (ByteImage.fill 1 none) 0 1 bytes := by
  trustIrCompilerProof {
    refine ⟨rfl,?_⟩
    intro ready
    obtain ⟨bytes,read⟩ := ready
    cases read
  } {
    refine ⟨by trustIrReduce,?_⟩
    intro ready
    obtain ⟨bytes,read⟩ := ready
    cases read
  }

end TrustIr.AggregateMemory.LeafCoverageControls
