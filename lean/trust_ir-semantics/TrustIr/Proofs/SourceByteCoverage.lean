-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceFieldCoherence

namespace TrustIr.AggregateMemory
open SourceLayout

/-- A byte window inside an actual child remains a window after placement. -/
theorem ByteLane.compose {parent child bytes : ByteImage} {base offset : Nat}
    (placed : ByteLane parent base child) (covered : ByteLane child offset bytes) :
    ByteLane parent (base + offset) bytes := by
  refine ⟨by have outer := placed.1; have inner := covered.1; omega,?_⟩
  intro index inside
  rw [Nat.add_assoc,placed.2 (offset + index) (by have bound := covered.1; omega)]
  exact covered.2 index inside

/-- Placement preserves the materialized bytes of every bounded child slice.
    Bounds are explicit because slicing clips an out-of-range request. -/
theorem ByteLane.materialized_slice {parent child : ByteImage} {base : Nat}
    (placed : ByteLane parent base child) (offset count : Nat)
    (bounded : offset + count ≤ child.size) :
    (parent.slice (base + offset) count).toList = (child.slice offset count).toList := by
  trustIrCompilerProof {
    have parentBound : base + offset + count ≤ parent.size := by
      have outer := placed.1
      omega
    have parentSize : (parent.slice (base + offset) count).size = count := by
      rw [ByteImage.size_slice]
      omega
    have childSize : (child.slice offset count).size = count := by
      rw [ByteImage.size_slice]
      omega
    apply List.ext
    intro index
    rw [image_materialized_lookup,image_materialized_lookup,parentSize,childSize]
    by_cases inside : index < count
    · rw [if_pos inside,if_pos inside,
        ByteImage.get_slice parent (base + offset) count index inside (by omega),
        ByteImage.get_slice child offset count index inside (by omega)]
      rw [Nat.add_assoc,placed.2 (offset + index) (by omega)]
    · rw [if_neg inside,if_neg inside]
  } {
    have parentBound : base + offset + count ≤ parent.size := by
      have outer := placed.1
      omega
    have parentSize : (parent.slice (base + offset) count).size = count := by
      rw [ByteImage.size_slice]
      omega
    have childSize : (child.slice offset count).size = count := by
      rw [ByteImage.size_slice]
      omega
    apply CompilerCompat.listGetConstructive_ext
    intro index
    rw [image_materialized_lookup,image_materialized_lookup,parentSize,childSize]
    by_cases inside : index < count
    · rw [if_pos inside,if_pos inside,
        ByteImage.get_slice parent (base + offset) count index inside (by omega),
        ByteImage.get_slice child offset count index inside (by omega)]
      rw [Nat.add_assoc,placed.2 (offset + index) (by omega)]
    · rw [if_neg inside,if_neg inside]
  }

/-- Actual initialized child bytes, rather than containing-field geometry,
    justify the same decoder read after an actual placement. -/
theorem InitializedLane.after_placement {parent child : ByteImage} {base offset count : Nat}
    {bytes : List UInt8} (placed : ByteLane parent base child)
    (bounded : offset + count ≤ child.size)
    (initialized : InitializedLane child offset count bytes) :
    InitializedLane parent (base + offset) count bytes := by
  apply InitializedLane.of_materialized
  rw [placed.materialized_slice offset count bounded]
  exact initialized.materialized

/-- The actual overwrite supplies placement authority for nested initialized lanes. -/
theorem ImageOverwrite.initialized_child {before child after : ByteImage}
    {base offset count : Nat} {bytes : List UInt8}
    (written : ImageOverwrite before base child after)
    (bounded : offset + count ≤ child.size)
    (initialized : InitializedLane child offset count bytes) :
    InitializedLane after (base + offset) count bytes :=
  initialized.after_placement written.lane bounded

/-- Successful reads authenticate exact initialized bytes when the requested
    window is in bounds; successful clipped reads alone do not give this bound. -/
theorem InitializedLane.byte_lane {image : ByteImage} {offset count : Nat}
    {bytes : List UInt8} (read : InitializedLane image offset count bytes)
    (bounded : offset + count ≤ image.size) :
    ByteLane image offset (ByteImage.ofList (bytes.map some)) ∧ bytes.length = count := by
  have materialized := read.materialized
  have extent : (image.slice offset count).size = count := by
    rw [ByteImage.size_slice]
    omega
  have lengths := congrArg List.length materialized
  rw [image_materialized_length,extent,List.length_map] at lengths
  have exactLength : bytes.length = count := lengths.symm
  refine ⟨⟨by simpa [ByteImage.size_ofList,List.length_map,exactLength] using bounded,?_⟩,exactLength⟩
  intro index inside
  have inCount : index < count := by
    simpa [ByteImage.size_ofList,List.length_map,exactLength] using inside
  have found := congrArg (fun rows => (trustIrListGet? rows index)) materialized
  dsimp only at found
  rw [image_materialized_lookup,extent,if_pos inCount,
    ByteImage.get_slice image offset count index inCount (by omega)] at found
  rw [ByteImage.get_ofList]
  have actual := congrArg (fun row : Option (Option UInt8) => row.getD none) found
  exact actual

/-- Later actual disjoint field writes preserve a bounded initialized read. -/
theorem FieldsEncoded.preserves_initialized_lane {model : ByteModel} {order : FunctionAddressOrder}
    {fields : List (Nat × Plan)} {values : List Value} {allowUnwritten : Bool}
    {before after : Image} {offset count : Nat} {bytes : List UInt8}
    (run : FieldsEncoded model order fields values allowUnwritten before after)
    (read : InitializedLane before.bytes offset count bytes)
    (bounded : offset + count ≤ before.bytes.size)
    (separated : FieldsAvoidLane fields offset count) :
    InitializedLane after.bytes offset count bytes := by
  obtain ⟨lane,length⟩ := read.byte_lane bounded
  have avoids : FieldsAvoidLane fields offset (ByteImage.ofList (bytes.map some)).size := by
    simpa [ByteImage.size_ofList,List.length_map,length] using separated
  have retained := (run.preserves_lane lane avoids).initialized bytes
  simpa [length] using retained

/-- A nested initialized carrier survives its actual parent overwrite and all
    subsequent disjoint payload writes. No padding byte is authorized here. -/
theorem FieldsEncoded.retains_initialized_child {model : ByteModel} {order : FunctionAddressOrder}
    {fields : List (Nat × Plan)} {values : List Value} {allowUnwritten : Bool}
    {before : ByteImage} {child : ByteImage} {placed after : Image}
    {base offset count : Nat} {bytes : List UInt8}
    (written : ImageOverwrite before base child placed.bytes)
    (bounded : offset + count ≤ child.size)
    (read : InitializedLane child offset count bytes)
    (run : FieldsEncoded model order fields values allowUnwritten placed after)
    (separated : FieldsAvoidLane fields (base + offset) count) :
    InitializedLane after.bytes (base + offset) count bytes := by
  have initial := written.initialized_child bounded read
  have placedBound : base + offset + count ≤ placed.bytes.size := by
    have outer := written.lane.1
    omega
  exact run.preserves_initialized_lane initial placedBound separated

/-- Actual nested-byte coverage discharges the default-niche premise used by
    the source-bound enum selector theorem. The read comes from the child,
    and the final image comes from the real remaining field encoder. -/
theorem EnumUntaggedCarrierReady.of_retained_child
    {model : ByteModel} {order : FunctionAddressOrder}
    {fields : List (Nat × Plan)} {values : List Value} {allowUnwritten : Bool}
    {before child : ByteImage} {placed after : Image} {base offset : Nat}
    {bytes : List UInt8} (info : Enumeration) (position untagged start stop first : Nat)
    (repr : EnumTagRepr)
    (encoding : info.encoding = .niche untagged start stop first (base + offset) repr)
    (written : ImageOverwrite before base child placed.bytes)
    (bounded : offset + tagBits repr / 8 ≤ child.size)
    (read : InitializedLane child offset (tagBits repr / 8) bytes)
    (run : FieldsEncoded model order fields values allowUnwritten placed after)
    (separated : FieldsAvoidLane fields (base + offset) (tagBits repr / 8)) :
    EnumUntaggedCarrierReady info position after.bytes := by
  rw [EnumUntaggedCarrierReady,encoding]
  intro _
  exact ⟨bytes,run.retains_initialized_child written bounded read separated⟩

end TrustIr.AggregateMemory

namespace TrustIr.AggregateMemory.ByteCoverageControls

private def before : ByteImage := ByteImage.fill 8 none
private def child : ByteImage := ByteImage.ofList [none,some 7]
private def placed : Image :=
  { bytes := (before.slice 0 2).append (child.append (before.slice 4 4)) }
private def final : Image :=
  { bytes := (placed.bytes.slice 0 6).append
      ((ByteImage.ofList [some 42]).append (placed.bytes.slice 7 1)) }
private def fields : List (Nat × Plan) := [(6,.leaf .U8 ⟨1,1⟩)]

theorem actual_child_placement : ImageOverwrite before 2 child placed.bytes := rfl

theorem actual_later_write : FieldsEncoded .le64 none fields [.int 8 42] false placed final := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

/-- An interior initialized byte survives nonzero placement and a later write. -/
theorem nested_carrier_survives : InitializedLane final.bytes 3 1 [7] := by
  apply FieldsEncoded.retains_initialized_child actual_child_placement
    (offset := 1) (count := 1) (by decide) (by rfl) actual_later_write
  intro field member
  cases member with
  | head => rfl
  | tail _ impossible => cases impossible

/-- The padding next to that initialized byte remains unreadable. -/
theorem padding_is_not_authorized : ¬ ∃ bytes, InitializedLane final.bytes 2 1 bytes := by
  intro ready
  obtain ⟨bytes,read⟩ := ready
  cases read

/-- A successful clipped read is not an authenticated full-size lane. -/
theorem clipped_read_needs_bound :
    InitializedLane (ByteImage.fill 0 none) 3 1 [] ∧ ¬ 3 + 1 ≤ (ByteImage.fill 0 none).size :=
  ⟨rfl,by decide⟩

end TrustIr.AggregateMemory.ByteCoverageControls
