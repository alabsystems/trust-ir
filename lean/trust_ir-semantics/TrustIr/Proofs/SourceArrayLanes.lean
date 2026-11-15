-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceArrayCoverage

namespace TrustIr.ByteImage

/-- Complete element extents with initialized bytes only in the certified
within-element lane. Bytes outside that lane may remain absent padding. -/
def StridedInitialized (stride offset count : Nat) (image : ByteImage) : Prop :=
  stride ∣ image.size ∧ ∀ index, index < image.size →
    offset ≤ index % stride → index % stride < offset + count →
    ∃ byte, image.get index = some byte

theorem StridedInitialized.empty (stride offset count : Nat) :
    StridedInitialized stride offset count ByteImage.empty := by
  refine ⟨Nat.dvd_zero stride,?_⟩
  intro index inside
  change index < 0 at inside
  omega

theorem StridedInitialized.append (stride offset count : Nat) (left right : ByteImage)
    (leftValid : StridedInitialized stride offset count left)
    (rightValid : StridedInitialized stride offset count right) :
    StridedInitialized stride offset count (left.append right) := by
  refine ⟨by rw [size_append]; exact Nat.dvd_add leftValid.1 rightValid.1,?_⟩
  intro index inside lower upper
  rw [get_append]
  by_cases before : index < left.size
  · rw [if_pos before]
    exact leftValid.2 index before lower upper
  · rw [if_neg before]
    have phase : index % stride = (index - left.size) % stride := by
      calc
        index % stride = (left.size + (index - left.size)) % stride := by
          congr 1
          omega
        _ = (index - left.size) % stride := by
          rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd leftValid.1,Nat.zero_add,Nat.mod_mod]
    apply rightValid.2 (index - left.size)
    · rw [size_append] at inside
      omega
    · simpa only [← phase] using lower
    · simpa only [← phase] using upper

theorem StridedInitialized.tile (stride offset count : Nat) (unit : ByteImage) (copies : Nat)
    (valid : StridedInitialized stride offset count unit) :
    StridedInitialized stride offset count (unit.tile copies) := by
  trustIrCompilerProof {
    refine ⟨by rw [size_tile]; exact Nat.dvd_trans valid.1 (Nat.dvd_mul_right unit.size copies),?_⟩
    intro index inside lower upper
    rw [size_tile] at inside
    rw [get_tile_inside unit copies index inside]
    apply valid.2 (index % unit.size)
    · have positive : 0 < unit.size := by
        by_cases zero : unit.size = 0
        · simp [zero] at inside
          omega
        · omega
      exact Nat.mod_lt _ positive
    · simpa only [Nat.mod_mod_of_dvd index valid.1] using lower
    · simpa only [Nat.mod_mod_of_dvd index valid.1] using upper
  } {
    refine ⟨by rw [size_tile]; exact Nat.dvd_trans valid.1 (Nat.dvd_mul_right unit.size copies),?_⟩
    intro index inside lower upper
    rw [size_tile] at inside
    rw [get_tile_inside unit copies index inside]
    apply valid.2 (index % unit.size)
    · have positive : 0 < unit.size := by
        by_cases zero : unit.size = 0
        · simp [zero] at inside
        · omega
      exact Nat.mod_lt _ positive
    · simpa only [Nat.mod_mod_of_dvd index valid.1] using lower
    · simpa only [Nat.mod_mod_of_dvd index valid.1] using upper
  }

end TrustIr.ByteImage

namespace TrustIr.AggregateMemory
open SourceLayout

/-- A retained template lane appears in every actual copy. This also covers
    empty templates and empty lanes, without a positive-byte-width premise. -/
theorem ByteLane.tile_copy {unit bytes : ByteImage} {offset copies copy : Nat}
    (lane : ByteLane unit offset bytes) (inside : copy < copies) :
    ByteLane (unit.tile copies) (copy * unit.size + offset) bytes := by
  have extent : (copy + 1) * unit.size ≤ copies * unit.size :=
    Nat.mul_le_mul_right unit.size (by omega)
  refine ⟨by rw [ByteImage.size_tile]; have bound := lane.1
             simp only [Nat.add_mul,Nat.one_mul] at extent
             rw [Nat.mul_comm unit.size copies]; omega,?_⟩
  intro index inBytes
  have inUnit : offset + index < unit.size := by have bound := lane.1; omega
  have inImage : copy * unit.size + offset + index < unit.size * copies := by
    simp only [Nat.add_mul,Nat.one_mul] at extent
    rw [Nat.mul_comm unit.size copies]
    omega
  rw [ByteImage.get_tile_inside unit copies _ inImage,Nat.add_assoc,
    Nat.mul_comm copy unit.size,Nat.mul_add_mod,Nat.mod_eq_of_lt inUnit]
  exact lane.2 index inBytes

/-- Repeating a multi-element template preserves the selected logical slot's
    child image. The source slot is selected modulo the template period;
    no equality of compact tree representations is required. -/
theorem ByteLane.tile_slot {unit bytes : ByteImage} {stride period copies slot : Nat}
    (positive : 0 < period) (extent : unit.size = period * stride)
    (inside : slot < period * copies)
    (lane : ByteLane unit ((slot % period) * stride) bytes) :
    ByteLane (unit.tile copies) (slot * stride) bytes := by
  have copyInside : slot / period < copies := by
    apply (Nat.div_lt_iff_lt_mul positive).2
    simpa only [Nat.mul_comm] using inside
  have placed := lane.tile_copy copyInside
  have position : slot / period * unit.size + slot % period * stride = slot * stride := by
    rw [extent,← Nat.mul_assoc,← Nat.add_mul]
    congr 1
    have decomposition := Nat.mod_add_div slot period
    rw [Nat.mul_comm period (slot / period)] at decomposition
    omega
  rw [position] at placed
  exact placed

/-- All compact representations retain the actual successful callback at
    every logical slot. The repetition-law parameter of the lower induction is
    discharged here by the proved semantics of ByteImage.tile. -/
theorem ArrayImageEncoded.slots (callback : Value → Except SemError ByteImage) (stride : Nat)
    (safe : ∀ value bytes, callback value = .ok bytes → bytes.size = stride)
    {size : Nat} (tree : CompactArray.Tree Value size) (image : ByteImage)
    (run : ArrayImageEncoded callback tree image) :
    image.size = size * stride ∧ ∀ slot value, slot < size → tree.get? slot = some value →
      ∃ child, callback value = .ok child ∧ child.size = stride ∧
        ByteLane image (slot * stride) child := by
  exact ArrayImageEncoded.slots_of_repetition
    (fun _ _ _ _ _ lane inside => lane.tile_copy inside) callback stride safe tree image run

/-- Actual array stores authenticate both logical census and complete byte
    extent, even when compact templates have hidden or zero-sized values. -/
theorem encode_array_geometry (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (values : CompactArray.Packed Value) (image : Image)
    (run : encode model order (.array ty layout count element) (.array values) false = .ok image) :
    values.size = count ∧ layout.size = element.layout.size * count := by
  obtain ⟨actual,same,census,fold⟩ := encode_array_steps model order ty layout count element _ image run
  cases same
  have safe : ∀ value bytes,
      (do pure (← encode model order element value false).bytes) = .ok bytes → bytes.size = element.layout.size := by
    intro value bytes encoded
    cases childRun : encode model order element value false with
    | error failure => simp [childRun,Bind.bind,Except.bind] at encoded
    | ok child =>
      simp [childRun,Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded
      cases encoded
      exact encode_extent model order element value false child childRun
  have size := (ArrayImageEncoded.slots _ element.layout.size safe values.tree image.bytes fold).1
  have parentSize := encode_extent model order (.array ty layout count element) (.array values) false image run
  change image.bytes.size = layout.size at parentSize
  refine ⟨census,?_⟩
  rw [← parentSize,size,census,Nat.mul_comm]

/-- Any successful array encoding places the actual selected child's entire
    image at its logical offset. This covers dense, uniform, split and cyclic
    trees, arbitrary phases and clipped tails, and zero-byte elements. -/
theorem encode_array_slot (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (values : CompactArray.Packed Value) (image : Image)
    (run : encode model order (.array ty layout count element) (.array values) false = .ok image)
    (slot : Nat) (value : Value) (inside : slot < values.size)
    (found : values.tree.get? slot = some value) :
    ∃ child, encode model order element value false = .ok child ∧
      ByteLane image.bytes (slot * element.layout.size) child.bytes := by
  obtain ⟨actual,same,_,fold⟩ := encode_array_steps model order ty layout count element _ image run
  cases same
  have safe : ∀ value bytes,
      (do pure (← encode model order element value false).bytes) = .ok bytes →
      bytes.size = element.layout.size := by
    intro value bytes encoded
    cases childRun : encode model order element value false with
    | error failure => simp [childRun,Bind.bind,Except.bind] at encoded
    | ok child =>
      simp [childRun,Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded
      cases encoded
      exact encode_extent model order element value false child childRun
  obtain ⟨_,slots⟩ := ArrayImageEncoded.slots _ element.layout.size safe values.tree image.bytes fold
  obtain ⟨bytes,encoded,_,lane⟩ := slots slot value inside found
  cases childRun : encode model order element value false with
  | error failure => simp [childRun,Bind.bind,Except.bind] at encoded
  | ok child =>
    simp [childRun,Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded
    cases encoded
    exact ⟨child,rfl,lane⟩

/-- The dense specialization of actual array-slot placement. -/
theorem encode_dense_array_slot (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (element : Plan) {size : Nat}
    (small : size ≤ 16) (values : CompactArray.Leaf Value size) (image : Image)
    (run : encode model order (.array ty layout size element)
      (.array ⟨size,.dense small values⟩) false = .ok image)
    (slot : Nat) (value : Value) (inside : slot < size)
    (found : values.get? slot = some value) :
    ∃ child, encode model order element value false = .ok child ∧
      ByteLane image.bytes (slot * element.layout.size) child.bytes :=
  encode_array_slot model order ty layout size element ⟨size,.dense small values⟩ image run slot value inside found

/-- The uniform specialization still requires an actual in-range source slot. -/
theorem encode_uniform_array_slot (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (element : Plan) (count : Nat)
    (value : Value) (image : Image)
    (run : encode model order (.array ty layout count element)
      (.array ⟨count,.uniform count value⟩) false = .ok image)
    (slot : Nat) (inside : slot < count) :
    ∃ child, encode model order element value false = .ok child ∧
      ByteLane image.bytes (slot * element.layout.size) child.bytes :=
  encode_array_slot model order ty layout count element ⟨count,.uniform count value⟩ image run slot value inside
    (by simp only [CompactArray.Tree.get?,if_pos inside])

/-- A real successful array decoder returns its exact logical census and
    the actual strict nested callback at every slot. -/
theorem decode_array_slots (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (layoutExtent : layout.size = element.layout.size * count) (image : ByteImage) (result : Value)
    (run : decode model order memory (.array ty layout count element) image = .ok result) :
    image.size = layout.size ∧ ∃ values : CompactArray.Packed Value,
      result = .array values ∧ values.size = count ∧
      ∀ slot value, slot < count → values.tree.get? slot = some value →
        ∃ part, part.size = element.layout.size ∧
          (∀ index, index < element.layout.size → part.get index = image.get (slot * element.layout.size + index)) ∧
          ChildDecoded model order memory element part value :=
  decode_array_slots_of_mapper
    (fun callback image width count extent tree run => ByteImage.mapBlocks_decoded callback image width count extent tree run)
    model order memory ty layout count element layoutExtent image result run

/-- The selected array value came from a real nested decoder call on this
    exact retained parent lane; source padding is not invented or initialized. -/
theorem decode_array_slot (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (layoutExtent : layout.size = element.layout.size * count)
    (image : ByteImage) (values : CompactArray.Packed Value)
    (run : decode model order memory (.array ty layout count element) image = .ok (.array values))
    (slot : Nat) (value : Value) (inside : slot < count) (found : values.tree.get? slot = some value) :
    ∃ part, part.size = element.layout.size ∧ ChildDecoded model order memory element part value ∧
      ByteLane image (slot * element.layout.size) part := by
  obtain ⟨imageSize,actual,same,_,slots⟩ := decode_array_slots model order memory ty layout count element
    layoutExtent image (.array values) run
  cases same
  obtain ⟨part,partSize,bytes,decoded⟩ := slots slot value inside found
  refine ⟨part,partSize,decoded,?_,?_⟩
  · have bounded := Nat.mul_le_mul_right element.layout.size (show slot + 1 ≤ count by omega)
    rw [Nat.add_mul,Nat.one_mul] at bounded
    rw [partSize,imageSize,layoutExtent]
    simpa only [Nat.mul_comm count element.layout.size] using bounded
  · intro index inPart
    exact (bytes index (by simpa only [partSize] using inPart)).symm

/-- An authentic source-plan origin discharges the parent/child extent premise
    for decoded slots, including independently prepared child plans. -/
theorem decode_source_array_slot (source : Environment) (id : TyId)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (origin : Plan.Origin (SourceElement source) (ActualSummary source) (.Array id count)
      (.array (.Array id count) layout count element))
    (image : ByteImage) (values : CompactArray.Packed Value)
    (run : decode model order memory (.array (.Array id count) layout count element) image = .ok (.array values))
    (slot : Nat) (value : Value) (inside : slot < count) (found : values.tree.get? slot = some value) :
    ∃ part, part.size = element.layout.size ∧ ChildDecoded model order memory element part value ∧
      ByteLane image (slot * element.layout.size) part :=
  decode_array_slot model order memory (.Array id count) layout count element origin.source_array_extent.1
    image values run slot value inside found

/-- Actual prepared source queries automatically supply all layout-origin
    evidence needed for exact decoded-slot custody. -/
theorem prepared_array_decoded_slot (source : Environment) (roots : List Ty) (id : TyId)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (prepared : (prepare source roots).query (.Array id count) =
      .ok (.array (.Array id count) layout count element))
    (image : ByteImage) (values : CompactArray.Packed Value)
    (run : decode model order memory (.array (.Array id count) layout count element) image = .ok (.array values))
    (slot : Nat) (value : Value) (inside : slot < count) (found : values.tree.get? slot = some value) :
    ∃ part, part.size = element.layout.size ∧ ChildDecoded model order memory element part value ∧
      ByteLane image (slot * element.layout.size) part :=
  decode_source_array_slot source id model order memory layout count element
    (prepared_plan_origin source roots (.Array id count) _ prepared) image values run slot value inside found

/-- Actual array writing and reading meet on identical child byte observations.
    The child value readback law remains a separate recursive obligation. -/
theorem array_slot_codec_bytes (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (layoutExtent : layout.size = element.layout.size * count)
    (inputs outputs : CompactArray.Packed Value) (image : Image)
    (encoded : encode model order (.array ty layout count element) (.array inputs) false = .ok image)
    (decoded : decode model order memory (.array ty layout count element) image.bytes = .ok (.array outputs))
    (slot : Nat) (input output : Value) (inside : slot < count)
    (inputFound : inputs.tree.get? slot = some input) (outputFound : outputs.tree.get? slot = some output) :
    ∃ stored : Image, ∃ loaded : ByteImage,
      encode model order element input false = .ok stored ∧
      ChildDecoded model order memory element loaded output ∧
      stored.bytes.size = element.layout.size ∧ loaded.size = element.layout.size ∧
      ∀ index, loaded.get index = stored.bytes.get index := by
  obtain ⟨actual,same,census,_⟩ := encode_array_steps model order ty layout count element (.array inputs) image encoded
  cases same
  obtain ⟨stored,storedRun,storedLane⟩ := encode_array_slot model order ty layout count element inputs image
    encoded slot input (by rw [census]; exact inside) inputFound
  obtain ⟨loaded,loadedSize,loadedRun,loadedLane⟩ := decode_array_slot model order memory ty layout count element
    layoutExtent image.bytes outputs decoded slot output inside outputFound
  have storedSize := encode_extent model order element input false stored storedRun
  refine ⟨stored,loaded,storedRun,loadedRun,storedSize,loadedSize,?_⟩
  intro index
  by_cases inChild : index < element.layout.size
  · exact (loadedLane.2 index (by rw [loadedSize]; exact inChild)).symm.trans
      (storedLane.2 index (by rw [storedSize]; exact inChild))
  · rw [ByteImage.get_outside loaded index (by rw [loadedSize]; omega),
      ByteImage.get_outside stored.bytes index (by rw [storedSize]; omega)]

/-- Prepared source queries discharge the codec bridge's parent/stride extent
    without a caller-supplied byte-placement or child-layout assertion. -/
theorem prepared_array_slot_codec_bytes (source : Environment) (roots : List Ty) (id : TyId)
    (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (prepared : (prepare source roots).query (.Array id count) = .ok (.array (.Array id count) layout count element))
    (inputs outputs : CompactArray.Packed Value) (image : Image)
    (encoded : encode model order (.array (.Array id count) layout count element) (.array inputs) false = .ok image)
    (decoded : decode model order memory (.array (.Array id count) layout count element) image.bytes = .ok (.array outputs))
    (slot : Nat) (input output : Value) (inside : slot < count)
    (inputFound : inputs.tree.get? slot = some input) (outputFound : outputs.tree.get? slot = some output) :
    ∃ stored : Image, ∃ loaded : ByteImage,
      encode model order element input false = .ok stored ∧ ChildDecoded model order memory element loaded output ∧
      stored.bytes.size = element.layout.size ∧ loaded.size = element.layout.size ∧
      ∀ index, loaded.get index = stored.bytes.get index :=
  array_slot_codec_bytes model order memory (.Array id count) layout count element
    (prepared_array_element_extent source roots id layout count element prepared).1 inputs outputs image
    encoded decoded slot input output inside inputFound outputFound

/-- A bounded successful read supplies an actual byte at each requested index. -/
theorem InitializedLane.present {image : ByteImage} {offset count : Nat} {bytes : List UInt8}
    (read : InitializedLane image offset count bytes) (bounded : offset + count ≤ image.size)
    (index : Nat) (inside : index < count) : ∃ byte, image.get (offset + index) = some byte := by
  trustIrCompilerProof {
    obtain ⟨lane,length⟩ := read.byte_lane bounded
    refine ⟨bytes.get ⟨index,by omega⟩,?_⟩
    rw [lane.2 index (by simpa [ByteImage.size_ofList,List.length_map,length] using inside),ByteImage.get_ofList]
    change ((trustIrListGet? (bytes.map some) index)).getD none = _
    rw [List.get?_map,List.get?_eq_get (by omega)]
    rfl
  } {
    obtain ⟨lane,length⟩ := read.byte_lane bounded
    refine ⟨bytes.get ⟨index,by omega⟩,?_⟩
    rw [lane.2 index (by simpa [ByteImage.size_ofList,List.length_map,length] using inside),ByteImage.get_ofList]
    change ((trustIrListGet? (bytes.map some) index)).getD none = _
    rw [CompilerCompat.listGetConstructive_map,CompilerCompat.listGet?_eq_get (by omega)]
    rfl
  }

/-- Presence at every bounded byte yields a real initialized read. Totalizing
lookup defaults below are unreachable, as witnessed by present. -/
theorem initialized_of_present (image : ByteImage) (offset count : Nat)
    (bounded : offset + count ≤ image.size)
    (present : ∀ index, index < count → ∃ byte, image.get (offset + index) = some byte) :
    ∃ bytes : List UInt8, bytes.length = count ∧ InitializedLane image offset count bytes := by
  trustIrCompilerProof {
    let bytes := (List.range count).map (fun index => (image.get (offset + index)).getD 0)
    have length : bytes.length = count := by
      simp only [bytes,List.length_map,metadata_range_length]
    have lane : ByteLane image offset (ByteImage.ofList (bytes.map some)) := by
      refine ⟨by simpa [ByteImage.size_ofList,List.length_map,length] using bounded,?_⟩
      intro index inside
      have inCount : index < count := by simpa [ByteImage.size_ofList,List.length_map,length] using inside
      obtain ⟨byte,found⟩ := present index inCount
      have selected : (trustIrListGet? bytes index) = some byte := by
        dsimp only [bytes]
        rw [List.get?_map,numbered_range_lookup,if_pos inCount]
        change some ((image.get (offset + index)).getD 0) = some byte
        rw [found]
        rfl
      rw [found,ByteImage.get_ofList]
      change some byte = ((trustIrListGet? (bytes.map some) index)).getD none
      rw [List.get?_map,selected]
      rfl
    exact ⟨bytes,length,by simpa only [length] using lane.initialized bytes⟩
  } {
    let bytes := (List.range count).map (fun index => (image.get (offset + index)).getD 0)
    have length : bytes.length = count := by
      simp only [bytes,List.length_map,metadata_range_length]
    have lane : ByteLane image offset (ByteImage.ofList (bytes.map some)) := by
      refine ⟨by simpa [ByteImage.size_ofList,List.length_map,length] using bounded,?_⟩
      intro index inside
      have inCount : index < count := by simpa [ByteImage.size_ofList,List.length_map,length] using inside
      obtain ⟨byte,found⟩ := present index inCount
      have selected : (trustIrListGet? bytes index) = some byte := by
        dsimp only [bytes]
        rw [CompilerCompat.listGetConstructive_map,numbered_range_lookup,if_pos inCount]
        change some ((image.get (offset + index)).getD 0) = some byte
        rw [found]
        rfl
      rw [found,ByteImage.get_ofList]
      change some byte = ((trustIrListGet? (bytes.map some) index)).getD none
      rw [CompilerCompat.listGetConstructive_map,selected]
      rfl
    exact ⟨bytes,length,by simpa only [length] using lane.initialized bytes⟩
  }

/-- One ordinary element image establishes the same lane mask used for all
compact array representations. Padding outside the lane remains unconstrained. -/
theorem InitializedLane.strided {image : ByteImage} {offset count stride : Nat} {bytes : List UInt8}
    (extent : image.size = stride) (read : InitializedLane image offset count bytes)
    (bounded : offset + count ≤ stride) : ByteImage.StridedInitialized stride offset count image := by
  refine ⟨by rw [extent]; exact Nat.dvd_refl stride,?_⟩
  intro index inside lower upper
  have small : index < stride := by omega
  rw [Nat.mod_eq_of_lt small] at lower upper
  obtain ⟨byte,present⟩ := read.present (by omega) (index - offset) (by omega)
  exact ⟨byte,by simpa only [Nat.add_sub_of_le lower] using present⟩

/-- Every bounded slot-lane covered by a strided image is an initialized read.
The bound is explicit: successful clipped empty reads cannot invent a slot. -/
theorem strided_initialized_window {image : ByteImage} {stride offset count : Nat}
    (valid : ByteImage.StridedInitialized stride offset count image)
    (within : offset + count ≤ stride) (slot : Nat)
    (bounded : slot * stride + offset + count ≤ image.size) :
    ∃ bytes : List UInt8, bytes.length = count ∧
      InitializedLane image (slot * stride + offset) count bytes := by
  apply initialized_of_present image _ count bounded
  intro index inside
  have small : offset + index < stride := by omega
  have phase : (slot * stride + offset + index) % stride = offset + index := by
    rw [Nat.add_assoc,Nat.mul_comm slot stride,Nat.mul_add_mod,Nat.mod_eq_of_lt small]
  exact valid.2 _ (by omega) (by rw [phase]; omega) (by rw [phase]; omega)

/-- Actual compact array encoding preserves a child lane in every emitted
stride. The premise concerns successful actual element calls, not padding or
logical materialization of the array. -/
theorem encode_array_strided (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (offset laneCount : Nat) (within : offset + laneCount ≤ element.layout.size)
    (safe : ∀ value child, encode model order element value false = .ok child →
      ∃ bytes : List UInt8, bytes.length = laneCount ∧ InitializedLane child.bytes offset laneCount bytes)
    (value : Value) (image : Image)
    (run : encode model order (.array ty layout count element) value false = .ok image) :
    ByteImage.StridedInitialized element.layout.size offset laneCount image.bytes := by
  obtain ⟨values,_,_,fold⟩ := encode_array_steps model order ty layout count element value image run
  apply ArrayImageEncoded.preserves (ByteImage.StridedInitialized element.layout.size offset laneCount)
    (ByteImage.StridedInitialized.empty _ _ _)
    (ByteImage.StridedInitialized.append _ _ _)
    (ByteImage.StridedInitialized.tile _ _ _) _ _ values.tree image.bytes fold
  intro child bytes encoded
  cases result : encode model order element child false with
  | error failure => simp [result,Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded
  | ok childImage =>
    simp [result,Bind.bind,Except.bind,Pure.pure,Except.pure] at encoded
    cases encoded
    obtain ⟨selected,_,read⟩ := safe child childImage result
    exact read.strided (encode_extent model order element child false childImage result) within

/-- A physically bounded array slot inherits its child's initialized lane from
the actual array fold, across all compact representations. -/
theorem encode_array_initialized_slot (model : ByteModel) (order : FunctionAddressOrder)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
    (offset laneCount : Nat) (within : offset + laneCount ≤ element.layout.size)
    (safe : ∀ value child, encode model order element value false = .ok child →
      ∃ bytes : List UInt8, bytes.length = laneCount ∧ InitializedLane child.bytes offset laneCount bytes)
    (slot : Nat) (bounded : slot * element.layout.size + offset + laneCount ≤ layout.size)
    (value : Value) (image : Image)
    (run : encode model order (.array ty layout count element) value false = .ok image) :
    ∃ bytes : List UInt8, bytes.length = laneCount ∧
      InitializedLane image.bytes (slot * element.layout.size + offset) laneCount bytes := by
  have mask := encode_array_strided model order ty layout count element offset laneCount within safe value image run
  apply strided_initialized_window mask within slot
  rw [encode_extent model order (.array ty layout count element) value false image run]
  exact bounded


/-- The checked production mapper discharges the lower array constructor's
    capability premise. The callback success guarantee covers real windows. -/
theorem decode_array_exists_of_children (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan) (image : ByteImage)
    (layoutExtent : layout.size = element.layout.size * count) (imageExtent : image.size = layout.size)
    (children : ∀ slot, slot < count → ∀ part, part.size = element.layout.size →
      (∀ index, index < element.layout.size → part.get index = image.get (slot * element.layout.size + index)) →
      ∃ value, ChildDecoded model order memory element part value) :
    ∃ values : CompactArray.Packed Value, values.size = count ∧
      decode model order memory (.array ty layout count element) image = .ok (.array values) :=
  decode_array_exists_of_mapper ByteImage.mapBlocks_exists_of_windows model order memory ty layout count element image
    layoutExtent imageExtent children

theorem ChildDecoded.array_exists_of_children (model : ByteModel) (order : FunctionAddressOrder) (memory : Memory)
    (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan) (image : ByteImage)
    (layoutExtent : layout.size = element.layout.size * count) (imageExtent : image.size = layout.size)
    (children : ∀ slot, slot < count → ∀ part, part.size = element.layout.size →
      (∀ index, index < element.layout.size → part.get index = image.get (slot * element.layout.size + index)) →
      ∃ value, ChildDecoded model order memory element part value) :
    ∃ values : CompactArray.Packed Value, values.size = count ∧
      ChildDecoded model order memory (.array ty layout count element) image (.array values) :=
  ChildDecoded.array_exists_of_mapper ByteImage.mapBlocks_exists_of_windows model order memory ty layout count element image
    layoutExtent imageExtent children

end TrustIr.AggregateMemory
