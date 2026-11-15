-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceSiblingGeometry

run_cmd do
  if Lean.versionString == "4.30.0-rc2" then
    let env ← Lean.getEnv
    let mut registered := 0
    for (n, _) in env.constants.map₁.toList do
      if n.toString.endsWith "TrustIr.SourceLayout.compileTy.eq_def" ||
         n.toString.endsWith "TrustIr.SourceLayout.compileTypes.eq_def" then
        Lean.Elab.Command.elabCommand (← `(command| attribute [local cbv_eval] $(Lean.mkIdent n):ident))
        registered := registered + 1
    unless registered == 2 do
      Lean.throwError "expected the two original layout compiler equations"
  else if Lean.versionString != "4.8.0" then
    Lean.throwError "unsupported compiler for layout equation reduction"

namespace TrustIr.AggregateMemory.ArrayLaneControls

private def element : Plan := .fields (.Tuple [.U8,.U16]) ⟨4,2⟩
  [(0,.leaf .U8 ⟨1,1⟩),(2,.leaf .U16 ⟨2,2⟩)]
private def a : Value := .aggregate [.int 8 7,.int 16 4660]
private def b : Value := .aggregate [.int 8 9,.int 16 9029]
private def uniform : CompactArray.Packed Value := ⟨3,.uniform 3 a⟩
private def dense : CompactArray.Packed Value :=
  ⟨3,.dense (by decide) (.cons a (.cons b (.cons a .nil)))⟩
private def split : CompactArray.Packed Value :=
  ⟨4,.split (by decide) (.uniform 2 a) (.uniform 2 b)⟩
private def periodic : CompactArray.Packed Value :=
  ⟨5,.periodic (.dense (by decide) (.cons a (.cons b .nil))) (by decide) 1 5⟩
private def observe (values : CompactArray.Packed Value) (offset count : Nat) :
    Except SemError (List (Option UInt8)) := do
  let image ← encode .le64 none
    (.array (.Array ⟨0⟩ values.size) ⟨values.size * 4,2⟩ values.size element) (.array values) false
  pure (image.bytes.slice offset count).toList

theorem element_lane : element.CoversLane 2 2 := by
  trustIrCompilerProof {
    apply Plan.CoversLane.fields (position := 1) (base := 2) (offset := 0)
      (child := .leaf .U16 ⟨2,2⟩) (by rfl) (by decide) (.leaf (by decide))
    intro field member
    cases member
  } {
    apply Plan.CoversLane.fields (position := 1) (base := 2) (offset := 0)
      (child := .leaf .U16 ⟨2,2⟩) (by trustIrReduce) (by decide) (.leaf (by decide))
    intro field member
    cases member
  }

/-- Two array levels and a field step retain both logical index and byte bounds. -/
theorem nested_array_field_path :
    (Plan.array (.Array ⟨1⟩ 2) ⟨24,2⟩ 2
      (.array (.Array ⟨0⟩ 3) ⟨12,2⟩ 3 element)).CoversLane 22 2 := by
  apply Plan.CoversLane.array (slot := 1) (offset := 10) (by decide) (by decide)
  apply Plan.CoversLane.array (slot := 2) (offset := 2) (by decide) (by decide)
  exact element_lane

theorem uniform_retains_lane_and_padding :
    observe uniform 10 2 = .ok [some 52,some 18] ∧ observe uniform 9 1 = .ok [none] := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

theorem dense_retains_lane_and_padding :
    observe dense 6 2 = .ok [some 69,some 35] ∧ observe dense 5 1 = .ok [none] := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

theorem split_retains_lane_and_padding :
    observe split 14 2 = .ok [some 69,some 35] ∧ observe split 13 1 = .ok [none] := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

theorem shifted_periodic_retains_lane_and_padding :
    observe periodic 18 2 = .ok [some 69,some 35] ∧ observe periodic 17 1 = .ok [none] := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

/-- A single visible good value does not force the hidden poison template slot. -/
theorem periodic_hidden_poison_not_forced :
    observe ⟨1,.periodic (.dense (by decide) (.cons (.undef .U8) (.cons a .nil))) (by decide) 1 1⟩ 2 2 =
      .ok [some 52,some 18] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem visible_unwritten_refuses :
    observe ⟨1,.uniform 1 .uninit⟩ 2 2 =
      .error (.ub "memory image: inspecting an unwritten lane") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

/-- The zero-byte read cannot authenticate a nonexistent logical array slot. -/
theorem empty_array_has_no_coverage (offset count : Nat) :
    ¬ (Plan.array (.Array ⟨0⟩ 0) ⟨0,1⟩ 0 (.leaf .U8 ⟨1,1⟩)).CoversLane offset count := by
  intro covered
  cases covered with
  | array inside bounded covered => omega

/-- Zero-stride repetition remains valid for an empty lane. -/
theorem zero_stride_empty_lane (copies : Nat) :
    ByteImage.StridedInitialized 0 0 0 (ByteImage.empty.tile copies) :=
  ByteImage.StridedInitialized.tile _ _ _ _ copies (ByteImage.StridedInitialized.empty _ _ _)

private def zeroElement : Plan := .fields (.Tuple []) ⟨0,1⟩ []
private def zeroArray (count : Nat) : Plan := .array (.Array ⟨0⟩ count) ⟨0,1⟩ count zeroElement

/-- Empty byte output does not excuse a visible invalid source value. -/
theorem zero_stride_visible_poison_refuses :
    encode .le64 none (zeroArray 3) (.array ⟨3,.uniform 3 .uninit⟩) false =
      .error (.ub "memory image: inspecting an unwritten lane") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

/-- With no logical slots the callback is unused, even if its retained value
    would be rejected at every visible slot. -/
theorem zero_count_hidden_poison_is_unused :
    encode .le64 none (zeroArray 0) (.array ⟨0,.uniform 0 .uninit⟩) false =
      .ok ⟨ByteImage.empty,[]⟩ := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem zero_stride_uniform_slot_has_actual_child (image : Image)
    (run : encode .le64 none (zeroArray 3)
      (.array ⟨3,.uniform 3 (.aggregate [])⟩) false = .ok image) :
    ∃ child, encode .le64 none zeroElement (.aggregate []) false = .ok child ∧
      ByteLane image.bytes 0 child.bytes := by
  simpa only [zeroElement,Plan.layout,Nat.mul_zero] using
    encode_uniform_array_slot .le64 none (.Array ⟨0⟩ 3) ⟨0,1⟩ zeroElement
      3 (.aggregate []) image run 2 (by decide)

/-- The logical lookup selects the second dense value, including its padding,
    rather than merely witnessing that some initialized child exists. -/
theorem dense_second_slot_has_selected_child (image : Image)
    (run : encode .le64 none (.array (.Array ⟨0⟩ 3) ⟨12,2⟩ 3 element)
      (.array dense) false = .ok image) :
    ∃ child, encode .le64 none element b false = .ok child ∧
      ByteLane image.bytes 4 child.bytes := by
  trustIrCompilerProof {
    exact encode_dense_array_slot .le64 none (.Array ⟨0⟩ 3) ⟨12,2⟩ element
      (by decide) (.cons a (.cons b (.cons a .nil))) image run 1 b (by decide) rfl
  } {
    exact encode_dense_array_slot .le64 none (.Array ⟨0⟩ 3) ⟨12,2⟩ element
      (by decide) (.cons a (.cons b (.cons a .nil))) image run 1 b (by decide) (by trustIrReduce)
  }

/-- Instantiate the general slot law on a child that also carries padding. -/
private theorem selected_slot (values : CompactArray.Packed Value) (slot : Nat) (value : Value)
    (inside : slot < values.size) (found : values.tree.get? slot = some value)
    (image : Image)
    (run : encode .le64 none (.array (.Array ⟨0⟩ values.size) ⟨values.size * 4,2⟩ values.size element)
      (.array values) false = .ok image) :
    ∃ child, encode .le64 none element value false = .ok child ∧
      ByteLane image.bytes (slot * 4) child.bytes :=
  encode_array_slot .le64 none (.Array ⟨0⟩ values.size) ⟨values.size * 4,2⟩ values.size
    element values image run slot value inside found

theorem split_left_boundary_child (image : Image)
    (run : encode .le64 none (.array (.Array ⟨0⟩ 4) ⟨16,2⟩ 4 element) (.array split) false = .ok image) :
    ∃ child, encode .le64 none element a false = .ok child ∧ ByteLane image.bytes 4 child.bytes := by
  trustIrCompilerProof {
    exact selected_slot split 1 a (by decide) rfl image run
  } {
    exact selected_slot split 1 a (by decide) (by trustIrReduce) image run
  }

theorem split_right_boundary_child (image : Image)
    (run : encode .le64 none (.array (.Array ⟨0⟩ 4) ⟨16,2⟩ 4 element) (.array split) false = .ok image) :
    ∃ child, encode .le64 none element b false = .ok child ∧ ByteLane image.bytes 8 child.bytes := by
  trustIrCompilerProof {
    exact selected_slot split 2 b (by decide) rfl image run
  } {
    exact selected_slot split 2 b (by decide) (by trustIrReduce) image run
  }

private def cyclic : CompactArray.Packed Value :=
  ⟨10,.periodic (.dense (by decide) (.cons a (.cons b (.cons a .nil)))) (by decide) 13 10⟩

theorem cyclic_prefix_child (image : Image)
    (run : encode .le64 none (.array (.Array ⟨0⟩ 10) ⟨40,2⟩ 10 element) (.array cyclic) false = .ok image) :
    ∃ child, encode .le64 none element a false = .ok child ∧ ByteLane image.bytes 4 child.bytes := by
  trustIrCompilerProof {
    exact selected_slot cyclic 1 a (by decide) rfl image run
  } {
    exact selected_slot cyclic 1 a (by decide) (by trustIrReduce) image run
  }

theorem cyclic_middle_child (image : Image)
    (run : encode .le64 none (.array (.Array ⟨0⟩ 10) ⟨40,2⟩ 10 element) (.array cyclic) false = .ok image) :
    ∃ child, encode .le64 none element a false = .ok child ∧ ByteLane image.bytes 20 child.bytes := by
  trustIrCompilerProof {
    exact selected_slot cyclic 5 a (by decide) rfl image run
  } {
    exact selected_slot cyclic 5 a (by decide) (by trustIrReduce) image run
  }

theorem cyclic_tail_child (image : Image)
    (run : encode .le64 none (.array (.Array ⟨0⟩ 10) ⟨40,2⟩ 10 element) (.array cyclic) false = .ok image) :
    ∃ child, encode .le64 none element b false = .ok child ∧ ByteLane image.bytes 36 child.bytes := by
  trustIrCompilerProof {
    exact selected_slot cyclic 9 b (by decide) rfl image run
  } {
    exact selected_slot cyclic 9 b (by decide) (by trustIrReduce) image run
  }

theorem cyclic_tail_value_and_padding :
    observe cyclic 38 2 = .ok [some 69,some 35] ∧ observe cyclic 37 1 = .ok [none] := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

private def poisonCycle (count : Nat) : CompactArray.Packed Value :=
  ⟨count,.periodic (.dense (by decide) (.cons .uninit (.cons a (.cons b .nil)))) (by decide) 1 count⟩

theorem clipped_cycle_does_not_force_poison :
    observe (poisonCycle 2) 6 2 = .ok [some 69,some 35] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem clipped_cycle_selected_child (image : Image)
    (run : encode .le64 none (.array (.Array ⟨0⟩ 2) ⟨8,2⟩ 2 element)
      (.array (poisonCycle 2)) false = .ok image) :
    ∃ child, encode .le64 none element a false = .ok child ∧ ByteLane image.bytes 0 child.bytes := by
  trustIrCompilerProof {
    exact selected_slot (poisonCycle 2) 0 a (by decide) rfl image run
  } {
    exact selected_slot (poisonCycle 2) 0 a (by decide) (by trustIrReduce) image run
  }

theorem complete_cycle_forces_visible_poison :
    observe (poisonCycle 5) 0 1 = .error (.ub "memory image: inspecting an unwritten lane") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem clipped_tail_forces_visible_poison :
    observe (poisonCycle 3) 0 1 = .error (.ub "memory image: inspecting an unwritten lane") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private def zeroCyclic : CompactArray.Packed Value :=
  ⟨5,.periodic (.uniform 2 (.aggregate [])) (by decide) 7 5⟩

theorem zero_stride_cyclic_success :
    encode .le32 none (zeroArray 5) (.array zeroCyclic) false = .ok ⟨ByteImage.empty,[]⟩ := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem zero_stride_cyclic_selected_child (image : Image)
    (run : encode .le32 none (zeroArray 5) (.array zeroCyclic) false = .ok image) :
    ∃ child, encode .le32 none zeroElement (.aggregate []) false = .ok child ∧
      ByteLane image.bytes 0 child.bytes := by
  trustIrCompilerProof {
    exact encode_array_slot .le32 none (.Array ⟨0⟩ 5) ⟨0,1⟩ 5 zeroElement zeroCyclic
      image run 4 (.aggregate []) (by decide) rfl
  } {
    exact encode_array_slot .le32 none (.Array ⟨0⟩ 5) ⟨0,1⟩ 5 zeroElement zeroCyclic
      image run 4 (.aggregate []) (by decide) (by trustIrReduce)
  }

/-- Repetition without whole-stride alignment can move padding into a lane. -/
theorem misaligned_repeat_refuses :
    ¬ ByteImage.StridedInitialized 3 0 1 (ByteImage.ofList [some 7,none]) ∧
      ((ByteImage.ofList [some 7,none]).tile 2).get 3 = none := by
  trustIrCompilerProof {
    refine ⟨?_,rfl⟩
    intro mask
    have bound := Nat.le_of_dvd (by decide : 0 < 2) mask.1
    change 3 ≤ 2 at bound
    omega
  } {
    refine ⟨?_,(by trustIrReduce)⟩
    intro mask
    have bound := Nat.le_of_dvd (by decide : 0 < 2) mask.1
    change 3 ≤ 2 at bound
    omega
  }

end TrustIr.AggregateMemory.ArrayLaneControls

namespace TrustIr.AggregateMemory.SourceArrayExtentControls
open SourceLayout

private def source : Environment := { types := [some .U16] }
private def nestedSource : Environment :=
  { types := [some (.Array ⟨1⟩ 3),some (.Tuple [.U8,.U16])] }
private def cell : Plan := .fields (.Tuple [.U8,.U16]) ⟨4,2⟩
  [(0,.leaf .U8 ⟨1,1⟩),(2,.leaf .U16 ⟨2,2⟩)]
private def row : Plan := .array (.Array ⟨1⟩ 3) ⟨12,2⟩ 3 cell
private def matrix : Plan := .array (.Array ⟨0⟩ 2) ⟨24,2⟩ 2 row
set_option maxHeartbeats 1000000 in
private theorem prepared : (prepare nestedSource [.U64]).query (.Array ⟨0⟩ 2) = .ok matrix := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem nested_array_path_without_parent_bound : matrix.LanePath 22 2 := by
  trustIrCompilerProof {
    exact .array (slot := 1) (offset := 10) (by decide)
      (.array (slot := 2) (offset := 2) (by decide)
        (.fields (position := 1) (base := 2) (offset := 0) (child := .leaf .U16 ⟨2,2⟩) rfl (.leaf (by decide))))
  } {
    exact .array (slot := 1) (offset := 10) (by decide)
      (.array (slot := 2) (offset := 2) (by decide)
        (.fields (position := 1) (base := 2) (offset := 0) (child := .leaf .U16 ⟨2,2⟩) (by trustIrReduce) (.leaf (by decide))))
  }

theorem actual_nested_array_path_is_covered : matrix.CoversLane 22 2 :=
  prepared_lane_path_covers nestedSource [.U64] (.Array ⟨0⟩ 2) matrix prepared 22 2
    nested_array_path_without_parent_bound

theorem actual_nested_array_path_is_bounded : 22 + 2 ≤ matrix.layout.size :=
  actual_nested_array_path_is_covered.bounds

theorem actual_nested_array_path_initializes (model : ByteModel) (order : FunctionAddressOrder)
    (value : Value) (image : Image) (run : encode model order matrix value false = .ok image) :
    ∃ bytes : List UInt8, bytes.length = 2 ∧ InitializedLane image.bytes 22 2 bytes :=
  actual_nested_array_path_is_covered.initialized model order value image run

private def wrongParent : Plan := .array (.Array ⟨0⟩ 2) ⟨1,2⟩ 2 (.leaf .U16 ⟨2,2⟩)
private def wrongChild : Plan := .array (.Array ⟨0⟩ 2) ⟨4,2⟩ 2 (.leaf .U16 ⟨1,2⟩)

theorem undersized_parent_has_no_actual_origin :
    ¬ Plan.Origin (SourceElement source) (ActualSummary source) (.Array ⟨0⟩ 2) wrongParent := by
  intro origin
  have impossible : 1 = 4 := origin.source_array_extent.1
  cases impossible

theorem forged_child_stride_has_no_actual_origin :
    ¬ Plan.Origin (SourceElement source) (ActualSummary source) (.Array ⟨0⟩ 2) wrongChild := by
  intro origin
  have impossible : 4 = 2 := origin.source_array_extent.1
  cases impossible

private def emptySource : Environment := { types := [some (.Tuple [])] }
private def zeroSized : Plan := .array (.Array ⟨0⟩ 3) ⟨0,1⟩ 3 (.fields (.Tuple []) ⟨0,1⟩ [])

theorem zero_sized_elements_keep_exact_extent :
    zeroSized.layout.size = 0 * 3 ∧ zeroSized.layout.alignment = 1 := by
  trustIrCompilerProof {
    have run : (prepare emptySource [.U8]).query (.Array ⟨0⟩ 3) = .ok zeroSized := rfl
    have extent := prepared_array_element_extent emptySource [.U8] ⟨0⟩ ⟨0,1⟩ 3 (.fields (.Tuple []) ⟨0,1⟩ []) run
    exact ⟨extent.1,extent.2.1⟩
  } {
    have run : (prepare emptySource [.U8]).query (.Array ⟨0⟩ 3) = .ok zeroSized := (by trustIrReduce)
    have extent := prepared_array_element_extent emptySource [.U8] ⟨0⟩ ⟨0,1⟩ 3 (.fields (.Tuple []) ⟨0,1⟩ []) run
    exact ⟨extent.1,extent.2.1⟩
  }

private def noSlots : Plan := .array (.Array ⟨0⟩ 0) ⟨0,2⟩ 0 (.leaf .U16 ⟨2,2⟩)

theorem zero_count_has_no_logical_lane (offset count : Nat) : ¬ noSlots.LanePath offset count := by
  intro path
  cases path with
  | array inside child => omega

end TrustIr.AggregateMemory.SourceArrayExtentControls

namespace TrustIr.AggregateMemory.ArrayDecoderControls

private def observeSlot (model : ByteModel) (plan : Plan) (image : ByteImage) (slot : Nat) :
    Except SemError (Option Value) := do
  let value ← decode model none Memory.empty plan image
  match value with
  | .array values => pure (values.tree.get? slot)
  | _ => pure none
private def refused (result : Except SemError Value) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false
private def tuple : Plan := .fields (.Tuple [.U8,.U16]) ⟨4,2⟩
  [(0,.leaf .U8 ⟨1,1⟩),(2,.leaf .U16 ⟨2,2⟩)]
private def tuples : Plan := .array (.Array ⟨0⟩ 2) ⟨8,2⟩ 2 tuple
private def padded : ByteImage := ByteImage.ofList
  [some 7,none,some 52,some 18,some 9,none,some 69,some 35]

theorem tuple_array_keeps_padding_absent :
    observeSlot .le64 tuples padded 1 = .ok (some (.aggregate [.int 8 9,.int 16 9029])) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private def chars : Plan := .array (.Array ⟨0⟩ 1) ⟨4,4⟩ 1 (.leaf .Char ⟨4,4⟩)
private def surrogate : ByteImage := ByteImage.ofList [some 0,some 216,some 0,some 0]

theorem nested_char_retains_raw_word :
    observeSlot .le64 chars surrogate 0 = .ok (some (.int 32 55296)) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem top_level_char_validation_stays_distinct :
    refused (decode .le64 none Memory.empty (.leaf .Char ⟨4,4⟩) surrogate) = true := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private def zero : Plan := .array (.Array ⟨0⟩ 3) ⟨0,1⟩ 3 (.fields (.Tuple []) ⟨0,1⟩ [])

theorem zero_stride_decoder_has_actual_slots :
    observeSlot .le32 zero ByteImage.empty 2 = .ok (some (.aggregate [])) ∧
      observeSlot .le32 zero ByteImage.empty 3 = .ok none := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

theorem zero_count_decoder_does_not_force_child :
    observeSlot .le64 (.array (.Array ⟨0⟩ 0) ⟨0,1⟩ 0 (.leaf .U8 ⟨1,1⟩)) ByteImage.empty 0 = .ok none := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

private def words : Plan := .array (.Array ⟨0⟩ 3) ⟨6,2⟩ 3 (.leaf .U16 ⟨2,2⟩)

theorem missing_covered_byte_refuses :
    refused (decode .le64 none Memory.empty words
      (ByteImage.ofList [some 1,some 0,none,some 0,some 3,some 0])) = true := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem parent_extent_mismatch_refuses :
    refused (decode .le64 none Memory.empty words (ByteImage.fill 5 (some 0))) = true := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

/-- The actual selected callback retains padding, even though the child only
    decodes its two covered fields. No initialized-padding premise is added. -/
theorem selected_child_keeps_padding (values : CompactArray.Packed Value)
    (run : decode .le64 none Memory.empty tuples padded = .ok (.array values))
    (found : values.tree.get? 1 = some (.aggregate [.int 8 9,.int 16 9029])) :
    ∃ part, ChildDecoded .le64 none Memory.empty tuple part (.aggregate [.int 8 9,.int 16 9029]) ∧
      part.get 1 = none := by
  trustIrCompilerProof {
    obtain ⟨part,partSize,decoded,lane⟩ := decode_array_slot .le64 none Memory.empty
      (.Array ⟨0⟩ 2) ⟨8,2⟩ 2 tuple rfl padded values run 1 _ (by decide) found
    refine ⟨part,decoded,?_⟩
    have byte := lane.2 1 (by rw [partSize]; decide)
    have absent : padded.get (1 * tuple.layout.size + 1) = none := rfl
    rw [absent] at byte
    exact byte.symm
  } {
    obtain ⟨part,partSize,decoded,lane⟩ := decode_array_slot .le64 none Memory.empty
      (.Array ⟨0⟩ 2) ⟨8,2⟩ 2 tuple (by trustIrReduce) padded values run 1 _ (by decide) found
    refine ⟨part,decoded,?_⟩
    have byte := lane.2 1 (by rw [partSize]; decide)
    have absent : padded.get (1 * tuple.layout.size + 1) = none := (by trustIrReduce)
    rw [absent] at byte
    exact byte.symm
  }

end TrustIr.AggregateMemory.ArrayDecoderControls
