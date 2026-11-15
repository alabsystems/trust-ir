-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.ScalarEncodedAdmission

namespace TrustIr.AggregateMemory.ScalarAdmissionControls
open SourceLayout

private def stored (model : ByteModel) (plan : Plan) (input : Value) : Image :=
  match encode model none plan input false with
  | .ok image => image
  | .error _ => { bytes := ByteImage.empty }
private def byte : Plan := .leaf .U8 ⟨1,1⟩
private def pointer : Plan := .leaf .Ptr ⟨8,8⟩
private def character : Plan := .leaf .Char ⟨4,4⟩

theorem integer_store_and_lane_check_supply_admission :
    ScalarReadbackInput .le64 byte (.int 8 513) := by
  trustIrCompilerProof {
    exact .integer_of_checked_encoded .le64 none .U8 ⟨1,1⟩ (.int 8 513) (stored .le64 byte (.int 8 513)) rfl rfl rfl
  } {
    exact .integer_of_checked_encoded .le64 none .U8 ⟨1,1⟩ (.int 8 513) (stored .le64 byte (.int 8 513)) (by trustIrReduce) (by trustIrReduce) (by trustIrReduce)
  }

theorem target32_signed_transport_supplies_admission :
    ScalarReadbackInput .le32 (.leaf .Isize ⟨4,4⟩) (.int 32 (-1)) := by
  trustIrCompilerProof {
    exact .integer_of_checked_encoded .le32 none .Isize ⟨4,4⟩ (.int 32 (-1))
      (stored .le32 (.leaf .Isize ⟨4,4⟩) (.int 32 (-1))) rfl rfl rfl
  } {
    exact .integer_of_checked_encoded .le32 none .Isize ⟨4,4⟩ (.int 32 (-1))
      (stored .le32 (.leaf .Isize ⟨4,4⟩) (.int 32 (-1))) (by trustIrReduce) (by trustIrReduce) (by trustIrReduce)
  }

theorem distinct_byte_image_integer_readback :
    ∃ output, decode .le64 none Memory.empty byte (ByteImage.source 1 (stored .le64 byte (.int 8 513)).bytes.get) = .ok output ∧
      ValueReadback .le64 Memory.empty (.int 8 513) output := by
  trustIrCompilerProof {
    exact (ScalarReadbackPlan.integer .U8 ⟨1,1⟩ rfl).readback .le64 none Memory.empty (.int 8 513)
      (stored .le64 byte (.int 8 513)) rfl rfl _ rfl (source_image_observations (stored .le64 byte (.int 8 513)).bytes) (by intro layout width raw impossible; cases impossible)
  } {
    exact (ScalarReadbackPlan.integer .U8 ⟨1,1⟩ (by trustIrReduce)).readback .le64 none Memory.empty (.int 8 513)
      (stored .le64 byte (.int 8 513)) (by trustIrReduce) (by trustIrReduce) _ (by trustIrReduce) (by
        have extent : (stored .le64 byte (.int 8 513)).bytes.size = 1 := by trustIrReduce
        simpa only [extent] using source_image_observations (stored .le64 byte (.int 8 513)).bytes) (by intro layout width raw impossible; cases impossible)
  }

theorem pointer_store_supplies_width_and_extent :
    ScalarReadbackInput .le64 pointer (.ptr 1025 (some ⟨99⟩)) := by
  trustIrCompilerProof {
    exact .pointer_of_checked_encoded .le64 none .Ptr ⟨8,8⟩ (.ptr 1025 (some ⟨99⟩))
      (stored .le64 pointer (.ptr 1025 (some ⟨99⟩))) rfl rfl rfl
  } {
    exact .pointer_of_checked_encoded .le64 none .Ptr ⟨8,8⟩ (.ptr 1025 (some ⟨99⟩))
      (stored .le64 pointer (.ptr 1025 (some ⟨99⟩))) (by trustIrReduce) (by trustIrReduce) (by trustIrReduce)
  }

theorem zero_pointer_canonical_readback :
    decode .le64 none Memory.empty pointer (stored .le64 pointer (.ptr 0 (some ⟨99⟩))).bytes = .ok .nullPtr := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem boolean_checker_supplies_admission : ScalarReadbackInput .le32 (.leaf .Bool ⟨1,1⟩) (.bool false) := by
  trustIrCompilerProof {
    exact .boolean_of_checked .le32 (.bool false) rfl
  } {
    exact .boolean_of_checked .le32 (.bool false) (by trustIrReduce)
  }

theorem unit_checker_supplies_admission : ScalarReadbackInput .le64 (.leaf .Unit ⟨0,1⟩) (.aggregate []) := by
  trustIrCompilerProof {
    exact .unit_of_checked .le64 (.aggregate []) rfl
  } {
    exact .unit_of_checked .le64 (.aggregate []) (by trustIrReduce)
  }

private def length32 : Plan := .leaf (.FatPtr .ContainerLen) ⟨8,4⟩
private def lengthInput : Value := .fatPtr 1025 (some ⟨99⟩) (.int 32 (-1))

theorem target32_length_store_supplies_metadata_admission : ScalarReadbackInput .le32 length32 lengthInput := by
  trustIrCompilerProof {
    exact .fat_of_encoded .le32 none .ContainerLen ⟨8,4⟩ lengthInput (stored .le32 length32 lengthInput) rfl
  } {
    exact .fat_of_encoded .le32 none .ContainerLen ⟨8,4⟩ lengthInput (stored .le32 length32 lengthInput) (by trustIrReduce)
  }

private def vtable : Plan := .leaf (.FatPtr .ContainerVtable) ⟨16,8⟩
private def vtableInput : Value := .fatPtr 1025 (some ⟨99⟩) (.ptr 1034 (some ⟨98⟩))

theorem vtable_store_supplies_both_address_bounds : ScalarReadbackInput .le64 vtable vtableInput := by
  trustIrCompilerProof {
    exact .fat_of_encoded .le64 none .ContainerVtable ⟨16,8⟩ vtableInput (stored .le64 vtable vtableInput) rfl
  } {
    exact .fat_of_encoded .le64 none .ContainerVtable ⟨16,8⟩ vtableInput (stored .le64 vtable vtableInput) (by trustIrReduce)
  }

theorem null_vtable_store_supplies_admission :
    ScalarReadbackInput .le64 vtable (.fatPtr 1025 none .nullPtr) := by
  trustIrCompilerProof {
    exact .fat_of_encoded .le64 none .ContainerVtable ⟨16,8⟩ (.fatPtr 1025 none .nullPtr)
      (stored .le64 vtable (.fatPtr 1025 none .nullPtr)) rfl
  } {
    exact .fat_of_encoded .le64 none .ContainerVtable ⟨16,8⟩ (.fatPtr 1025 none .nullPtr)
      (stored .le64 vtable (.fatPtr 1025 none .nullPtr)) (by trustIrReduce)
  }

/-- Storage success alone is insufficient: the real lane checker refuses this
    integer carrier at a pointer type. -/
theorem pointer_byte_storage_does_not_authenticate_lane :
    encode .le64 none pointer (.int 64 1025) false = .ok (stored .le64 pointer (.int 64 1025)) ∧
    checkAggregateLane .le64 .Ptr (.int 64 1025) =
      .error (.typeError "MakeAggregate: operand does not match its declared type") := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

theorem boolean_byte_storage_does_not_authenticate_lane :
    encode .le64 none (.leaf .Bool ⟨1,1⟩) (.int 8 1) false =
      .ok (stored .le64 (.leaf .Bool ⟨1,1⟩) (.int 8 1)) ∧
    checkAggregateLane .le64 .Bool (.int 8 1) =
      .error (.typeError "MakeAggregate: operand does not match its declared type") := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

theorem target32_pointer_lane_check_does_not_waive_overflow :
    checkAggregateLane .le32 .Ptr (.ptr 4294967296 none) = .ok () ∧
    encode .le32 none (.leaf .Ptr ⟨4,4⟩) (.ptr 4294967296 none) false =
      .error (.ub "Store: pointer address exceeds the target width") := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl⟩
  } {
    exact ⟨(by trustIrReduce),(by trustIrReduce)⟩
  }

theorem wrong_fat_metadata_still_refuses :
    encode .le32 none length32 (.fatPtr 1025 none (.int 64 3)) false =
      .error (.typeError "memory image: noncanonical fat-pointer lanes") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem nested_surrogate_has_checked_store_admission :
    ScalarReadbackInput .le64 character (.int 32 55296) := by
  trustIrCompilerProof {
    exact .integer_of_checked_encoded .le64 none .Char ⟨4,4⟩ (.int 32 55296)
      (stored .le64 character (.int 32 55296)) rfl rfl rfl
  } {
    exact .integer_of_checked_encoded .le64 none .Char ⟨4,4⟩ (.int 32 55296)
      (stored .le64 character (.int 32 55296)) (by trustIrReduce) (by trustIrReduce) (by trustIrReduce)
  }

theorem recursive_checker_supplies_valid_top_character (ctx : EvalContext) :
    TopCharReady character (.int 32 128512) := by
  trustIrCompilerProof {
    exact top_char_ready_of_checked_closure ctx 1 character (.int 32 128512) rfl
  } {
    exact top_char_ready_of_checked_closure ctx 1 character (.int 32 128512) (by trustIrReduce)
  }

theorem recursive_checker_refuses_surrogate (ctx : EvalContext) :
    checkClosureValueAt ctx 1 .Char (.int 32 55296) =
      .error (.ub "closure boundary: invalid Unicode scalar value") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem top_surrogate_load_still_refuses :
    decode .le64 none Memory.empty character (stored .le64 character (.int 32 55296)).bytes =
      .error (.ub "memory decode: invalid Unicode scalar value") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact (by trustIrReduce)
  }

theorem float_has_no_implicit_scalar_plan : ¬ ScalarReadbackPlan (.leaf .F64 ⟨8,8⟩) := by
  intro shape
  cases shape with
  | integer ty layout integer => cases integer
  | pointer ty layout pointer => cases pointer

end TrustIr.AggregateMemory.ScalarAdmissionControls
