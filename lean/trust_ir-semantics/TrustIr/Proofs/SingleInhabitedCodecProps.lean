-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SourceLayoutProps
import TrustIr.Semantics.AggregateAccess

namespace TrustIr.SingleInhabitedProps
open SourceLayout AggregateMemory

private def nestedSource : Environment :=
  { source with enums := [definition,
      { id := ⟨1⟩, name := "OptionSelected"
        variants := [{ name := "None", fields := [] },
          { name := "Some", fields := [.Enum ⟨0⟩] }]
        layout := some { encoding := .direct 0, size := 8, align := 4, variantFieldOffsets := [[], [4]] } }] }

private def logicalValue : Value := .aggregate [.int 8 42, .int 32 67305985]
private def payloadBytes : List (Option UInt8) := [some 1, some 2, some 3, some 4]

private def selectedPlan : Plan :=
  .enumeration (.Enum ⟨0⟩) ⟨4, 4⟩
    { tag := .i8, discriminants := [-7, 42], encoding := .singleInhabited 1,
      variants := [[], [{ ty := .U32, offset := 0, size := 4, align := 4 }]],
      uninhabited := [true, false] }
    [none, some [(0, .leaf .U32 ⟨4, 4⟩)]]

/-- The plan is derived by the actual source service before any byte proof. -/
theorem source_prepares_selected_plan :
    (AggregateMemory.prepare source [.Enum ⟨0⟩]).query (.Enum ⟨0⟩) =
      .ok selectedPlan := by
  trustIrCompilerProof {
    simp only [AggregateMemory.prepare, AggregateMemory.Service.query,
      List.forIn, List.forIn.loop]
    rfl
  } {
    trustIrReduce
  }

private def roundtrip (environment : Environment) (ty : Ty) (value : Value) :
    Except SemError (List (Option UInt8) × Value) := do
  let plan ← (AggregateMemory.prepare environment [ty]).query ty
  let image ← encode .le64 none plan value
  let decoded ← decode .le64 none Memory.empty plan image.bytes
  pure (image.bytes.toList, decoded)

/-- Actual preparation, encoding and decoding preserve the selected logical tag. -/
theorem selected_discriminant_and_bytes_roundtrip :
    roundtrip source (.Enum ⟨0⟩) logicalValue =
      .ok (payloadBytes, logicalValue) := by
  simp only [roundtrip, source_prepares_selected_plan]
  trustIrReduce

theorem nested_option_roundtrip :
    roundtrip nestedSource (.Enum ⟨1⟩) (.aggregate [.int 8 1, logicalValue]) =
      .ok ([some 1, none, none, none] ++ payloadBytes,
        .aggregate [.int 8 1, logicalValue]) := by
  trustIrCompilerProof {
    simp only [roundtrip, AggregateMemory.prepare, AggregateMemory.Service.query,
      List.forIn, List.forIn.loop]
    rfl
  } {
    trustIrReduce
  }

theorem dead_variant_value_cannot_be_encoded :
    (do
      let plan ← (AggregateMemory.prepare source [.Enum ⟨0⟩]).query (.Enum ⟨0⟩)
      let _ ← encode .le64 none plan (.aggregate [.int 8 (-7), .uninit, .uninit])
      pure ()) = .error (.typeError "memory image: uninhabited enum variant") := by
  simp only [source_prepares_selected_plan]
  trustIrReduce

end TrustIr.SingleInhabitedProps
