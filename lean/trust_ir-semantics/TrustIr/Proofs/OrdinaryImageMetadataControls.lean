-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.OrdinaryImageMetadata

namespace TrustIr.AggregateMemory.OrdinaryImageMetadataControls
open SourceLayout

private def byte : Plan := .leaf .U8 ⟨1,1⟩
private def padded : Plan := .fields (.Tuple [.U8,.U8]) ⟨4,1⟩ [(0,byte),(3,byte)]
private def input : Value := .aggregate [.int 8 7,.int 8 9]
private def image : Image :=
  match encode .le64 none padded input false with
  | .ok stored => stored
  | .error _ => { bytes := ByteImage.empty }

/-- Empty metadata does not imply fully initialized padding bytes. -/
theorem padding_is_not_an_unwritten_lane :
    encode .le64 none padded input false = .ok image ∧ image.bytes.get 1 = none ∧ image.unwritten = [] := by
  trustIrCompilerProof {
    exact ⟨rfl,rfl,rfl⟩
  } {
    exact ⟨by trustIrReduce,by trustIrReduce,by trustIrReduce⟩
  }

theorem nested_ordinary_metadata_empty (model : ByteModel) (order : FunctionAddressOrder)
    (plan : Plan) (value : Value) (stored : Image)
    (encoded : encode model order plan value false = .ok stored) : stored.unwritten = [] :=
  encode_ordinary_unwritten_empty model order plan value stored encoded

theorem unwritten_permission_is_observable :
    encode .le64 none padded .uninit true =
      .ok { bytes := ByteImage.fill 4 none, unwritten := [(0,4)] } := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem ordinary_whole_unwritten_refuses :
    encode .le32 none padded .uninit false = .error (.ub "memory image: inspecting an unwritten lane") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem ordinary_nested_unwritten_refuses :
    encode .le64 none padded (.aggregate [.int 8 7,.uninit]) false =
      .error (.ub "memory image: inspecting an unwritten lane") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem allowed_nested_unwritten_retains_offset :
    (encode .le32 none padded (.aggregate [.int 8 7,.uninit]) true).map (fun stored => stored.unwritten) =
      .ok [(3,1)] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem empty_array_unused_template_has_no_records :
    (encode .le64 none (.array (.Array ⟨0⟩ 0) ⟨0,1⟩ 0 padded)
      (.array (.uniform 0 .uninit)) false).map (fun stored => stored.unwritten) = .ok [] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem visible_array_unwritten_refuses :
    encode .le64 none (.array (.Array ⟨0⟩ 1) ⟨1,1⟩ 1 byte)
      (.array (.uniform 1 .uninit)) true = .error (.ub "memory image: inspecting an unwritten lane") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private def info : Enumeration :=
  { tag := .u8, discriminants := [0], encoding := .untagged,
    variants := [[{ ty := .U8,offset := 0,size := 1,align := 1 }]], uninhabited := [false] }
private def enumeration : Plan := .enumeration (.Enum ⟨0⟩) ⟨1,1⟩ info [some [(0,byte)]]

theorem enum_payload_metadata_empty :
    (encode .le64 none enumeration (.aggregate [.int 8 0,.int 8 9]) false).map
      (fun stored => stored.unwritten) = .ok [] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem enum_payload_does_not_inherit_permission :
    encode .le32 none enumeration (.aggregate [.int 8 0,.uninit]) true =
      .error (.ub "memory image: inspecting an unwritten lane") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem zero_sized_whole_record_is_retained_by_encoder :
    (encode .le64 none (.leaf .Unit ⟨0,1⟩) .uninit true).map (fun stored => stored.unwritten) =
      .ok [(0,0)] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem zero_sized_record_is_omitted_by_memory :
    (Memory.empty.recordUnwritten ⟨0⟩ 1024 [(0,0)]).unwritten = [] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem ordinary_recording_preserves_existing_memory (memory : Memory) (allocation : AllocId) (address : Nat) :
    memory.recordUnwritten allocation address image.unwritten = memory := by
  trustIrCompilerProof {
    exact encode_ordinary_recordUnwritten .le64 none padded input image rfl memory allocation address
  } {
    exact encode_ordinary_recordUnwritten .le64 none padded input image (by trustIrReduce) memory allocation address
  }

/-- Copying holes transports bytes only, without inventing source-lane facts. -/
theorem copying_padding_does_not_record_unwritten :
    (Memory.empty.writeImage 1024 image.bytes).unwritten = [] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

end TrustIr.AggregateMemory.OrdinaryImageMetadataControls
