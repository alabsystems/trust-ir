-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.UnwrittenImageBounds

namespace TrustIr.AggregateMemory.UnwrittenImageBoundsControls

private def byte : Plan := .leaf .U8 ⟨1,1⟩
private def inner : Plan := .fields (.Tuple [.U8,.U8]) ⟨4,1⟩ [(1,byte),(3,byte)]
private def outer : Plan := .fields (.Tuple [.Tuple [.U8,.U8]]) ⟨8,1⟩ [(2,inner)]
private def input : Value := .aggregate [.aggregate [.uninit,.int 8 9]]
private def image (model : ByteModel) : Image :=
  match encode model none outer input true with
  | .ok image => image
  | .error _ => { bytes := ByteImage.empty }

private theorem encoded (model : ByteModel) : encode model none outer input true = .ok (image model) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem nested_offsets_are_added (model : ByteModel) : (image model).unwritten = [(3,1)] := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem actual_nested_encoding_is_bounded (model : ByteModel) : (image model).UnwrittenBounded :=
  encode_unwritten_bounded model none outer input true (image model) (encoded model)

theorem declared_extent_supplies_the_bound (model : ByteModel) :
    ∀ start count, (start,count) ∈ (image model).unwritten → start + count ≤ 8 :=
  encode_unwritten_plan_bounds model none outer input true (image model) (encoded model)

theorem registration_moves_into_destination_window (model : ByteModel) :
    ((Memory.empty.recordUnwritten ⟨7⟩ 100 (image model).unwritten).isUnwritten ⟨7⟩ 103,
     (Memory.empty.recordUnwritten ⟨7⟩ 100 (image model).unwritten).isUnwritten ⟨7⟩ 104) = (true,false) := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem registration_retains_allocation_identity (model : ByteModel) :
    (Memory.empty.recordUnwritten ⟨7⟩ 100 (image model).unwritten).isUnwritten ⟨8⟩ 103 = false := by
  trustIrCompilerProof {
    cases model <;> rfl
  } {
    cases model <;> trustIrReduce
  }

theorem actual_encoding_supplies_registration_bounds (model : ByteModel) (memory : Memory)
    (allocation : AllocId) (address : Nat) (lane : UnwrittenRange)
    (member : lane ∈ (memory.recordUnwritten allocation address (image model).unwritten).unwritten) :
    lane ∈ memory.unwritten ∨ lane.allocation = allocation ∧ address ≤ lane.start ∧
      lane.start < lane.stop ∧ lane.stop ≤ address + 8 :=
  encode_registered_unwritten_bounds model none outer input true (image model) (encoded model)
    memory allocation address lane member

theorem fabricated_outside_record_is_not_bounded :
    ¬ (Image.mk (ByteImage.fill 8 none) [(8,1)]).UnwrittenBounded := by
  intro bounded
  have bound := bounded 8 1 (List.Mem.head _)
  simp only [ByteImage.size_fill] at bound
  omega

theorem child_outside_parent_refuses :
    encode .le64 none (.fields (.Tuple [.U8]) ⟨1,1⟩ [(1,byte)]) (.aggregate [.uninit]) true =
      .error (.typeError "memory image: field exceeds source layout") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem zero_sized_child_outside_parent_also_refuses :
    encode .le32 none (.fields (.Tuple [.Unit]) ⟨0,1⟩ [(1,.leaf .Unit ⟨0,1⟩)]) (.aggregate [.uninit]) true =
      .error (.typeError "memory image: field exceeds source layout") := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem whole_array_unwritten_has_bounded_record :
    encode .le64 none (.array (.Array ⟨0⟩ 8) ⟨8,1⟩ 8 byte) .uninit true =
      .ok { bytes := ByteImage.fill 8 none, unwritten := [(0,8)] } := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

theorem zero_sized_record_at_endpoint_is_bounded :
    (Image.mk (ByteImage.fill 8 none) [(8,0)]).UnwrittenBounded := by
  intro start count member
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
  obtain ⟨rfl,rfl⟩ := member
  exact Nat.le_refl _

theorem zero_sized_registration_adds_no_record :
    (Memory.empty.recordUnwritten ⟨7⟩ 100 [(8,0)]).unwritten = [] := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

private def old : Memory := Memory.empty.recordUnwritten ⟨9⟩ 3000 [(0,1)]

theorem unrelated_old_records_are_preserved :
    (old.recordUnwritten ⟨7⟩ 100 (image .le64).unwritten).isUnwritten ⟨9⟩ 3000 = true := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

/-- Arbitrary overlapping plans may retain records under later byte writes.
    Extent safety alone must never be used as a readback/initialization law. -/
theorem bounded_record_does_not_imply_absent_bytes :
    (encode .le64 none (.fields (.Tuple [.U8,.U8]) ⟨1,1⟩ [(0,byte),(0,byte)])
      (.aggregate [.uninit,.int 8 9]) true).map
      (fun stored => (stored.bytes.get 0,stored.unwritten)) = .ok (some 9,[(0,1)]) := by
  trustIrCompilerProof {
    exact rfl
  } {
    exact by trustIrReduce
  }

end TrustIr.AggregateMemory.UnwrittenImageBoundsControls
