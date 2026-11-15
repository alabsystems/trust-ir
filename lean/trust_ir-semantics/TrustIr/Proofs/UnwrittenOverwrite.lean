-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.UnwrittenImageBounds

namespace TrustIr

private def laneCovers (allocation : AllocId) (query : Nat) (lane : UnwrittenRange) : Bool :=
  lane.allocation == allocation && lane.start ≤ query && query < lane.stop

private def clippedLane (address length : Nat) (lane : UnwrittenRange) : List UnwrittenRange :=
  if lane.stop ≤ address || address + length ≤ lane.start then [lane]
  else
    (if lane.start < address then [{ lane with stop := address }] else []) ++
    (if address + length < lane.stop then [{ lane with start := address + length }] else [])

private theorem any_append {α : Type} (left right : List α) (predicate : α → Bool) :
    (left ++ right).any predicate = (left.any predicate || right.any predicate) := by
  induction left with
  | nil => rfl
  | cons head rest ih => simp only [List.cons_append,List.any_cons,ih,Bool.or_assoc]

private theorem clipped_lane_coverage (allocation : AllocId) (query address length : Nat) (lane : UnwrittenRange) :
    (clippedLane address length lane).any (laneCovers allocation query) =
      (laneCovers allocation query lane && !(address ≤ query && query < address + length)) := by
  trustIrCompilerProof {
    by_cases same : lane.allocation = allocation
    all_goals unfold clippedLane
    all_goals repeat' split
    all_goals apply Bool.eq_iff_iff.mpr
    all_goals simp_all [laneCovers,any_append]
    case pos.inl =>
      rename_i disjoint
      intro low high
      rcases disjoint with before | after
      · exact Or.inl (Nat.lt_of_lt_of_le high before)
      · exact Or.inr (Nat.le_trans after low)
    case pos.inr.inl.inl =>
      rename_i overlap _leftPart _rightPart
      constructor
      · intro covered
        rcases covered with ⟨low,high⟩ | ⟨low,high⟩
        · exact ⟨⟨low,Nat.lt_trans high overlap.1⟩,Or.inl high⟩
        · exact ⟨⟨Nat.le_trans (Nat.le_of_lt overlap.2) low,high⟩,Or.inr low⟩
      · rintro ⟨⟨low,high⟩,outside⟩
        rcases outside with before | after
        · exact Or.inl ⟨low,before⟩
        · exact Or.inr ⟨after,high⟩
    case pos.inr.inl.inr =>
      rename_i overlap _leftPart rightPart
      constructor
      · rintro ⟨low,high⟩
        exact ⟨⟨low,Nat.lt_trans high overlap.1⟩,Or.inl high⟩
      · rintro ⟨⟨low,high⟩,outside⟩
        rcases outside with before | after
        · exact ⟨low,before⟩
        · exact False.elim (Nat.not_lt_of_ge (Nat.le_trans rightPart after) high)
    case pos.inr.inr.inl =>
      rename_i overlap leftPart _rightPart
      constructor
      · rintro ⟨low,high⟩
        exact ⟨⟨Nat.le_trans (Nat.le_of_lt overlap.2) low,high⟩,Or.inr low⟩
      · rintro ⟨⟨low,high⟩,outside⟩
        rcases outside with before | after
        · exact False.elim (Nat.not_lt_of_ge (Nat.le_trans leftPart low) before)
        · exact ⟨after,high⟩
    case pos.inr.inr.inr =>
      rename_i _overlap leftPart rightPart
      intro low high
      exact ⟨Nat.le_trans leftPart low,Nat.lt_of_lt_of_le high rightPart⟩
  } {
    by_cases same : lane.allocation = allocation
    all_goals unfold clippedLane
    all_goals repeat' split
    all_goals apply Bool.eq_iff_iff.mpr
    all_goals simp_all [laneCovers,any_append]
    case pos.isTrue =>
      rename_i disjoint
      intro low high
      rcases disjoint with before | after
      · exact Or.inl (Nat.lt_of_lt_of_le high before)
      · exact Or.inr (Nat.le_trans after low)
    case pos.isFalse.isTrue.isTrue =>
      rename_i overlap _leftPart _rightPart
      constructor
      · intro covered
        rcases covered with ⟨low,high⟩ | ⟨low,high⟩
        · exact ⟨⟨low,Nat.lt_trans high overlap.1⟩,Or.inl high⟩
        · exact ⟨⟨Nat.le_trans (Nat.le_of_lt overlap.2) low,high⟩,Or.inr low⟩
      · rintro ⟨⟨low,high⟩,outside⟩
        rcases outside with before | after
        · exact Or.inl ⟨low,before⟩
        · exact Or.inr ⟨after,high⟩
    case pos.isFalse.isTrue.isFalse =>
      rename_i overlap _leftPart rightPart
      constructor
      · rintro ⟨low,high⟩
        exact ⟨⟨low,Nat.lt_trans high overlap.1⟩,Or.inl high⟩
      · rintro ⟨⟨low,high⟩,outside⟩
        rcases outside with before | after
        · exact ⟨low,before⟩
        · exact False.elim (Nat.not_lt_of_ge (Nat.le_trans rightPart after) high)
    case pos.isFalse.isFalse.isTrue =>
      rename_i overlap leftPart _rightPart
      constructor
      · rintro ⟨low,high⟩
        exact ⟨⟨Nat.le_trans (Nat.le_of_lt overlap.2) low,high⟩,Or.inr low⟩
      · rintro ⟨⟨low,high⟩,outside⟩
        rcases outside with before | after
        · exact False.elim (Nat.not_lt_of_ge (Nat.le_trans leftPart low) before)
        · exact ⟨after,high⟩
    case pos.isFalse.isFalse.isFalse =>
      rename_i _overlap leftPart rightPart
      intro low high
      exact ⟨Nat.le_trans leftPart low,Nat.lt_of_lt_of_le high rightPart⟩
  }

private theorem clipped_list_coverage (allocation : AllocId) (query address length : Nat)
    (lanes : List UnwrittenRange) :
    (trustIrListBind lanes (clippedLane address length)).any (laneCovers allocation query) =
      (lanes.any (laneCovers allocation query) && !(address ≤ query && query < address + length)) := by
  trustIrCompilerProof {
    induction lanes with
    | nil => simp only [List.nil_bind,List.any_nil,Bool.false_and]
    | cons first rest ih =>
      rw [List.cons_bind,any_append,clipped_lane_coverage,ih,List.any_cons,Bool.and_or_distrib_right]
  } {
    induction lanes with
    | nil => simp only [List.flatMap_nil,List.any_nil,Bool.false_and]
    | cons first rest ih =>
      rw [List.flatMap_cons,any_append,clipped_lane_coverage,ih,List.any_cons,Bool.and_or_distrib_right]
  }

/-- Exact coverage after clipping a write window: old coverage outside the
    half-open interval, no coverage inside it, for every allocation identity.
    No well-formedness assumption on the old record list is needed. -/
theorem Memory.forgetUnwritten_coverage (memory : Memory) (allocation : AllocId)
    (query address length : Nat) :
    (memory.forgetUnwritten address length).isUnwritten allocation query =
      (memory.isUnwritten allocation query && !(address ≤ query && query < address + length)) := by
  change ((memory.forgetUnwritten address length).unwritten.any (laneCovers allocation query)) =
    (memory.unwritten.any (laneCovers allocation query) && !(address ≤ query && query < address + length))
  by_cases zero : length = 0
  · subst length
    have empty : (decide (address ≤ query) && decide (query < address)) = false := by
      by_cases before : query < address
      · simp [before,Nat.not_le_of_lt before]
      · simp [before]
    cases rows : memory.unwritten <;>
      simp only [Memory.forgetUnwritten,rows,beq_self_eq_true,ite_true,Nat.add_zero,empty,Bool.not_false,Bool.and_true]
  · cases rows : memory.unwritten with
    | nil => simp only [Memory.forgetUnwritten,rows,List.any_nil,Bool.false_and]
    | cons first rest =>
      have nonzero : (length == 0) = false := by simp [zero]
      simp only [Memory.forgetUnwritten,rows,nonzero,Bool.false_eq_true,ite_false]
      exact clipped_list_coverage allocation query address length (first :: rest)

/-- Authoritative byte-image writes use exactly the clipping coverage law,
    regardless of whether the copied bytes are defined, absent or padding. -/
theorem Memory.writeImage_unwritten_coverage (memory : Memory) (allocation : AllocId)
    (query address : Nat) (image : ByteImage) :
    (memory.writeImage address image).isUnwritten allocation query =
      (memory.isUnwritten allocation query && !(address ≤ query && query < address + image.size)) := by
  have metadata : (memory.writeImage address image).unwritten =
      (memory.forgetUnwritten address image.size).unwritten := by
    by_cases zero : image.size = 0
    · cases rows : memory.unwritten <;> simp [Memory.writeImage,Memory.forgetUnwritten,zero,rows]
    · simp only [Memory.writeImage,zero,ite_false]
  unfold Memory.isUnwritten
  rw [metadata]
  exact memory.forgetUnwritten_coverage allocation query address image.size

theorem Memory.writeImage_unwritten_inside (memory : Memory) (allocation : AllocId)
    (query address : Nat) (image : ByteImage) (low : address ≤ query) (high : query < address + image.size) :
    (memory.writeImage address image).isUnwritten allocation query = false := by
  rw [memory.writeImage_unwritten_coverage]
  simp [low,high]

theorem Memory.writeImage_unwritten_outside (memory : Memory) (allocation : AllocId)
    (query address : Nat) (image : ByteImage) (outside : query < address ∨ address + image.size ≤ query) :
    (memory.writeImage address image).isUnwritten allocation query = memory.isUnwritten allocation query := by
  rw [memory.writeImage_unwritten_coverage]
  rcases outside with before | after
  · simp [Nat.not_le_of_lt before]
  · simp [Nat.not_lt_of_ge after]

/-- Byte copying cannot invent unwritten source-lane facts at any address. -/
theorem Memory.writeImage_no_new_unwritten (memory : Memory) (allocation : AllocId)
    (query address : Nat) (image : ByteImage) (clear : memory.isUnwritten allocation query = false) :
    (memory.writeImage address image).isUnwritten allocation query = false := by
  rw [memory.writeImage_unwritten_coverage,clear]
  rfl

theorem Memory.writeBytesMaybeUninit_unwritten_coverage (memory : Memory) (allocation : AllocId)
    (query address : Nat) (bytes : List (Option UInt8)) :
    (memory.writeBytesMaybeUninit address bytes).isUnwritten allocation query =
      (memory.isUnwritten allocation query && !(address ≤ query && query < address + bytes.length)) := by
  simpa only [Memory.writeBytesMaybeUninit,ByteImage.size_ofList] using
    memory.writeImage_unwritten_coverage allocation query address (ByteImage.ofList bytes)

theorem Memory.writeBytes_unwritten_coverage (memory : Memory) (allocation : AllocId)
    (query address : Nat) (bytes : List UInt8) :
    (memory.writeBytes address bytes).isUnwritten allocation query =
      (memory.isUnwritten allocation query && !(address ≤ query && query < address + bytes.length)) := by
  simpa only [Memory.writeBytes,ByteImage.size_ofList,List.length_map] using
    memory.writeImage_unwritten_coverage allocation query address (ByteImage.ofList (bytes.map some))

namespace AggregateMemory

/-- The actual final memory update for an ordinary encoded image clears old
    lane claims in the written window, preserves coverage outside, and adds no
    new claims. This is a publication law, not a successful Store execution. -/
theorem encode_ordinary_publication_coverage (model : ByteModel) (order : FunctionAddressOrder)
    (plan : Plan) (value : Value) (image : Image)
    (run : encode model order plan value false = .ok image)
    (memory : Memory) (allocation queryAllocation : AllocId) (address query : Nat) :
    ((memory.writeImage address image.bytes).recordUnwritten allocation address image.unwritten).isUnwritten
      queryAllocation query =
      (memory.isUnwritten queryAllocation query && !(address ≤ query && query < address + plan.layout.size)) := by
  rw [encode_ordinary_unwritten_empty model order plan value image run]
  change (memory.writeImage address image.bytes).isUnwritten queryAllocation query = _
  rw [memory.writeImage_unwritten_coverage,encode_extent model order plan value false image run]

end AggregateMemory
end TrustIr
