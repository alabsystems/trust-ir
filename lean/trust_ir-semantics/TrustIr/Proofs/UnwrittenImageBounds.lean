-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.OrdinaryImageMetadata

namespace TrustIr.AggregateMemory

private theorem mem_append_cases {α : Type} {value : α} (left right : List α)
    (member : value ∈ left ++ right) : value ∈ left ∨ value ∈ right := by
  induction left with
  | nil => exact Or.inr member
  | cons first rest ih =>
    cases member with
    | head => exact Or.inl (List.Mem.head _)
    | tail _ member =>
      rcases ih member with earlier | later
      · exact Or.inl (List.Mem.tail _ earlier)
      · exact Or.inr later


/-- Every explicit lane record lies inside the actual retained image. Absent
    padding and overlap/initialization validity are separate properties. -/
def Image.UnwrittenBounded (image : Image) : Prop :=
  ∀ start count, (start,count) ∈ image.unwritten → start + count ≤ image.bytes.size

theorem Image.unwritten_bounded_of_empty (image : Image) (empty : image.unwritten = []) :
    image.UnwrittenBounded := by
  intro start count member
  simp only [empty,List.not_mem_nil] at member

/-- Successful field overwrites bound every shifted child record by the actual
    parent image, retaining any already bounded incoming records. -/
theorem FieldsEncoded.unwritten_bounded {model : ByteModel} {order : FunctionAddressOrder}
    {fields : List (Nat × Plan)} {values : List Value} {allow : Bool} {before after : Image}
    (children : ∀ offset child, (offset,child) ∈ fields → ∀ value image,
      encode model order child value allow = .ok image → image.UnwrittenBounded)
    (initial : before.UnwrittenBounded)
    (run : FieldsEncoded model order fields values allow before after) : after.UnwrittenBounded := by
  induction fields generalizing values before with
  | nil =>
    obtain ⟨_,rfl⟩ := FieldsEncoded.nil_iff.mp run
    exact initial
  | cons field rest ih =>
    obtain ⟨offset,plan⟩ := field
    obtain ⟨value,later,child,bytes,rfl,encoded,written,remaining⟩ := run.head
    have childBounded := children offset plan (by simp) value child encoded
    have fits := written.lane.1
    have extent := written.extent
    apply ih (by
      intro offset child member
      exact children offset child (List.mem_cons_of_mem _ member)) ?_ remaining
    intro start count member
    rcases mem_append_cases _ _ member with earlier | shifted
    · have bound := initial start count earlier
      simpa only [extent] using bound
    · obtain ⟨lane,member,same⟩ := List.mem_map.mp shifted
      obtain ⟨childStart,childCount⟩ := lane
      have bound := childBounded childStart childCount member
      cases same
      dsimp only at fits extent ⊢
      omega

/-- Every real successful encoding, including the special unwritten path,
    confines its explicit records to its actual byte extent. No source-origin
    or decoder equation is required. -/
theorem encode_unwritten_bounded (model : ByteModel) (order : FunctionAddressOrder)
    (plan : Plan) (value : Value) (allow : Bool) (image : Image)
    (run : encode model order plan value allow = .ok image) : image.UnwrittenBounded := by
  by_cases whole : value = .uninit
  · subst value
    rw [encode_uninit_exact] at run
    cases allow with
    | false => cases run
    | true =>
      simp only [ite_true,Except.ok.injEq] at run
      cases run
      intro start count member
      simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
      obtain ⟨rfl,rfl⟩ := member
      simp only [Nat.zero_add,ByteImage.size_fill]
      exact Nat.le_refl _
  · have initialized : value.isUninit = false := by
      cases value <;> first | rfl | exact False.elim (whole rfl)
    cases plan with
    | leaf ty layout =>
      have ordinary : encode model order (.leaf ty layout) value false = .ok image := by
        rw [encode] at run ⊢
        simpa only [initialized,Bool.false_eq_true,ite_false] using run
      exact image.unwritten_bounded_of_empty (encode_ordinary_unwritten_empty model order _ value image ordinary)
    | array ty layout count element =>
      have ordinary : encode model order (.array ty layout count element) value false = .ok image := by
        rw [encode] at run ⊢
        simpa only [initialized,Bool.false_eq_true,ite_false] using run
      exact image.unwritten_bounded_of_empty (encode_ordinary_unwritten_empty model order _ value image ordinary)
    | enumeration ty layout info variants =>
      have ordinary : encode model order (.enumeration ty layout info variants) value false = .ok image := by
        rw [encode] at run ⊢
        simpa only [initialized,Bool.false_eq_true,ite_false] using run
      exact image.unwritten_bounded_of_empty (encode_ordinary_unwritten_empty model order _ value image ordinary)
    | fields ty layout fields =>
      rw [encode] at run
      simp only [initialized,Bool.false_eq_true,ite_false,Bind.bind,Except.bind,Pure.pure,Except.pure] at run
      cases value <;> try cases run
      rename_i values
      apply FieldsEncoded.unwritten_bounded (before := { bytes := ByteImage.fill layout.size none }) ?_ ?_ run
      · intro offset child _member input stored encoded
        exact encode_unwritten_bounded model order child input allow stored encoded
      · exact Image.unwritten_bounded_of_empty _ rfl
termination_by sizeOf plan
decreasing_by
  simp_wf
  have inside := List.sizeOf_lt_of_mem _member
  simp_all
  omega

/-- The same bound in the retained source plan's declared byte extent. -/
theorem encode_unwritten_plan_bounds (model : ByteModel) (order : FunctionAddressOrder)
    (plan : Plan) (value : Value) (allow : Bool) (image : Image)
    (run : encode model order plan value allow = .ok image)
    (start count : Nat) (member : (start,count) ∈ image.unwritten) : start + count ≤ plan.layout.size := by
  have bound := encode_unwritten_bounded model order plan value allow image run start count member
  simpa only [encode_extent model order plan value allow image run] using bound

private theorem filter_map_property {α β : Type} (select : α → Option β) (rows : List α) (property : β → Prop)
    (safe : ∀ row ∈ rows, ∀ value, select row = some value → property value) :
    ∀ value ∈ rows.filterMap select, property value := by
  induction rows with
  | nil => intro value member; cases member
  | cons head rest ih =>
    intro value member
    cases selected : select head <;> simp only [List.filterMap,selected] at member
    · exact ih (fun row member => safe row (.tail _ member)) value member
    · cases member with
      | head => exact safe head (.head _) _ selected
      | tail _ member => exact ih (fun row member => safe row (.tail _ member)) value member

/-- Registration retains old records verbatim or adds a nonempty range with
    the requested allocation, wholly within the actual destination window.
    Bounds on unrelated preexisting records are deliberately not assumed. -/
theorem Image.recordUnwritten_bounds (image : Image) (bounded : image.UnwrittenBounded)
    (memory : Memory) (allocation : AllocId) (address : Nat) (lane : UnwrittenRange)
    (member : lane ∈ (memory.recordUnwritten allocation address image.unwritten).unwritten) :
    lane ∈ memory.unwritten ∨
      lane.allocation = allocation ∧ address ≤ lane.start ∧ lane.start < lane.stop ∧
        lane.stop ≤ address + image.bytes.size := by
  cases entries : image.unwritten with
  | nil =>
    simp only [entries,Memory.recordUnwritten] at member
    exact Or.inl member
  | cons first rest =>
    simp only [entries,Memory.recordUnwritten] at member
    rcases mem_append_cases _ _ member with earlier | registered
    · exact Or.inl earlier
    · apply Or.inr
      refine filter_map_property _ _ (fun lane => lane.allocation = allocation ∧ address ≤ lane.start ∧
        lane.start < lane.stop ∧ lane.stop ≤ address + image.bytes.size) ?_ lane registered
      intro row inside actual selected
      obtain ⟨start,count⟩ := row
      have bound := bounded start count (by rw [entries]; exact inside)
      by_cases zero : count = 0
      · simp [zero] at selected
      · simp [zero] at selected
        cases selected
        refine ⟨rfl,?_,?_,?_⟩
        · dsimp only; omega
        · exact Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero zero)
        · dsimp only; omega

/-- Actual successful source encoding supplies the registration bound without
    a caller-provided lane extent certificate. -/
theorem encode_registered_unwritten_bounds (model : ByteModel) (order : FunctionAddressOrder)
    (plan : Plan) (value : Value) (allow : Bool) (image : Image)
    (run : encode model order plan value allow = .ok image)
    (memory : Memory) (allocation : AllocId) (address : Nat) (lane : UnwrittenRange)
    (member : lane ∈ (memory.recordUnwritten allocation address image.unwritten).unwritten) :
    lane ∈ memory.unwritten ∨
      lane.allocation = allocation ∧ address ≤ lane.start ∧ lane.start < lane.stop ∧
        lane.stop ≤ address + plan.layout.size := by
  have bound := image.recordUnwritten_bounds (encode_unwritten_bounded model order plan value allow image run)
    memory allocation address lane member
  simpa only [encode_extent model order plan value allow image run] using bound

end TrustIr.AggregateMemory
