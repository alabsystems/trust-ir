-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Bounds

namespace TrustIr.SourceLayout

/-- Positive-size byte intervals do not intersect. Empty fields may share
an offset, including an offset inside another field's storage. -/
def Field.Separated (left right : Field) : Prop :=
  left.size = 0 ∨ right.size = 0 ∨ left.offset + left.size ≤ right.offset ∨
    right.offset + right.size ≤ left.offset

theorem Field.Separated.symm {left right : Field} (safe : left.Separated right) :
    right.Separated left := by
  rcases safe with zero | zero | before | after
  · exact .inr (.inl zero)
  · exact .inl zero
  · exact .inr (.inr (.inr before))
  · exact .inr (.inr (.inl after))

theorem overlap_false_iff_separated (left right : Field) :
    overlap left.offset left.size right.offset right.size = false ↔ left.Separated right := by
  by_cases leftZero : left.size = 0 <;> by_cases rightZero : right.size = 0 <;>
    by_cases before : left.offset < right.offset + right.size <;>
    by_cases after : right.offset < left.offset + left.size <;>
    simp_all [overlap, Field.Separated] <;> omega

/-- Every ordered pair of distinct occurrences has disjoint positive storage. -/
def FieldsSeparated : List Field → Prop
  | [] => True
  | first :: rest => (∀ other, other ∈ rest → first.Separated other) ∧ FieldsSeparated rest

private theorem any_false_iff {α : Type} (predicate : α → Bool) (values : List α) :
    values.any predicate = false ↔ ∀ value, value ∈ values → predicate value = false := by
  induction values with
  | nil => simp
  | cons first rest ih => simp [List.any_cons, Bool.or_eq_false_iff, ih, List.forall_mem_cons]

theorem hasOverlap_false_iff_separated (fields : List Field) :
    hasOverlap fields = false ↔ FieldsSeparated fields := by
  induction fields with
  | nil => simp [hasOverlap, FieldsSeparated]
  | cons first rest ih =>
    simp only [hasOverlap, Bool.or_eq_false_iff, any_false_iff, ih, FieldsSeparated]
    constructor
    · intro safe
      exact ⟨fun other member => (overlap_false_iff_separated first other).mp (safe.1 other member), safe.2⟩
    · intro safe
      exact ⟨fun other member => (overlap_false_iff_separated first other).mpr (safe.1 other member), safe.2⟩

private theorem field_mem_append (field : Field) (left right : List Field) :
    field ∈ left ++ right ↔ field ∈ left ∨ field ∈ right := by
  induction left with
  | nil => simp
  | cons first rest ih => simp [List.cons_append, ih, or_assoc]

private theorem field_mem_reverse (field : Field) (fields : List Field) :
    field ∈ fields.reverse ↔ field ∈ fields := by
  induction fields with
  | nil => simp
  | cons first rest ih => simp [List.reverse_cons, field_mem_append, ih, or_comm]

theorem FieldsSeparated.snoc {fields : List Field} {last : Field}
    (safe : FieldsSeparated fields) (apart : ∀ field, field ∈ fields → field.Separated last) :
    FieldsSeparated (fields ++ [last]) := by
  induction fields with
  | nil => simp [FieldsSeparated]
  | cons first rest ih =>
    refine ⟨?_, ih safe.2 (fun field member => apart field (List.mem_cons_of_mem _ member))⟩
    intro field member
    rcases (field_mem_append field rest [last]).mp member with old | final
    · exact safe.1 field old
    · have same : field = last := by simpa using final
      subst field
      exact apart first ((trustIrListMemConsSelf _ _))

theorem FieldsSeparated.reverse {fields : List Field} (safe : FieldsSeparated fields) :
    FieldsSeparated fields.reverse := by
  induction fields with
  | nil => trivial
  | cons first rest ih =>
    rw [List.reverse_cons]
    exact (ih safe.2).snoc (fun field member =>
      (safe.1 field ((field_mem_reverse field rest).mp member)).symm)

/-- Field storage lies within the owning summary, without asserting codec,
source-type identity or stronger alignment properties. -/
def FieldsContained (size : Nat) (fields : List Field) : Prop :=
  ∀ field, field ∈ fields → field.offset + field.size ≤ size

def FieldGeometry (value : Summary) : Prop :=
  FieldsSeparated value.fields ∧ FieldsContained value.size value.fields

theorem FieldsContained.reverse {size : Nat} {fields : List Field}
    (safe : FieldsContained size fields) : FieldsContained size fields.reverse :=
  fun field member => safe field ((field_mem_reverse field fields).mp member)

theorem alignUp_lower_bound (offset align result : Nat) (success : alignUp offset align = .ok result) :
    offset ≤ result := by
  unfold alignUp at success
  split at success
  · cases success
  · have exactValue := checked_ok _ _ success
    omega

theorem alignUp_aligned (offset align result : Nat) (success : alignUp offset align = .ok result) :
    align ≠ 0 ∧ result % align = 0 := by
  unfold alignUp at success
  split at success
  · cases success
  · rename_i nonzero
    have exactValue := checked_ok _ _ success
    refine ⟨nonzero, ?_⟩
    rw [exactValue.1, Nat.add_mod_mod, ← Nat.mod_add_mod offset align (align - offset % align)]
    have remainder := Nat.mod_lt offset (by omega : 0 < align)
    have sum : offset % align + (align - offset % align) = align := by omega
    rw [sum, Nat.mod_self]

/-- Canonical placement retains both separation and the running extent. -/
def PlacementGeometry (state : PlacementState) : Prop :=
  FieldsSeparated state.fields ∧ FieldsContained state.cursor state.fields

theorem PlacementGeometry.empty : PlacementGeometry ({} : PlacementState) :=
  ⟨trivial, by intro field impossible; cases impossible⟩

private theorem canonical_update_geometry (ty : Ty) (summary : Summary) (alignment : Result Nat)
    (before after : PlacementState) (safe : PlacementGeometry before)
    (updated : (do
      let align ← alignment
      let offset ← alignUp before.cursor align
      let cursor ← checked (offset + summary.size)
      pure ({ cursor, align := max before.align align, fields := { ty, offset, size := summary.size, align } :: before.fields } : PlacementState)) = .ok after) :
    PlacementGeometry after := by
  cases alignmentRun : alignment with
  | error error => simp [alignmentRun, Bind.bind, Except.bind] at updated
  | ok align =>
    simp only [alignmentRun, Bind.bind, Except.bind, Pure.pure, Except.pure] at updated
    cases offsetRun : alignUp before.cursor align with
    | error error => simp [offsetRun] at updated
    | ok offset =>
      simp only [offsetRun] at updated
      cases cursorRun : checked (offset + summary.size) with
      | error error => simp [cursorRun] at updated
      | ok cursor =>
        simp only [cursorRun] at updated
        cases updated
        have lower := alignUp_lower_bound before.cursor align offset offsetRun
        have limit := (checked_ok _ _ cursorRun).1
        refine ⟨⟨?_, safe.1⟩, ?_⟩
        · intro field member
          exact Or.inr (Or.inr (Or.inr (Nat.le_trans (safe.2 field member) lower)))
        · intro field member
          cases member with
          | head => change offset + summary.size ≤ cursor; omega
          | tail _ member => have old := safe.2 field member; change field.offset + field.size ≤ cursor; omega

theorem canonicalFields_steps_geometry (graph : Graph) (mode : Mode) (kind : String) (id : Nat)
    (fields : List (Ty × Nat)) (first last : PlacementState) (safe : PlacementGeometry first)
    (steps : StepsDerivation graph (canonicalFields mode kind id fields).steps first last) :
    PlacementGeometry last := by
  induction fields generalizing first with
  | nil => cases steps; exact safe
  | cons entry rest ih =>
    rcases entry with ⟨ty, child⟩
    cases steps with
    | child solved updated later =>
      exact ih _ (canonical_update_geometry ty _ _ _ _ safe updated) later

theorem Equation.Executes.canonicalFields_geometry {graph : Graph} {value : Summary}
    (mode : Mode) (kind : String) (id : Nat) (fields : List (Ty × Nat))
    (run : (canonicalFields mode kind id fields).Executes graph value) : FieldGeometry value := by
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases initial
  have placed := canonicalFields_steps_geometry graph mode kind id fields _ _ PlacementGeometry.empty steps
  dsimp only [canonicalFields] at finished
  cases aligned : alignUp last.cursor last.align with
  | error error => simp [aligned, Bind.bind, Except.bind] at finished
  | ok size =>
    simp only [aligned, Bind.bind, Except.bind] at finished
    have same := (finish_ok_iff mode _ value).mp finished
    rw [same.1]
    refine ⟨placed.1.reverse, ?_⟩
    apply FieldsContained.reverse
    intro field member
    exact Nat.le_trans (placed.2 field member) (alignUp_lower_bound _ _ _ aligned)

theorem declaredFields_finish_fields (mode : Mode) (kind : String) (id size align clamp : Nat)
    (transparent : Bool) (fields : List (Ty × Option Nat × Nat)) (state : PlacementState) (value : Summary)
    (success : (declaredFields mode kind id size align clamp transparent fields).finish state = .ok value) :
    value.size = size ∧ value.fields = state.fields.reverse ∧ FieldsSeparated value.fields := by
  dsimp only [declaredFields] at success
  simp only [Except.bind, Except.pure, Bind.bind, Pure.pure, MonadExceptOf.throw] at success
  split at success
  · cases success
  · rename_i accepted
    have noOverlap : hasOverlap state.fields = false := by
      cases h : hasOverlap state.fields <;> simp_all
    have separated := ((hasOverlap_false_iff_separated state.fields).mp noOverlap).reverse
    repeat first
      | (have exactValue := (finish_ok_iff mode _ value).mp success
         rw [exactValue.1]
         exact ⟨rfl, rfl, separated⟩)
      | (split at success)
      | cases success

theorem declaredFields_finalizes_separated (mode : Mode) (kind : String) (id size align clamp : Nat)
    (transparent : Bool) (fields : List (Ty × Option Nat × Nat)) :
    (declaredFields mode kind id size align clamp transparent fields).Finalizes
      (fun value => FieldsSeparated value.fields) :=
  fun state value success => (declaredFields_finish_fields mode kind id size align clamp transparent fields
    state value success).2.2

private theorem declared_update_contained (mode : Mode) (kind : String) (id size align : Nat)
    (ty : Ty) (declared : Option Nat) (summary : Summary) (alignment : Result Nat)
    (before after : PlacementState) (safe : FieldsContained size before.fields)
    (updated : (do
      let fieldAlign ← alignment
      let offset ← match declared with
        | some offset => pure offset
        | none => if summary.size == 0 then pure 0 else throw (Error.incoherent kind id)
      let limit ← checked (offset + summary.size)
      if (declared.isSome || mode == Mode.shape || kind != "struct") &&
          (offset % fieldAlign != 0 || fieldAlign > align || limit > size) then
        throw (Error.incoherent kind id)
      pure ({ before with fields := { ty, offset, size := summary.size, align := fieldAlign } :: before.fields } : PlacementState))
      = .ok after) : FieldsContained size after.fields := by
  cases alignmentRun : alignment with
  | error error => simp [alignmentRun, Bind.bind, Except.bind] at updated
  | ok fieldAlign =>
    cases declared with
    | some offset =>
      simp only [alignmentRun, Option.isSome, Bool.true_or, Bool.true_and,
        Bind.bind, Except.bind, Pure.pure, Except.pure] at updated
      cases limitRun : checked (offset + summary.size) with
      | error error => simp [limitRun] at updated
      | ok limit =>
        simp only [limitRun] at updated
        have fits : limit ≤ size := by
          by_cases fits : limit ≤ size
          · exact fits
          · have bad : size < limit := by omega
            simp [bad, MonadExceptOf.throw] at updated
        split at updated
        · cases updated
        · cases updated
          have exactLimit := (checked_ok _ _ limitRun).1
          intro field member
          cases member with
          | head => change offset + summary.size ≤ size; omega
          | tail _ member => exact safe field member
    | none =>
      by_cases zero : summary.size = 0
      · simp only [alignmentRun, zero, beq_self_eq_true, ite_true, Bind.bind, Except.bind,
          Pure.pure, Except.pure] at updated
        cases limitRun : checked (0 + 0) with
        | error error => simp [limitRun] at updated
        | ok limit =>
          simp only [limitRun] at updated
          split at updated
          · cases updated
          · cases updated
            intro field member
            cases member with
            | head => change 0 + 0 ≤ size; omega
            | tail _ member => exact safe field member
      · have nonzero : (summary.size == 0) = false := by simp [zero]
        simp [alignmentRun, nonzero, Bind.bind, Except.bind, MonadExceptOf.throw] at updated

theorem declaredFields_steps_contained (graph : Graph) (mode : Mode) (kind : String)
    (id size align clamp : Nat) (transparent : Bool) (fields : List (Ty × Option Nat × Nat))
    (first last : PlacementState) (safe : FieldsContained size first.fields)
    (steps : StepsDerivation graph (declaredFields mode kind id size align clamp transparent fields).steps first last) :
    FieldsContained size last.fields := by
  induction fields generalizing first with
  | nil => cases steps; exact safe
  | cons entry rest ih =>
    rcases entry with ⟨ty, declared, child⟩
    cases steps with
    | child solved updated later =>
      exact ih _ (declared_update_contained mode kind id size align ty declared _ _ _ _ safe updated) later

theorem Equation.Executes.declaredFields_geometry {graph : Graph} {value : Summary}
    (mode : Mode) (kind : String) (id size align clamp : Nat) (transparent : Bool)
    (fields : List (Ty × Option Nat × Nat))
    (run : (declaredFields mode kind id size align clamp transparent fields).Executes graph value) :
    FieldGeometry value := by
  rcases run with ⟨first, last, initial, steps, finished⟩
  have empty : first = ({} : PlacementState) := by
    dsimp only [declaredFields] at initial
    split at initial
    · cases initial
    · exact (Except.ok.inj initial).symm
  subst first
  have contained := declaredFields_steps_contained graph mode kind id size align clamp transparent fields _ _
    (by intro field impossible; cases impossible) steps
  have snapshot := declaredFields_finish_fields mode kind id size align clamp transparent fields last value finished
  exact ⟨snapshot.2.2, by rw [snapshot.1, snapshot.2.1]; exact contained.reverse⟩

/-- Every field has a nonzero divisor and aligned offset. Required positions
also have alignment no greater than the enclosing aggregate. -/
def FieldsAligned (required : Field → Prop) (align : Nat) (fields : List Field) : Prop :=
  ∀ field, field ∈ fields →
    field.align ≠ 0 ∧ field.offset % field.align = 0 ∧ (required field → field.align ≤ align)

def AlignmentGeometry (required : Field → Prop) (value : Summary) : Prop :=
  ∃ align, value.align = some align ∧ align ≠ 0 ∧ value.size % align = 0 ∧
    FieldsAligned required align value.fields

theorem FieldsAligned.reverse {required : Field → Prop} {align : Nat} {fields : List Field}
    (safe : FieldsAligned required align fields) : FieldsAligned required align fields.reverse :=
  fun field member => safe field ((field_mem_reverse field fields).mp member)

theorem FieldsAligned.weaken {strong weak : Field → Prop} {align : Nat} {fields : List Field}
    (safe : FieldsAligned strong align fields) (implies : ∀ field, weak field → strong field) :
    FieldsAligned weak align fields := by
  intro field member
  have actual := safe field member
  exact ⟨actual.1, actual.2.1, fun needed => actual.2.2 (implies field needed)⟩

theorem AlignmentGeometry.weaken {strong weak : Field → Prop} {value : Summary}
    (safe : AlignmentGeometry strong value) (implies : ∀ field, weak field → strong field) :
    AlignmentGeometry weak value := by
  rcases safe with ⟨align, actual, positive, multiple, fields⟩
  exact ⟨align, actual, positive, multiple, fields.weaken implies⟩

private theorem canonical_update_aligned (ty : Ty) (summary : Summary) (alignment : Result Nat)
    (before after : PlacementState) (safe : FieldsAligned (fun _ => True) before.align before.fields)
    (updated : (do
      let align ← alignment
      let offset ← alignUp before.cursor align
      let cursor ← checked (offset + summary.size)
      pure ({ cursor, align := max before.align align, fields := { ty, offset, size := summary.size, align } :: before.fields } : PlacementState)) = .ok after) :
    FieldsAligned (fun _ => True) after.align after.fields := by
  cases alignmentRun : alignment with
  | error error => simp [alignmentRun, Bind.bind, Except.bind] at updated
  | ok align =>
    simp only [alignmentRun, Bind.bind, Except.bind, Pure.pure, Except.pure] at updated
    cases offsetRun : alignUp before.cursor align with
    | error error => simp [offsetRun] at updated
    | ok offset =>
      simp only [offsetRun] at updated
      cases cursorRun : checked (offset + summary.size) with
      | error error => simp [cursorRun] at updated
      | ok cursor =>
        simp only [cursorRun] at updated
        cases updated
        have aligned := alignUp_aligned before.cursor align offset offsetRun
        intro field member
        cases member with
        | head => exact ⟨aligned.1, aligned.2, fun _ => Nat.le_max_right _ _⟩
        | tail _ member =>
          have old := safe field member
          exact ⟨old.1, old.2.1, fun _ => Nat.le_trans (old.2.2 trivial) (Nat.le_max_left _ _)⟩

theorem canonicalFields_steps_aligned (graph : Graph) (mode : Mode) (kind : String) (id : Nat)
    (fields : List (Ty × Nat)) (first last : PlacementState)
    (safe : FieldsAligned (fun _ => True) first.align first.fields)
    (steps : StepsDerivation graph (canonicalFields mode kind id fields).steps first last) :
    FieldsAligned (fun _ => True) last.align last.fields := by
  induction fields generalizing first with
  | nil => cases steps; exact safe
  | cons entry rest ih =>
    rcases entry with ⟨ty, child⟩
    cases steps with
    | child solved updated later =>
      exact ih _ (canonical_update_aligned ty _ _ _ _ safe updated) later

theorem Equation.Executes.canonicalFields_alignment {graph : Graph} {value : Summary}
    (mode : Mode) (kind : String) (id : Nat) (fields : List (Ty × Nat))
    (run : (canonicalFields mode kind id fields).Executes graph value) :
    AlignmentGeometry (fun _ => True) value := by
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases initial
  have placed := canonicalFields_steps_aligned graph mode kind id fields _ _
    (by intro field impossible; cases impossible) steps
  dsimp only [canonicalFields] at finished
  cases aligned : alignUp last.cursor last.align with
  | error error => simp [aligned, Bind.bind, Except.bind] at finished
  | ok size =>
    simp only [aligned, Bind.bind, Except.bind] at finished
    have same := (finish_ok_iff mode _ value).mp finished
    rw [same.1]
    have alignedSize := alignUp_aligned last.cursor last.align size aligned
    exact ⟨last.align, rfl, alignedSize.1, alignedSize.2, placed.reverse⟩

/-- Omitted zero-sized execution struct positions retain their intentional
metadata exception. Shape and non-struct aggregates check every position. -/
def FieldAlignmentRequired (mode : Mode) (kind : String) (field : Field) : Prop :=
  field.size ≠ 0 ∨ mode = .shape ∨ kind ≠ "struct"

private theorem normalized_alignment_positive (kind : String) (id clamp : Nat) (summary : Summary)
    (positive : clamp ≠ 0) (result : Nat)
    (run : ((do
      let natural ← match summary.align with
        | some align => pure align
        | none => throw (Error.incoherent kind id)
      pure (min (max 1 natural) clamp)) : Result Nat) = .ok result) : result ≠ 0 := by
  cases h : summary.align with
  | none => simp [h, Bind.bind, Except.bind, MonadExceptOf.throw] at run
  | some natural =>
    simp only [h, Bind.bind, Except.bind, Pure.pure, Except.pure] at run
    cases run
    have lower := Nat.le_max_left 1 natural
    rw [Nat.min_def]
    split <;> omega

private theorem alignment_guard_facts {α : Type} (kind : String) (id offset fieldAlign align limit size : Nat)
    (value after : α)
    (run : (if offset % fieldAlign != 0 || fieldAlign > align || limit > size then
      (Except.error (Error.incoherent kind id) : Result α) else .ok value) = .ok after) :
    offset % fieldAlign = 0 ∧ fieldAlign ≤ align ∧ after = value := by
  have aligned : offset % fieldAlign = 0 := by
    by_cases good : offset % fieldAlign = 0
    · exact good
    · simp [good] at run
  have capped : fieldAlign ≤ align := by
    by_cases good : fieldAlign ≤ align
    · exact good
    · have bad : align < fieldAlign := by omega
      simp [bad] at run
  refine ⟨aligned, capped, ?_⟩
  split at run
  · cases run
  · exact (Except.ok.inj run).symm

private theorem declared_update_aligned (mode : Mode) (kind : String) (id size align : Nat)
    (ty : Ty) (declared : Option Nat) (summary : Summary) (alignment : Result Nat)
    (before after : PlacementState)
    (positive : ∀ result, alignment = .ok result → result ≠ 0)
    (safe : FieldsAligned (FieldAlignmentRequired mode kind) align before.fields)
    (updated : (do
      let fieldAlign ← alignment
      let offset ← match declared with
        | some offset => pure offset
        | none => if summary.size == 0 then pure 0 else throw (Error.incoherent kind id)
      let limit ← checked (offset + summary.size)
      if (declared.isSome || mode == Mode.shape || kind != "struct") &&
          (offset % fieldAlign != 0 || fieldAlign > align || limit > size) then
        throw (Error.incoherent kind id)
      pure ({ before with fields := { ty, offset, size := summary.size, align := fieldAlign } :: before.fields } : PlacementState))
      = .ok after) : FieldsAligned (FieldAlignmentRequired mode kind) align after.fields := by
  cases alignmentRun : alignment with
  | error error => simp [alignmentRun, Bind.bind, Except.bind] at updated
  | ok fieldAlign =>
    have nonzero := positive fieldAlign alignmentRun
    cases declared with
    | some offset =>
      simp only [alignmentRun, Option.isSome, Bool.true_or, Bool.true_and,
        Bind.bind, Except.bind, Pure.pure, Except.pure, MonadExceptOf.throw] at updated
      cases limitRun : checked (offset + summary.size) with
      | error error => simp [limitRun] at updated
      | ok limit =>
        simp only [limitRun] at updated
        have facts := alignment_guard_facts kind id offset fieldAlign align limit size _ after updated
        rw [facts.2.2]
        intro field member
        cases member with
        | head => exact ⟨nonzero, facts.1, fun _ => facts.2.1⟩
        | tail _ member => exact safe field member
    | none =>
      by_cases zero : summary.size = 0
      · simp only [alignmentRun, zero, beq_self_eq_true, ite_true, Bind.bind, Except.bind,
          Pure.pure, Except.pure, MonadExceptOf.throw] at updated
        cases limitRun : checked (0 + 0) with
        | error error => simp [limitRun] at updated
        | ok limit =>
          simp only [limitRun] at updated
          by_cases strict : mode = .shape ∨ kind ≠ "struct"
          · have mandatory : (Option.isSome (none : Option Nat) || mode == Mode.shape || kind != "struct") = true := by
              rcases strict with shape | nonstruct
              · subst mode; rfl
              · simp [nonstruct]
            simp only [mandatory, Bool.true_and] at updated
            have facts := alignment_guard_facts kind id 0 fieldAlign align limit size _ after updated
            rw [facts.2.2]
            intro field member
            cases member with
            | head => exact ⟨nonzero, facts.1, fun _ => facts.2.1⟩
            | tail _ member => exact safe field member
          · split at updated
            · cases updated
            · cases updated
              intro field member
              cases member with
              | head =>
                refine ⟨nonzero, Nat.zero_mod _, ?_⟩
                intro needed
                rcases needed with impossible | shape | nonstruct
                · exact False.elim (impossible rfl)
                · exact False.elim (strict (.inl shape))
                · exact False.elim (strict (.inr nonstruct))
              | tail _ member => exact safe field member
      · have nonzeroSize : (summary.size == 0) = false := by simp [zero]
        simp [alignmentRun, nonzeroSize, Bind.bind, Except.bind, MonadExceptOf.throw] at updated

theorem declaredFields_steps_aligned (graph : Graph) (mode : Mode) (kind : String)
    (id size align clamp : Nat) (transparent : Bool) (fields : List (Ty × Option Nat × Nat))
    (positive : clamp ≠ 0) (first last : PlacementState)
    (safe : FieldsAligned (FieldAlignmentRequired mode kind) align first.fields)
    (steps : StepsDerivation graph (declaredFields mode kind id size align clamp transparent fields).steps first last) :
    FieldsAligned (FieldAlignmentRequired mode kind) align last.fields := by
  induction fields generalizing first with
  | nil => cases steps; exact safe
  | cons entry rest ih =>
    rcases entry with ⟨ty, declared, child⟩
    cases steps with
    | child solved updated later =>
      exact ih _ (declared_update_aligned mode kind id size align ty declared _ _ _ _
        (normalized_alignment_positive kind id clamp _ positive) safe updated) later

theorem declaredFields_finish_exact (mode : Mode) (kind : String) (id size align clamp : Nat)
    (transparent : Bool) (fields : List (Ty × Option Nat × Nat)) (state : PlacementState) (value : Summary)
    (success : (declaredFields mode kind id size align clamp transparent fields).finish state = .ok value) :
    value = { size, align := some align, fields := state.fields.reverse } := by
  dsimp only [declaredFields] at success
  simp only [Except.bind, Except.pure, Bind.bind, Pure.pure, MonadExceptOf.throw] at success
  repeat first
    | exact ((finish_ok_iff mode _ value).mp success).1
    | (split at success)
    | cases success

theorem powerOfTwo_nonzero (align : Nat) (power : powerOfTwo align = true) : align ≠ 0 := by
  intro zero
  simp [zero, powerOfTwo] at power

theorem declaredFields_initial_facts (mode : Mode) (kind : String) (id size align clamp : Nat)
    (transparent : Bool) (fields : List (Ty × Option Nat × Nat)) (first : PlacementState)
    (initial : (declaredFields mode kind id size align clamp transparent fields).initial = .ok first) :
    powerOfTwo align = true ∧ size % align = 0 ∧ align ≤ clamp ∧ first = ({} : PlacementState) := by
  dsimp only [declaredFields] at initial
  have power : powerOfTwo align = true := by
    cases h : powerOfTwo align <;> simp_all
  have multiple : size % align = 0 := by
    by_cases good : size % align = 0
    · exact good
    · simp [good] at initial
  have capped : align ≤ clamp := by
    by_cases good : align ≤ clamp
    · exact good
    · have bad : clamp < align := by omega
      simp [bad] at initial
  refine ⟨power, multiple, capped, ?_⟩
  split at initial
  · cases initial
  · exact (Except.ok.inj initial).symm

theorem Equation.Executes.declaredFields_power_of_two {graph : Graph} {value : Summary}
    (mode : Mode) (kind : String) (id size align clamp : Nat) (transparent : Bool)
    (fields : List (Ty × Option Nat × Nat))
    (run : (declaredFields mode kind id size align clamp transparent fields).Executes graph value) :
    value.align = some align ∧ powerOfTwo align = true := by
  rcases run with ⟨first, last, initial, steps, finished⟩
  have admitted := declaredFields_initial_facts mode kind id size align clamp transparent fields first initial
  rw [declaredFields_finish_exact mode kind id size align clamp transparent fields last value finished]
  exact ⟨rfl, admitted.1⟩

theorem Equation.Executes.declaredFields_alignment {graph : Graph} {value : Summary}
    (mode : Mode) (kind : String) (id size align clamp : Nat) (transparent : Bool)
    (fields : List (Ty × Option Nat × Nat))
    (run : (declaredFields mode kind id size align clamp transparent fields).Executes graph value) :
    AlignmentGeometry (FieldAlignmentRequired mode kind) value := by
  rcases run with ⟨first, last, initial, steps, finished⟩
  have header := declaredFields_initial_facts mode kind id size align clamp transparent fields first initial
  have admitted : align ≠ 0 ∧ size % align = 0 ∧ align ≤ clamp ∧ first = ({} : PlacementState) :=
    ⟨powerOfTwo_nonzero align header.1, header.2⟩
  have positive : clamp ≠ 0 := by have nonzero := admitted.1; have capped := admitted.2.2.1; omega
  have empty := admitted.2.2.2
  subst first
  have placed := declaredFields_steps_aligned graph mode kind id size align clamp transparent fields positive _ _
    (by intro field impossible; cases impossible) steps
  rw [declaredFields_finish_exact mode kind id size align clamp transparent fields last value finished]
  exact ⟨align, rfl, admitted.1, admitted.2.1, placed.reverse⟩

/-- The actual alignment checks carry the aggregate-kind and mode boundary. -/
def Equation.AlignmentGuarded (mode : Mode) (kind : String) (equation : Equation) : Prop :=
  ∀ graph value, equation.Executes graph value → AlignmentGeometry (FieldAlignmentRequired mode kind) value

theorem Equation.AlignmentGuarded.failed (mode : Mode) (kind : String) (error : Error) :
    (Equation.done (.error error)).AlignmentGuarded mode kind := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases initial

theorem Equation.AlignmentGuarded.canonicalFields (mode : Mode) (kind : String) (id : Nat)
    (fields : List (Ty × Nat)) : (canonicalFields mode kind id fields).AlignmentGuarded mode kind :=
  fun _ _ run => (run.canonicalFields_alignment mode kind id fields).weaken (fun _ _ => trivial)

theorem Equation.AlignmentGuarded.declaredFields (mode : Mode) (kind : String) (id size align clamp : Nat)
    (transparent : Bool) (fields : List (Ty × Option Nat × Nat)) :
    (declaredFields mode kind id size align clamp transparent fields).AlignmentGuarded mode kind :=
  fun _ _ run => run.declaredFields_alignment mode kind id size align clamp transparent fields

theorem Equation.AlignmentGuarded.sequence (mode : Mode) (kind : String) (children : List Nat) {next : Equation}
    (safe : next.AlignmentGuarded mode kind) : (Equation.sequence children next).AlignmentGuarded mode kind :=
  fun _ _ run => safe _ _ run.sequence_body

theorem NodeDerivation.alignment_geometry {graph : Graph} {node : Nat} {value : Summary} {equation : Equation}
    (mode : Mode) (kind : String) (found : graph.nodes.find node = some equation)
    (safe : equation.AlignmentGuarded mode kind) (derived : NodeDerivation graph node value) :
    AlignmentGeometry (FieldAlignmentRequired mode kind) value :=
  safe graph value (NodeDerivation.execution found derived)

/-- Storage geometry is checked by the actual ordered execution. -/
def Equation.FieldGuarded (equation : Equation) : Prop :=
  ∀ graph value, equation.Executes graph value → FieldGeometry value

theorem Equation.FieldGuarded.failed (error : Error) :
    (Equation.done (.error error)).FieldGuarded := by
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases initial

theorem Equation.FieldGuarded.canonicalFields (mode : Mode) (kind : String) (id : Nat)
    (fields : List (Ty × Nat)) : (canonicalFields mode kind id fields).FieldGuarded :=
  fun _ _ run => run.canonicalFields_geometry mode kind id fields

theorem Equation.FieldGuarded.declaredFields (mode : Mode) (kind : String) (id size align clamp : Nat)
    (transparent : Bool) (fields : List (Ty × Option Nat × Nat)) :
    (declaredFields mode kind id size align clamp transparent fields).FieldGuarded :=
  fun _ _ run => run.declaredFields_geometry mode kind id size align clamp transparent fields

theorem Equation.FieldGuarded.sequence (children : List Nat) {next : Equation}
    (safe : next.FieldGuarded) : (Equation.sequence children next).FieldGuarded :=
  fun _ _ run => safe _ _ run.sequence_body

theorem NodeDerivation.field_geometry {graph : Graph} {node : Nat} {value : Summary} {equation : Equation}
    (found : graph.nodes.find node = some equation) (safe : equation.FieldGuarded)
    (derived : NodeDerivation graph node value) : FieldGeometry value :=
  safe graph value (NodeDerivation.execution found derived)

end TrustIr.SourceLayout
