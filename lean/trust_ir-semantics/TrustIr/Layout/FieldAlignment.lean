-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Alignment
import TrustIr.Layout.Storage

namespace TrustIr.SourceLayout

/-- Every physical field retains an admitted alignment, including empty ones. -/
def FieldPowers (fields : List Field) : Prop :=
  ∀ field, field ∈ fields → powerOfTwo field.align = true

/-- Offsets remain aligned even for empty fields. The aggregate cap for direct
fields is required only for positive storage; enum rows require every cap. -/
def FieldAlignmentSummary (value : Summary) : Prop :=
  (∀ field, field ∈ value.fields → powerOfTwo field.align = true ∧
    field.offset % field.align = 0 ∧
    ∀ align, value.align = some align → field.size ≠ 0 → field.align ≤ align) ∧
  (∀ enumeration, value.enumeration = some enumeration →
    ∃ align, value.align = some align ∧
      ∀ fields, fields ∈ enumeration.variants → FieldPowers fields ∧ FieldsAligned (fun _ => True) align fields)

private theorem alignment_mem_append {α : Type} (value : α) (left right : List α) :
    value ∈ left ++ right ↔ value ∈ left ∨ value ∈ right := by
  induction left with
  | nil => simp
  | cons first rest ih => simp [List.cons_append, ih, or_assoc]

private theorem alignment_mem_reverse {α : Type} (value : α) (values : List α) :
    value ∈ values.reverse ↔ value ∈ values := by
  induction values with
  | nil => simp
  | cons first rest ih => simp [List.reverse_cons, alignment_mem_append, ih, or_comm]

theorem FieldPowers.reverse {fields : List Field} (safe : FieldPowers fields) : FieldPowers fields.reverse :=
  fun field member => safe field ((alignment_mem_reverse field fields).mp member)

theorem normalized_alignment_power (kind : String) (id clamp : Nat) (summary : Summary)
    (safe : BoundedAlignment summary) (clampValid : clamp = word64Max ∨ powerOfTwo clamp = true)
    (result : Nat)
    (run : ((do
      let natural ← match summary.align with
        | some align => pure align
        | none => throw (Error.incoherent kind id)
      pure (min (max 1 natural) clamp)) : Result Nat) = .ok result) : powerOfTwo result = true := by
  cases actual : summary.align with
  | none => simp [actual, Except.bind, Bind.bind, MonadExceptOf.throw] at run
  | some natural =>
    have power := (safe.2 natural actual).1
    have positive := powerOfTwo_nonzero natural power
    have bound : natural ≤ word64Max := by
      have word := safe.1.2
      rw [actual] at word
      simpa only [Nat.one_mul] using word
    simp only [actual, Except.bind, Bind.bind, Except.pure, Pure.pure] at run
    have same := Except.ok.inj run
    rw [← same, Nat.max_eq_right (by omega)]
    rcases clampValid with fixed | clamped
    · rw [fixed, Nat.min_eq_left bound]; exact power
    · rw [Nat.min_def]; split <;> assumption

private theorem canonical_update_field_powers (ty : Ty) (summary : Summary) (alignment : Result Nat)
    (before after : PlacementState) (safe : FieldPowers before.fields)
    (aligned : ∀ align, alignment = .ok align → powerOfTwo align = true)
    (updated : (do
      let align ← alignment
      let offset ← alignUp before.cursor align
      let cursor ← checked (offset + summary.size)
      pure ({ cursor, align := max before.align align, fields := { ty, offset, size := summary.size, align } :: before.fields } : PlacementState)) = .ok after) :
    FieldPowers after.fields := by
  cases alignmentRun : alignment with
  | error error => simp [alignmentRun, Except.bind, Bind.bind] at updated
  | ok align =>
    have fieldPower := aligned align alignmentRun
    simp only [alignmentRun, Except.bind, Bind.bind, Except.pure, Pure.pure] at updated
    cases offsetRun : alignUp before.cursor align with
    | error error => simp [offsetRun] at updated
    | ok offset =>
      simp only [offsetRun] at updated
      cases cursorRun : checked (offset + summary.size) with
      | error error => simp [cursorRun] at updated
      | ok cursor =>
        simp only [cursorRun] at updated
        cases updated
        intro field member
        cases member with
        | head => exact fieldPower
        | tail _ member => exact safe field member

private theorem declared_update_field_powers (kind : String) (id : Nat) (ty : Ty) (summary : Summary)
    (alignment offsetResult : Result Nat) (guard : Nat → Nat → Nat → Bool)
    (before after : PlacementState) (safe : FieldPowers before.fields)
    (aligned : ∀ align, alignment = .ok align → powerOfTwo align = true)
    (updated : (do
      let align ← alignment
      let offset ← offsetResult
      let limit ← checked (offset + summary.size)
      if guard align offset limit then throw (Error.incoherent kind id)
      pure ({ before with fields := { ty, offset, size := summary.size, align } :: before.fields } : PlacementState)) = .ok after) :
    FieldPowers after.fields := by
  cases alignmentRun : alignment with
  | error error => simp [alignmentRun, Except.bind, Bind.bind] at updated
  | ok align =>
    have fieldPower := aligned align alignmentRun
    simp only [alignmentRun, Except.bind, Bind.bind, Except.pure, Pure.pure] at updated
    cases offsetRun : offsetResult with
    | error error => simp [offsetRun] at updated
    | ok offset =>
      simp only [offsetRun] at updated
      cases limitRun : checked (offset + summary.size) with
      | error error => simp [limitRun] at updated
      | ok limit =>
        simp only [limitRun] at updated
        split at updated
        · cases updated
        · cases updated
          intro field member
          cases member with
          | head => exact fieldPower
          | tail _ member => exact safe field member

theorem canonicalFields_steps_field_powers (graph : Graph) (powers : graph.PowerAlignmentInvariant)
    (mode : Mode) (kind : String) (id : Nat) (fields : List (Ty × Nat))
    (first last : PlacementState) (safe : FieldPowers first.fields)
    (steps : StepsDerivation graph (canonicalFields mode kind id fields).steps first last) :
    FieldPowers last.fields := by
  induction fields generalizing first with
  | nil => cases steps; exact safe
  | cons entry rest ih =>
    rcases entry with ⟨ty, child⟩
    cases steps with
    | child solved updated later =>
      exact ih _ (canonical_update_field_powers ty _ _ _ _ safe
        (normalized_alignment_power kind id word64Max _ (solved.satisfies_at powers) (.inl rfl)) updated) later

theorem declaredFields_steps_field_powers (graph : Graph) (powers : graph.PowerAlignmentInvariant)
    (mode : Mode) (kind : String) (id size align clamp : Nat) (transparent : Bool)
    (fields : List (Ty × Option Nat × Nat)) (clampValid : clamp = word64Max ∨ powerOfTwo clamp = true)
    (first last : PlacementState) (safe : FieldPowers first.fields)
    (steps : StepsDerivation graph (declaredFields mode kind id size align clamp transparent fields).steps first last) :
    FieldPowers last.fields := by
  induction fields generalizing first with
  | nil => cases steps; exact safe
  | cons entry rest ih =>
    rcases entry with ⟨ty, declared, child⟩
    cases steps with
    | child solved updated later =>
      rename_i summary next
      have inserted : FieldPowers next.fields := by
        cases declared with
        | some offset =>
          exact declared_update_field_powers kind id ty summary _ (.ok offset)
            (fun fieldAlign offset limit => (true || mode == Mode.shape || kind != "struct") &&
              (offset % fieldAlign != 0 || fieldAlign > align || limit > size)) _ _ safe
            (normalized_alignment_power kind id clamp summary (solved.satisfies_at powers) clampValid) updated
        | none =>
          by_cases zero : summary.size = 0
          · have zeroTest : (summary.size == 0) = true := by simp [zero]
            simp only [zeroTest, ite_true] at updated
            exact declared_update_field_powers kind id ty summary _ (.ok 0)
              (fun fieldAlign offset limit => (false || mode == Mode.shape || kind != "struct") &&
                (offset % fieldAlign != 0 || fieldAlign > align || limit > size)) _ _ safe
              (normalized_alignment_power kind id clamp summary (solved.satisfies_at powers) clampValid) updated
          · have nonzero : (summary.size == 0) = false := by simp [zero]
            simp only [nonzero, Bool.false_eq_true, ite_false] at updated
            exact declared_update_field_powers kind id ty summary _ (.error (.incoherent kind id))
              (fun fieldAlign offset limit => (false || mode == Mode.shape || kind != "struct") &&
                (offset % fieldAlign != 0 || fieldAlign > align || limit > size)) _ _ safe
              (normalized_alignment_power kind id clamp summary (solved.satisfies_at powers) clampValid) updated
      exact ih _ inserted later

theorem Equation.Executes.canonicalFields_field_powers {graph : Graph} (powers : graph.PowerAlignmentInvariant)
    {value : Summary} (mode : Mode) (kind : String) (id : Nat) (fields : List (Ty × Nat))
    (run : (canonicalFields mode kind id fields).Executes graph value) : FieldPowers value.fields := by
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases initial
  have collected := canonicalFields_steps_field_powers graph powers mode kind id fields _ _
    (by intro field impossible; cases impossible) steps
  dsimp only [canonicalFields] at finished
  cases rounded : alignUp last.cursor last.align with
  | error error => simp [rounded, Except.bind, Bind.bind] at finished
  | ok size =>
    simp only [rounded, Except.bind, Bind.bind] at finished
    rw [((finish_ok_iff mode _ value).mp finished).1]
    exact collected.reverse

theorem Equation.Executes.declaredFields_field_powers {graph : Graph} (powers : graph.PowerAlignmentInvariant)
    {value : Summary} (mode : Mode) (kind : String) (id size align clamp : Nat) (transparent : Bool)
    (fields : List (Ty × Option Nat × Nat)) (clampValid : clamp = word64Max ∨ powerOfTwo clamp = true)
    (run : (declaredFields mode kind id size align clamp transparent fields).Executes graph value) :
    FieldPowers value.fields := by
  rcases run with ⟨first, last, initial, steps, finished⟩
  have header := declaredFields_initial_facts mode kind id size align clamp transparent fields first initial
  have empty := header.2.2.2
  subst first
  have collected := declaredFields_steps_field_powers graph powers mode kind id size align clamp transparent fields
    clampValid _ _ (by intro field impossible; cases impossible) steps
  rw [declaredFields_finish_exact mode kind id size align clamp transparent fields last value finished]
  exact collected.reverse

theorem FieldAlignmentSummary.empty {value : Summary}
    (fields : value.fields = []) (enumeration : value.enumeration = none) : FieldAlignmentSummary value := by
  constructor
  · rw [fields]; intro field impossible; cases impossible
  · intro actual impossible; rw [enumeration] at impossible; cases impossible

theorem FieldAlignmentSummary.of_geometry {value : Summary} {required : Field → Prop}
    (powers : FieldPowers value.fields) (geometry : AlignmentGeometry required value)
    (positiveRequired : ∀ field, field.size ≠ 0 → required field)
    (enumeration : value.enumeration = none) : FieldAlignmentSummary value := by
  rcases geometry with ⟨align, present, nonzero, multiple, fields⟩
  constructor
  · intro field member
    have aligned := fields field member
    refine ⟨powers field member, aligned.2.1, ?_⟩
    intro actual same positive
    rw [present] at same
    cases same
    exact aligned.2.2 (positiveRequired field positive)
  · intro actual impossible; rw [enumeration] at impossible; cases impossible

/-- Local field safety may use the separately proved alignment invariant in
this exact graph; it cannot assume arbitrary child summaries are authentic. -/
def Equation.FieldAlignmentGuarded (equation : Equation) : Prop :=
  ∀ graph, graph.PowerAlignmentInvariant → ∀ value, equation.Executes graph value → FieldAlignmentSummary value

theorem Equation.FieldAlignmentGuarded.failed (error : Error) :
    (Equation.done (.error error)).FieldAlignmentGuarded := by
  intro graph powers value run
  rcases run with ⟨first, last, impossible, steps, finished⟩
  cases impossible

theorem Equation.FieldAlignmentGuarded.done (result : Result Summary)
    (safe : ∀ value, result = .ok value → FieldAlignmentSummary value) :
    (Equation.done result).FieldAlignmentGuarded := by
  intro graph powers value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases steps
  exact safe value (initial.trans finished)

theorem Equation.FieldAlignmentGuarded.canonicalFields (mode : Mode) (kind : String) (id : Nat)
    (fields : List (Ty × Nat)) : (canonicalFields mode kind id fields).FieldAlignmentGuarded := by
  intro graph powers value run
  have geometry := run.canonicalFields_alignment mode kind id fields
  have fieldPowers := run.canonicalFields_field_powers powers mode kind id fields
  apply FieldAlignmentSummary.of_geometry fieldPowers geometry (fun _ _ => trivial)
  rcases run with ⟨first, last, initial, steps, finished⟩
  dsimp only [TrustIr.SourceLayout.canonicalFields] at finished
  cases rounded : alignUp last.cursor last.align with
  | error error => simp [rounded, Except.bind, Bind.bind] at finished
  | ok size =>
    simp only [rounded, Except.bind, Bind.bind] at finished
    rw [((finish_ok_iff mode _ value).mp finished).1]

theorem Equation.FieldAlignmentGuarded.declaredFields (mode : Mode) (kind : String)
    (id size align clamp : Nat) (transparent : Bool) (fields : List (Ty × Option Nat × Nat))
    (clampValid : clamp = word64Max ∨ powerOfTwo clamp = true) :
    (declaredFields mode kind id size align clamp transparent fields).FieldAlignmentGuarded := by
  intro graph powers value run
  have geometry := run.declaredFields_alignment mode kind id size align clamp transparent fields
  have fieldPowers := run.declaredFields_field_powers powers mode kind id size align clamp transparent fields clampValid
  apply FieldAlignmentSummary.of_geometry fieldPowers geometry (fun field positive => Or.inl positive)
  rcases run with ⟨first, last, initial, steps, finished⟩
  rw [declaredFields_finish_exact mode kind id size align clamp transparent fields last value finished]

theorem Equation.FieldAlignmentGuarded.scaled (mode : Mode) (count child : Nat) :
    (scaled mode count child).FieldAlignmentGuarded := by
  intro graph powers value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases steps with
  | child solved updated later =>
    cases later
    cases finished
    dsimp only [scaled] at updated
    simp only [Except.bind, Bind.bind] at updated
    split at updated
    · cases updated
    · rw [((finish_ok_iff mode _ _).mp updated).1]
      exact FieldAlignmentSummary.empty rfl rfl

theorem Equation.FieldAlignmentGuarded.sequence (children : List Nat) {next : Equation}
    (safe : next.FieldAlignmentGuarded) : (Equation.sequence children next).FieldAlignmentGuarded :=
  fun graph powers value run => safe graph powers value run.sequence_body

theorem Equation.FieldAlignmentGuarded.unit (steps : List (Step Unit)) :
    ({ kind := .unit, initial := .ok (), steps, finish := fun _ => .ok { size := 0, align := some 1 } } : Equation).FieldAlignmentGuarded := by
  intro graph powers value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases finished
  exact FieldAlignmentSummary.empty rfl rfl

theorem ScalarSummary.field_alignment (model : ByteModel) {value : Summary}
    (scalar : ScalarSummary model.pointerBytes value) : FieldAlignmentSummary value := by
  cases scalar <;> exact FieldAlignmentSummary.empty rfl rfl

/-- Persistent rules may rely on a separately established invariant in the
actual future graph, while retaining exact dynamic child equations. -/
def Equation.PersistentRule (environment : Graph → Prop) (property : Summary → Prop)
    (lower : Nat) (graph : Graph) (equation : Equation) : Prop :=
  ∀ after, graph.DynamicExtends lower after → environment after →
    equation.ContextualRule after (fun _ value => property value) 0

def Graph.PersistentInvariant (environment : Graph → Prop) (property : Summary → Prop)
    (lower : Nat) (graph : Graph) : Prop :=
  ∀ node equation, graph.nodes.find node = some equation → equation.PersistentRule environment property lower graph

theorem Equation.PersistentRule.weaken {environment : Graph → Prop} {property : Summary → Prop}
    {lower : Nat} {before after : Graph} {equation : Equation}
    (safe : equation.PersistentRule environment property lower before)
    (extended : before.DynamicExtends lower after) : equation.PersistentRule environment property lower after :=
  fun next growth ready => safe next (extended.trans growth) ready

theorem Graph.PersistentInvariant.contextual {environment : Graph → Prop} {property : Summary → Prop}
    {lower : Nat} {graph : Graph} (safe : graph.PersistentInvariant environment property lower)
    (ready : environment graph) : graph.ContextualInvariant (fun _ value => property value) := by
  intro node equation found
  exact ((safe node equation found) graph (Graph.DynamicExtends.refl lower graph) ready).reowner (fun _ good => good)

theorem Graph.PersistentInvariant.empty (environment : Graph → Prop) (property : Summary → Prop) (lower count : Nat) :
    ({ count } : Graph).PersistentInvariant environment property lower := by
  intro node equation impossible
  cases impossible

theorem Graph.PersistentInvariant.insert {environment : Graph → Prop} {property : Summary → Prop}
    {lower : Nat} {graph : Graph} (safe : graph.PersistentInvariant environment property lower)
    (node : Nat) (equation : Equation)
    (extended : graph.DynamicExtends lower { graph with nodes := graph.nodes.insert node equation })
    (guarded : equation.PersistentRule environment property lower graph) :
    ({ graph with nodes := graph.nodes.insert node equation } : Graph).PersistentInvariant environment property lower := by
  intro child original found
  change (graph.nodes.insert node equation).find child = some original at found
  rw [NatIndexTree.find_insert] at found
  by_cases same : child = node
  · rw [if_pos same] at found
    cases found
    exact guarded.weaken extended
  · rw [if_neg same] at found
    exact (safe child original found).weaken extended

theorem Graph.PersistentInvariant.allocate {environment : Graph → Prop} {property : Summary → Prop}
    {lower : Nat} {graph : Graph} (safe : graph.PersistentInvariant environment property lower)
    (bounded : graph.Bounded) (equation : Equation) (guarded : equation.PersistentRule environment property lower graph) :
    ({ graph with nodes := graph.nodes.insert graph.count equation, count := graph.count + 1 } : Graph).PersistentInvariant environment property lower :=
  safe.insert graph.count equation ((Graph.Extends.allocate bounded equation).dynamic lower) guarded

theorem Graph.PersistentInvariant.put_below {environment : Graph → Prop} {property : Summary → Prop}
    {lower : Nat} {graph : Graph} (safe : graph.PersistentInvariant environment property lower)
    (node : Nat) (inside : node < lower) (equation : Equation)
    (guarded : equation.PersistentRule environment property lower graph) :
    ({ graph with nodes := graph.nodes.insert node equation } : Graph).PersistentInvariant environment property lower :=
  safe.insert node equation (Graph.DynamicExtends.put_below graph lower node inside equation) guarded

theorem Graph.PersistentInvariant.leaves {environment : Graph → Prop} {property : Summary → Prop}
    {lower : Nat} {graph : Graph} (safe : graph.PersistentInvariant environment property lower) (leaves : NatIndexTree Nat) :
    ({ graph with leaves } : Graph).PersistentInvariant environment property lower := by
  intro node equation found
  exact (safe node equation found).weaken (fun _ _ _ old => old)

abbrev Equation.FieldAlignmentRule (lower : Nat) (graph : Graph) (equation : Equation) :=
  equation.PersistentRule Graph.PowerAlignmentInvariant FieldAlignmentSummary lower graph

abbrev Graph.FieldAlignmentInvariant (lower : Nat) (graph : Graph) :=
  graph.PersistentInvariant Graph.PowerAlignmentInvariant FieldAlignmentSummary lower

theorem Equation.FieldAlignmentGuarded.rule {equation : Equation} (safe : equation.FieldAlignmentGuarded)
    (lower : Nat) (graph : Graph) : equation.FieldAlignmentRule lower graph := by
  intro after extended powers first last value initial steps finished
  exact safe after powers value ⟨first, last, initial, steps.derivation, finished⟩

theorem Equation.FieldAlignmentRule.alias (lower : Nat) (graph : Graph) (child : Nat) :
    (Equation.alias child).FieldAlignmentRule lower graph :=
  fun after extended powers => Equation.ContextualRule.alias after 0 child (fun _ safe => safe)

/-- Canonical rows have their own aggregate alignment; descriptor rows must
have the descriptor's exact alignment. Every physical row checks all caps. -/
def VariantAligned (parent : Option Nat) (value : Summary) : Prop :=
  ∃ align, value.align = some align ∧ FieldPowers value.fields ∧
    FieldsAligned (fun _ => True) align value.fields ∧
    ∀ expected, parent = some expected → align = expected

def Equation.VariantAlignmentGuarded (parent : Option Nat) (equation : Equation) : Prop :=
  ∀ graph, graph.PowerAlignmentInvariant → ∀ value, equation.Executes graph value → VariantAligned parent value

theorem Equation.VariantAlignmentGuarded.failed (parent : Option Nat) (error : Error) :
    (Equation.done (.error error)).VariantAlignmentGuarded parent := by
  intro graph powers value run
  rcases run with ⟨first, last, impossible, steps, finished⟩
  cases impossible

theorem Equation.VariantAlignmentGuarded.canonicalFields (mode : Mode) (id : Nat) (fields : List (Ty × Nat)) :
    (canonicalFields mode "enum" id fields).VariantAlignmentGuarded none := by
  intro graph powers value run
  have fieldPowers := run.canonicalFields_field_powers powers mode "enum" id fields
  rcases run.canonicalFields_alignment mode "enum" id fields with ⟨align, present, nonzero, multiple, aligned⟩
  exact ⟨align, present, fieldPowers, aligned, by intro expected impossible; cases impossible⟩

theorem Equation.VariantAlignmentGuarded.declaredFields (mode : Mode) (id size align : Nat)
    (fields : List (Ty × Option Nat × Nat)) :
    (declaredFields mode "enum" id size align word64Max false fields).VariantAlignmentGuarded (some align) := by
  intro graph powers value run
  have fieldPowers := run.declaredFields_field_powers powers mode "enum" id size align word64Max false fields (.inl rfl)
  have header := run.declaredFields_power_of_two mode "enum" id size align word64Max false fields
  rcases run.declaredFields_alignment mode "enum" id size align word64Max false fields with
    ⟨actual, present, nonzero, multiple, aligned⟩
  have same : actual = align := Option.some.inj (present.symm.trans header.1)
  subst actual
  refine ⟨align, present, fieldPowers, aligned.weaken (fun field needed => Or.inr (Or.inr (by decide))), ?_⟩
  intro expected exactParent
  cases exactParent
  rfl

def Graph.VariantAlignmentCertificates (parent : Option Nat) (nodes : List Nat) (graph : Graph) : Prop :=
  ∀ node, node ∈ nodes → ∃ equation, graph.nodes.find node = some equation ∧ equation.VariantAlignmentGuarded parent

theorem Graph.VariantAlignmentCertificates.weaken {parent : Option Nat} {nodes : List Nat} {before after : Graph}
    (safe : before.VariantAlignmentCertificates parent nodes) (extended : before.Extends after) :
    after.VariantAlignmentCertificates parent nodes := by
  intro node member
  rcases safe node member with ⟨equation, found, guarded⟩
  exact ⟨equation, extended node equation found, guarded⟩

theorem Graph.VariantAlignmentCertificates.reverse {parent : Option Nat} {nodes : List Nat} {graph : Graph}
    (safe : graph.VariantAlignmentCertificates parent nodes) : graph.VariantAlignmentCertificates parent nodes.reverse :=
  fun node member => safe node ((alignment_mem_reverse node nodes).mp member)

theorem Graph.VariantAlignmentCertificates.allocate {parent : Option Nat} {nodes : List Nat} {graph : Graph}
    (safe : graph.VariantAlignmentCertificates parent nodes) (bounded : graph.Bounded)
    (equation : Equation) (guarded : equation.VariantAlignmentGuarded parent) :
    ({ graph with nodes := graph.nodes.insert graph.count equation, count := graph.count + 1 } : Graph).VariantAlignmentCertificates parent (graph.count :: nodes) := by
  have old := safe.weaken (Graph.Extends.allocate bounded equation)
  intro node member
  cases member with
  | head =>
    refine ⟨equation, ?_, guarded⟩
    change (graph.nodes.insert graph.count equation).find graph.count = some equation
    rw [NatIndexTree.find_insert, if_pos rfl]
  | tail _ member => exact old node member

theorem Graph.VariantAlignmentCertificates.dynamic_weaken {parent : Option Nat} {nodes : List Nat}
    {lower : Nat} {before after : Graph} (safe : before.VariantAlignmentCertificates parent nodes)
    (outside : ∀ child, child ∈ nodes → lower ≤ child) (extended : before.DynamicExtends lower after) :
    after.VariantAlignmentCertificates parent nodes := by
  intro child member
  rcases safe child member with ⟨equation, found, guarded⟩
  exact ⟨equation, extended child equation (outside child member) found, guarded⟩

theorem Graph.VariantAlignmentCertificates.child {parent : Option Nat} {nodes : List Nat} {graph : Graph}
    (safe : graph.VariantAlignmentCertificates parent nodes) (powers : graph.PowerAlignmentInvariant)
    {node : Nat} (member : node ∈ nodes) {value : Summary} (derived : NodeDerivation graph node value) :
    VariantAligned parent value := by
  rcases safe node member with ⟨equation, found, guarded⟩
  exact guarded graph powers value (derived.execution found)

theorem FieldPowers.translate (offset : Nat) {fields : List Field} (safe : FieldPowers fields) :
    FieldPowers (fields.map (fun field => { field with offset := offset + field.offset })) := by
  intro field member
  rcases List.mem_map.mp member with ⟨original, present, same⟩
  subst field
  exact safe original present

/-- Alignment survives payload relocation because the admitted field
alignment divides the payload alignment, which divides the actual offset. -/
theorem FieldsAligned.translate (offset payloadAlign parentAlign childAlign : Nat) {fields : List Field}
    (powers : FieldPowers fields) (safe : FieldsAligned (fun _ => True) childAlign fields)
    (childBound : childAlign ≤ payloadAlign) (payloadPower : powerOfTwo payloadAlign = true)
    (offsetAligned : offset % payloadAlign = 0) (parentBound : payloadAlign ≤ parentAlign) :
    FieldsAligned (fun _ => True) parentAlign
      (fields.map (fun field => { field with offset := offset + field.offset })) := by
  intro field member
  rcases List.mem_map.mp member with ⟨original, present, same⟩
  subst field
  have aligned := safe original present
  have cap := aligned.2.2 trivial
  have divides := powerOfTwo_dvd_of_le (powers original present) payloadPower (Nat.le_trans cap childBound)
  have offsetDivides := Nat.dvd_trans divides (Nat.dvd_of_mod_eq_zero offsetAligned)
  have offsetMultiple := Nat.mod_eq_zero_of_dvd offsetDivides
  refine ⟨aligned.1, ?_, fun _ => Nat.le_trans cap (Nat.le_trans childBound parentBound)⟩
  change (offset + original.offset) % original.align = 0
  simp [Nat.add_mod, offsetMultiple, aligned.2.1]

private theorem fold_alignment_monotone (variants : List Summary) (initial : Nat) :
    initial ≤ variants.foldl (fun out value => max out (value.align.getD 1)) initial := by
  induction variants generalizing initial with
  | nil => exact Nat.le_refl _
  | cons first rest ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem variant_alignment_le_payload (variants : List Summary) (summary : Summary) (member : summary ∈ variants) :
    summary.align.getD 1 ≤ variants.foldl (fun out value => max out (value.align.getD 1)) 1 := by
  have bound : ∀ initial, summary.align.getD 1 ≤
      variants.foldl (fun out value => max out (value.align.getD 1)) initial := by
    induction variants with
    | nil => cases member
    | cons first rest ih =>
      intro initial
      cases member with
      | head => exact Nat.le_trans (Nat.le_max_right _ _) (fold_alignment_monotone rest _)
      | tail _ later => exact ih later _
  exact bound 1

theorem EnumConstruction.canonical_field_alignment {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output)
    (canonical : definition.layout = none)
    (children : ∀ value, value ∈ variants → PowerAlignment value ∧ VariantAligned none value) :
    FieldAlignmentSummary output := by
  rcases constructed.canonical_view canonical with ⟨offset, extent, size, placed, bounded, rounded, finished⟩
  rw [((finish_ok_iff mode _ output).mp finished).1]
  constructor
  · intro field impossible; cases impossible
  · intro enumeration actual
    cases actual
    refine ⟨_, rfl, ?_⟩
    intro fields member
    rcases List.mem_map.mp member with ⟨summary, present, same⟩
    subst fields
    rcases (children summary present).2 with ⟨childAlign, childPresent, fieldPowers, aligned, exactParent⟩
    have childBound := variant_alignment_le_payload variants summary present
    rw [childPresent] at childBound
    exact ⟨fieldPowers.translate offset, FieldsAligned.translate offset _ _ childAlign fieldPowers aligned childBound
      (payload_alignment_power variants (fun value member => (children value member).1))
      (alignUp_aligned _ _ _ placed).2 (Nat.le_max_right _ _)⟩

theorem EnumConstruction.descriptor_field_alignment {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output)
    (descriptor : EnumLayoutDescriptor) (authored : definition.layout = some descriptor)
    (children : ∀ value, value ∈ variants → VariantAligned (some descriptor.align) value) :
    FieldAlignmentSummary output := by
  rw [constructed.descriptor_exact descriptor authored]
  constructor
  · intro field impossible; cases impossible
  · intro enumeration actual
    cases actual
    refine ⟨descriptor.align, rfl, ?_⟩
    intro fields member
    rcases List.mem_map.mp member with ⟨summary, present, same⟩
    subst fields
    rcases children summary present with ⟨align, childPresent, fieldPowers, aligned, exactParent⟩
    rw [exactParent descriptor.align rfl] at aligned
    exact ⟨fieldPowers, aligned⟩

theorem Equation.FieldAlignmentRule.enumeration (lower : Nat) (graph : Graph)
    (mode : Mode) (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat)
    (children : graph.VariantAlignmentCertificates (definition.layout.map (·.align)) nodes)
    (outside : ∀ child, child ∈ nodes → lower ≤ child) :
    (enumEquation mode definition uninhabited nodes).FieldAlignmentRule lower graph := by
  intro after extended powers first last value initial steps finished
  have run : (enumEquation mode definition uninhabited nodes).Executes after value :=
    ⟨first, last, initial, steps.derivation, finished⟩
  have certificates := children.dynamic_weaken outside extended
  cases authored : definition.layout with
  | none =>
    rw [authored] at certificates
    rcases run.canonicalEnum_view mode definition uninhabited nodes authored with
      ⟨tag, values, state, tagged, numbered, collected, constructed⟩
    have valid := enum_children_property after (fun value => PowerAlignment value ∧ VariantAligned none value)
      nodes [] state (by intro value impossible; cases impossible)
      (fun node member summary derived =>
        ⟨(derived.satisfies_at powers).2, certificates.child powers member derived⟩) collected
    exact constructed.canonical_field_alignment authored
      (fun summary member => valid summary ((alignment_mem_reverse summary state).mp member))
  | some descriptor =>
    rw [authored] at certificates
    rcases run.descriptorEnum_view mode definition uninhabited nodes descriptor authored with
      ⟨tag, values, state, tagged, numbered, admitted, collected, constructed⟩
    have valid := enum_children_property after (VariantAligned (some descriptor.align)) nodes [] state
      (by intro value impossible; cases impossible)
      (fun node member summary derived => certificates.child powers member derived) collected
    exact constructed.descriptor_field_alignment descriptor authored
      (fun summary member => valid summary ((alignment_mem_reverse summary state).mp member))

end TrustIr.SourceLayout
