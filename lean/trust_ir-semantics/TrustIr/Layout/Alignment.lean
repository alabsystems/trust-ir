-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.EnumGeometry
import TrustIr.Layout.Scalar

namespace TrustIr.SourceLayout

private theorem high_bit (value exponent : Nat)
    (lower : 2 ^ exponent ≤ value) (upper : value < 2 ^ (exponent + 1)) :
    value.testBit exponent = true := by
  trustIrCompilerProof {
    have quotient : value / 2 ^ exponent = 1 :=
      Nat.div_eq_of_lt_le (by simpa using lower) (by simpa [Nat.pow_succ, Nat.mul_comm] using upper)
    rw [Nat.testBit_to_div_mod, quotient]
    rfl
  } {
    exact Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt lower upper
  }

/-- The actual bitwise admission predicate accepts exactly powers of two. -/
theorem powerOfTwo_iff_power (value : Nat) :
    powerOfTwo value = true ↔ ∃ exponent, value = 2 ^ exponent := by
  constructor
  · intro accepted
    have positive := powerOfTwo_nonzero value accepted
    have lower := Nat.log2_self_le positive
    have upper := Nat.lt_log2_self (n := value)
    refine ⟨value.log2, ?_⟩
    by_cases exactValue : value = 2 ^ value.log2
    · exact exactValue
    · have previous : 2 ^ value.log2 ≤ value - 1 := by omega
      have bit := high_bit value value.log2 lower upper
      have previousBit := high_bit (value - 1) value.log2 previous (by omega)
      have zero : value &&& (value - 1) = 0 := by
        by_cases good : value &&& (value - 1) = 0
        · exact good
        · simp [powerOfTwo, good] at accepted
      have same := congrArg (fun n : Nat => n.testBit value.log2) zero
      simp only [Nat.testBit_and, bit, previousBit, Bool.true_and, Nat.zero_testBit] at same <;> cases same
  · rintro ⟨exponent, rfl⟩
    have positive : 2 ^ exponent ≠ 0 := Nat.ne_of_gt (Nat.two_pow_pos exponent)
    trustIrCompilerProof {
      simp [powerOfTwo, positive, Nat.and_pow_two_is_mod]
    } {
      simp [powerOfTwo, positive, Nat.and_two_pow_sub_one_eq_mod]
    }

theorem powerOfTwo_max {left right : Nat} (leftPower : powerOfTwo left = true)
    (rightPower : powerOfTwo right = true) : powerOfTwo (max left right) = true := by
  rw [Nat.max_def]
  split <;> assumption

/-- The size ordering of admitted alignments also gives divisibility. -/
theorem powerOfTwo_dvd_of_le {small large : Nat} (smallPower : powerOfTwo small = true)
    (largePower : powerOfTwo large = true) (ordered : small ≤ large) : small ∣ large := by
  rcases (powerOfTwo_iff_power small).mp smallPower with ⟨smallExp, rfl⟩
  rcases (powerOfTwo_iff_power large).mp largePower with ⟨largeExp, rfl⟩
  exact (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mpr
    ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp ordered)

/-- Absent alignment stays absent. Every present aggregate alignment is a
power of two and divides the aggregate size. -/
def PowerAlignment (value : Summary) : Prop :=
  ∀ align, value.align = some align → powerOfTwo align = true ∧ value.size % align = 0

/-- Word bounds justify the canonical field normalizer's upper clamp. -/
def BoundedAlignment (value : Summary) : Prop := WordBounds 1 value ∧ PowerAlignment value

abbrev Graph.PowerAlignmentInvariant (graph : Graph) :=
  graph.IndexedInvariant (fun _ value => BoundedAlignment value)

abbrev Equation.PowerAlignmentRule (owner : Nat) (equation : Equation) :=
  equation.IndexedRule (fun _ value => BoundedAlignment value) owner

theorem ScalarSummary.power_alignment (model : ByteModel) {value : Summary}
    (scalar : ScalarSummary model.pointerBytes value) : PowerAlignment value := by
  cases scalar with
  | plain size allowed =>
    rcases allowed with same | same | same | same | same | same <;> subst size
    all_goals cases model <;> intro align actual <;> cases actual <;> decide
  | fat => cases model <;> intro align actual <;> cases actual <;> decide
  | unit => intro align actual; cases actual; decide
  | never => intro align impossible; cases impossible

theorem PowerAlignment.of_finish {mode : Mode} {input value : Summary}
    (safe : PowerAlignment input) (finished : finish mode input = .ok value) : PowerAlignment value :=
  ((finish_ok_iff mode input value).mp finished).1 ▸ safe

theorem BoundedAlignment.of_finish {mode : Mode} {input value : Summary}
    (safe : PowerAlignment input) (finished : finish mode input = .ok value) : BoundedAlignment value := by
  have result := (finish_ok_iff mode input value).mp finished
  rw [result.1]
  exact ⟨result.2.1, safe⟩

private theorem normalized_word_alignment_power (kind : String) (id : Nat) (summary : Summary)
    (safe : BoundedAlignment summary) (result : Nat)
    (run : ((do
      let natural ← match summary.align with
        | some align => pure align
        | none => throw (Error.incoherent kind id)
      pure (min (max 1 natural) word64Max)) : Result Nat) = .ok result) :
    powerOfTwo result = true := by
  cases actual : summary.align with
  | none => simp [actual, Except.bind, Bind.bind, MonadExceptOf.throw] at run
  | some natural =>
    have power := (safe.2 natural actual).1
    have positive := powerOfTwo_nonzero natural power
    have bound : natural ≤ word64Max := by
      have word := safe.1.2
      rw [actual] at word
      simpa only [Nat.one_mul] using word
    have normal : min (max 1 natural) word64Max = natural := by
      rw [Nat.max_eq_right (by omega), Nat.min_eq_left bound]
    simp only [actual, Except.bind, Bind.bind, Except.pure, Pure.pure] at run
    have same := Except.ok.inj run
    rw [← same, normal]
    exact power

private theorem placement_update_power (ty : Ty) (summary : Summary) (alignment : Result Nat)
    (before after : PlacementState) (safe : powerOfTwo before.align = true)
    (aligned : ∀ align, alignment = .ok align → powerOfTwo align = true)
    (updated : (do
      let align ← alignment
      let offset ← alignUp before.cursor align
      let cursor ← checked (offset + summary.size)
      pure ({ cursor, align := max before.align align, fields := { ty, offset, size := summary.size, align } :: before.fields } : PlacementState)) = .ok after) :
    powerOfTwo after.align = true := by
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
        exact powerOfTwo_max safe fieldPower

theorem canonicalFields_steps_power (mode : Mode) (kind : String) (id : Nat)
    (fields : List (Ty × Nat)) (first last : PlacementState) (safe : powerOfTwo first.align = true)
    (steps : StepsInvariantAt (fun _ value => BoundedAlignment value)
      (canonicalFields mode kind id fields).steps first last) : powerOfTwo last.align = true := by
  induction fields generalizing first with
  | nil => cases steps; exact safe
  | cons entry rest ih =>
    rcases entry with ⟨ty, child⟩
    cases steps with
    | child good updated later =>
      exact ih _ (placement_update_power ty _ _ _ _ safe
        (normalized_word_alignment_power kind id _ good) updated) later

theorem Equation.PowerAlignmentRule.canonicalFields (owner : Nat) (mode : Mode) (kind : String)
    (id : Nat) (fields : List (Ty × Nat)) :
    (canonicalFields mode kind id fields).PowerAlignmentRule owner := by
  apply Equation.IndexedRule.checked
  intro first last value initial steps finished
  cases initial
  have power := canonicalFields_steps_power mode kind id fields _ _ (by decide) steps
  dsimp only [TrustIr.SourceLayout.canonicalFields] at finished
  cases aligned : alignUp last.cursor last.align with
  | error error => simp [aligned, Bind.bind, Except.bind] at finished
  | ok size =>
    simp only [aligned, Bind.bind, Except.bind] at finished
    apply BoundedAlignment.of_finish _ finished
    intro align actual
    cases actual
    exact ⟨power, (alignUp_aligned _ _ _ aligned).2⟩

theorem Equation.PowerAlignmentRule.declaredFields (owner : Nat) (mode : Mode) (kind : String)
    (id size align clamp : Nat) (transparent : Bool) (fields : List (Ty × Option Nat × Nat)) :
    (declaredFields mode kind id size align clamp transparent fields).PowerAlignmentRule owner := by
  apply Equation.IndexedRule.guarded
  intro graph value run
  have word := (Equation.WordGuarded.declaredFields mode kind id size align clamp transparent fields) graph value run
  refine ⟨word, ?_⟩
  rcases run with ⟨first, last, initial, steps, finished⟩
  have header := declaredFields_initial_facts mode kind id size align clamp transparent fields first initial
  rw [declaredFields_finish_exact mode kind id size align clamp transparent fields last value finished]
  intro actual same
  cases same
  exact ⟨header.1, header.2.1⟩

theorem Equation.PowerAlignmentRule.done (owner : Nat) (result : Result Summary)
    (safe : ∀ value, result = .ok value → BoundedAlignment value) :
    (Equation.done result).PowerAlignmentRule owner := Equation.IndexedRule.done owner result safe

theorem Equation.PowerAlignmentRule.failed (owner : Nat) (error : Error) :
    (Equation.done (.error error)).PowerAlignmentRule owner :=
  Equation.PowerAlignmentRule.done owner _ (by intro value impossible; cases impossible)

theorem Equation.PowerAlignmentRule.scaled (owner : Nat) (mode : Mode) (count child : Nat) :
    (scaled mode count child).PowerAlignmentRule owner := by
  apply Equation.IndexedRule.checked
  intro first last value initial steps finished
  cases steps with
  | child good updated later =>
    cases later
    cases finished
    dsimp only [scaled] at updated
    simp only [Except.bind, Bind.bind] at updated
    split at updated
    · cases updated
    · have computed := (checked_ok _ _ (by assumption)).1
      apply BoundedAlignment.of_finish _ updated
      intro align actual
      have childSafe := good.2 align actual
      exact ⟨childSafe.1, by rw [computed]; simp only [Nat.mul_mod, childSafe.2, Nat.zero_mul, Nat.zero_mod]⟩

theorem Equation.PowerAlignmentRule.unit (owner : Nat) (steps : List (Step Unit)) :
    ({ kind := .unit, initial := .ok (), steps, finish := fun _ => .ok { size := 0, align := some 1 } } : Equation).PowerAlignmentRule owner := by
  apply Equation.IndexedRule.guarded
  intro graph value run
  rcases run with ⟨first, last, initial, steps, finished⟩
  cases finished
  refine ⟨WordBounds.unit, ?_⟩
  intro align actual
  cases actual
  decide

theorem tag_alignment_power (tag : EnumTagRepr) : powerOfTwo (tagBits tag / 8) = true := by
  cases tag <;> decide

private theorem enum_children_alignment (nodes : List Nat) (first last : List Summary)
    (initial : ∀ value, value ∈ first → BoundedAlignment value)
    (steps : StepsInvariantAt (fun _ value => BoundedAlignment value)
      (nodes.map (fun child => .child child fun value state => .ok (value :: state))) first last) :
    ∀ value, value ∈ last → BoundedAlignment value := by
  induction nodes generalizing first with
  | nil => cases steps; exact initial
  | cons node rest ih =>
    cases steps with
    | child good updated later =>
      cases updated
      apply ih _ _ later
      intro value member
      cases member with
      | head => exact good
      | tail _ member => exact initial value member

theorem payload_alignment_power (variants : List Summary)
    (children : ∀ value, value ∈ variants → PowerAlignment value) :
    powerOfTwo (variants.foldl (fun out value => max out (value.align.getD 1)) 1) = true := by
  have walk : ∀ initial, powerOfTwo initial = true →
      powerOfTwo (variants.foldl (fun out value => max out (value.align.getD 1)) initial) = true := by
    induction variants with
    | nil => intro initial safe; exact safe
    | cons first rest ih =>
      intro initial safe
      have child := children first ((trustIrListMemConsSelf _ _))
      have childPower : powerOfTwo (first.align.getD 1) = true := by
        cases actual : first.align with
        | none => decide
        | some align => exact (child align actual).1
      exact ih (fun value member => children value (List.mem_cons_of_mem _ member)) _
        (powerOfTwo_max safe childPower)
  exact walk 1 (by decide)

theorem EnumConstruction.canonical_power_alignment {mode : Mode} {definition : EnumDef} {tag : EnumTagRepr}
    {values : List Int} {uninhabited : List Bool} {variants : List Summary} {output : Summary}
    (constructed : EnumConstruction mode definition tag values uninhabited variants output)
    (canonical : definition.layout = none)
    (children : ∀ value, value ∈ variants → PowerAlignment value) : BoundedAlignment output := by
  rcases constructed.canonical_view canonical with ⟨offset, extent, size, placed, bounded, rounded, finished⟩
  apply BoundedAlignment.of_finish _ finished
  intro align actual
  cases actual
  exact ⟨powerOfTwo_max (tag_alignment_power tag) (payload_alignment_power variants children),
    (alignUp_aligned _ _ _ rounded).2⟩

private theorem alignment_member_append {α : Type} (value : α) (left right : List α) :
    value ∈ left ++ right ↔ value ∈ left ∨ value ∈ right := by
  induction left with
  | nil => simp
  | cons first rest ih => simp [List.cons_append, ih, or_assoc]

private theorem alignment_member_reverse {α : Type} (value : α) (values : List α) :
    value ∈ values.reverse ↔ value ∈ values := by
  induction values with
  | nil => simp
  | cons first rest ih => simp [List.reverse_cons, alignment_member_append, ih, or_comm]

theorem Equation.PowerAlignmentRule.enumeration (owner : Nat) (mode : Mode)
    (definition : EnumDef) (uninhabited : List Bool) (nodes : List Nat) :
    (enumEquation mode definition uninhabited nodes).PowerAlignmentRule owner := by
  cases authored : definition.layout with
  | some descriptor =>
    apply Equation.IndexedRule.guarded
    intro graph value run
    have word := (Equation.WordGuarded.enumeration mode definition uninhabited nodes) graph value run
    have header := run.descriptorEnum_header mode definition uninhabited nodes descriptor authored
    rcases run.descriptorEnum_view mode definition uninhabited nodes descriptor authored with
      ⟨tag, values, state, tagged, numbered, admitted, collected, constructed⟩
    refine ⟨word, ?_⟩
    rw [constructed.descriptor_exact descriptor authored]
    intro align actual
    cases actual
    exact ⟨header.1, header.2.1⟩
  | none =>
    cases ht : canonicalTag definition with
    | none =>
      have selected : enumEquation mode definition uninhabited nodes =
          Equation.done (.error (.incoherent "enum" definition.id.index)) := by
        unfold enumEquation; rw [ht]
      rw [selected]
      exact Equation.PowerAlignmentRule.failed owner _
    | some tag =>
      cases hv : discriminants definition with
      | none =>
        have selected : enumEquation mode definition uninhabited nodes =
            Equation.done (.error (.incoherent "enum" definition.id.index)) := by
          unfold enumEquation; rw [ht, hv]
        rw [selected]
        exact Equation.PowerAlignmentRule.failed owner _
      | some values =>
        unfold enumEquation
        rw [ht, hv]
        dsimp only
        rw [authored]
        apply Equation.IndexedRule.checked
        intro first last value initial steps finished
        cases initial
        have children := enum_children_alignment nodes [] last (by intro value impossible; cases impossible) steps
        have constructed : EnumConstruction mode definition tag values uninhabited last.reverse value := finished
        exact constructed.canonical_power_alignment authored
          (fun value member => (children value ((alignment_member_reverse value last).mp member)).2)

theorem Equation.PowerAlignmentRule.sequence (owner : Nat) (children : List Nat) {next : Equation}
    (safe : next.PowerAlignmentRule owner) : (Equation.sequence children next).PowerAlignmentRule owner :=
  Equation.IndexedRule.sequence children safe

theorem BoundedAlignment.unit : BoundedAlignment { size := 0, align := some 1 } := by
  refine ⟨WordBounds.unit, ?_⟩
  intro align actual
  cases actual
  decide

end TrustIr.SourceLayout
