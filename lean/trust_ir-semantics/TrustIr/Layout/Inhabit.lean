-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Index

namespace TrustIr.SourceLayout

/-- Positive equations for Rust's least uninhabitedness solution. A cycle
    alone derives nothing; every duplicate definition must satisfy the rule. -/
inductive Formula where
  | yes
  | no
  | ref (node : Nat)
  | any (children : List Formula)
  | all (children : List Formula)

mutual
  def Formula.holds (facts : NatIndexTree Unit) : Formula → Bool
    | .yes => true
    | .no => false
    | .ref node => (facts.find node).isSome
    | .any children => Formula.someHold facts children
    | .all children => Formula.allHold facts children
  def Formula.someHold (facts : NatIndexTree Unit) : List Formula → Bool
    | [] => false
    | first :: rest => first.holds facts || Formula.someHold facts rest
  def Formula.allHold (facts : NatIndexTree Unit) : List Formula → Bool
    | [] => true
    | first :: rest => first.holds facts && Formula.allHold facts rest
end

private def recordBase (index : Index) : Nat := index.closureBase

mutual
  def inhabitFormula (index : Index) : Ty → Formula
    | .Never => .yes
    | .Tuple fields => .any (inhabitFormulas index fields)
    | .Array element count =>
      if count == 0 || !(index.typeRows[element.index]?).isSome then .no else .ref element.index
    | .Refine base _ =>
      if (index.typeRows[base.index]?).isSome then .ref base.index else .no
    | .Struct id => match index.structPositions.find id.index with
      | some position => .ref (index.structBase + position)
      | none => .no
    | .Enum id => match index.enumPositions.find id.index with
      | some position => .ref (index.enumBase + position)
      | none => .no
    | .Record id => match index.recordPositions.find id.index with
      | some position => .ref (recordBase index + position)
      | none => .no
    | _ => .no
  def inhabitFormulas (index : Index) : List Ty → List Formula
    | [] => []
    | first :: rest => inhabitFormula index first :: inhabitFormulas index rest
end

private def equations (index : Index) : NatIndexTree Formula := Id.run do
  let mut out := NatIndexTree.empty
  for (ty, position) in numbered index.source.types do
    out := out.insert position (match ty with | some ty => inhabitFormula index ty | none => .no)
  for (definition, position) in numbered index.source.structs do
    let definitions := (index.structDefinitions.find definition.id.index).getD []
    let rule := Formula.all (definitions.map (fun row =>
      Formula.any (inhabitFormulas index (row.fields.map (·.ty)))))
    let canonical := (index.structPositions.find definition.id.index).getD position
    out := out.insert (index.structBase + position)
      (if canonical == position then rule else .ref (index.structBase + canonical))
  for (definition, position) in numbered index.source.enums do
    let definitions := (index.enumDefinitions.find definition.id.index).getD []
    let rule := Formula.all (definitions.map (fun row => Formula.all (row.variants.map (fun variant =>
      Formula.any (inhabitFormulas index variant.fields)))))
    let canonical := (index.enumPositions.find definition.id.index).getD position
    out := out.insert (index.enumBase + position)
      (if canonical == position then rule else .ref (index.enumBase + canonical))
  for (definition, position) in numbered index.source.records do
    let definitions := (index.recordDefinitions.find definition.id.index).getD []
    let rule := Formula.all (definitions.map (fun row =>
      Formula.any (inhabitFormulas index (row.fields.map (·.ty)))))
    let canonical := (index.recordPositions.find definition.id.index).getD position
    out := out.insert (recordBase index + position)
      (if canonical == position then rule else .ref (recordBase index + canonical))
  return out

private theorem find_valid (test : Nat → Bool) (rows : List Nat) (key : Nat)
    (found : rows.find? test = some key) : key ∈ rows ∧ test key = true := by
  induction rows with
  | nil => cases found
  | cons first rest ih =>
    by_cases yes : test first = true
    · simp [List.find?, yes] at found
      cases found
      exact ⟨by simp, yes⟩
    · simp [List.find?, yes] at found
      obtain ⟨member, result⟩ := ih found
      exact ⟨List.mem_cons_of_mem first member, result⟩

private def choose (test : Nat → Bool) (rows : List Nat) :
    Option { key : Nat // key ∈ rows ∧ test key = true } :=
  match found : rows.find? test with
  | none => none
  | some key => some ⟨key, find_valid test rows key found⟩

/-- Each newly derived fact removes its actual equation. The solver stops at
    a fixed point, with no arbitrary iteration limit or cycle-as-proof rule. -/
private def close (rules : NatIndexTree Formula) (remaining : List Nat)
    (facts : NatIndexTree Unit) : NatIndexTree Unit :=
  match choose (fun key => (rules.find key).any (·.holds facts)) remaining with
  | none => facts
  | some selected => close rules (remaining.erase selected.val) (facts.insert selected.val ())
termination_by remaining.length
decreasing_by exact erase_length_lt remaining selected.val selected.property.1

def uninhabitedFacts (index : Index) : NatIndexTree Unit :=
  close (equations index) (List.range (recordBase index + index.source.records.length)) .empty

def variantUninhabited (index : Index) (facts : NatIndexTree Unit)
    (fields : List Ty) : Bool := (Formula.any (inhabitFormulas index fields)).holds facts

/-- Finite evidence for an equation fact. Every fact used to enable the rule
    must already have a derivation; a circular reference alone is no evidence.
    This is equation evidence, not yet a theorem about typed runtime values. -/
inductive FactDerivation (rules : NatIndexTree Formula) : Nat → Prop where
  | rule (facts : NatIndexTree Unit) (node : Nat) (formula : Formula)
      (found : rules.find node = some formula)
      (enabled : formula.holds facts = true)
      (premises : ∀ key, facts.find key = some () → FactDerivation rules key) :
      FactDerivation rules node

private theorem close_derivations (rules : NatIndexTree Formula) (remaining : List Nat)
    (facts : NatIndexTree Unit)
    (valid : ∀ key, facts.find key = some () → FactDerivation rules key) :
    ∀ key, (close rules remaining facts).find key = some () → FactDerivation rules key := by
  generalize size : remaining.length = count
  induction count using trustIrNatStrongInduction generalizing remaining facts with
  | ind size ih =>
    rw [close]
    split
    · exact valid
    · rename_i selected _selected_eq
      have enabled := selected.property.2
      cases found : rules.find selected.val with
      | none => simp [found, Option.any] at enabled
      | some formula =>
        have step : FactDerivation rules selected.val :=
          .rule facts selected.val formula found (by simpa [found, Option.any] using enabled) valid
        apply ih (remaining.erase selected.val).length
          (by have shorter := erase_length_lt remaining selected.val selected.property.1; omega)
          (remaining.erase selected.val) (facts.insert selected.val ()) _ rfl
        intro key present
        rw [NatIndexTree.find_insert] at present
        split at present
        · rename_i same
          exact same.symm ▸ step
        · exact valid key present

/-- Every flag returned by the actual terminating solver has finite equation
    evidence. In particular, solver termination never serves as a proof of a
    recursive type's uninhabitedness. -/
theorem uninhabitedFacts_derivation (index : Index) (node : Nat)
    (found : (uninhabitedFacts index).find node = some ()) :
    FactDerivation (equations index) node := by
  apply close_derivations (equations index) _ .empty _ node found
  intro key impossible
  cases impossible

/-- Interpret finite equation evidence in any property preserved by enabled
    rules. The premise quantifies over actual finite fact stores, so no
    fixed-point or semantic correctness assumption is hidden in the solver. -/
theorem FactDerivation.sound {rules : NatIndexTree Formula} {property : Nat → Prop}
    (step : ∀ facts node formula, rules.find node = some formula →
      formula.holds facts = true →
      (∀ key, facts.find key = some () → property key) → property node)
    {node : Nat} (proof : FactDerivation rules node) : property node := by
  induction proof with
  | rule facts node formula found enabled _premises ih =>
      exact step facts node formula found enabled ih

/-- A source interpretation is sound for solver flags once each of the actual
    generated source equations preserves it. Establishing that premise for
    typed values is a separate obligation. -/
theorem uninhabitedFacts_sound (index : Index) (property : Nat → Prop)
    (step : ∀ facts node formula, (equations index).find node = some formula →
      formula.holds facts = true →
      (∀ key, facts.find key = some () → property key) → property node)
    (node : Nat) (found : (uninhabitedFacts index).find node = some ()) :
    property node :=
  (uninhabitedFacts_derivation index node found).sound step

/-- A successful conjunction checks every retained occurrence, including
    duplicate source rows. -/
theorem Formula.allHold_member (facts : NatIndexTree Unit) (children : List Formula)
    (enabled : Formula.allHold facts children = true) (child : Formula)
    (member : child ∈ children) : child.holds facts = true := by
  induction children with
  | nil => cases member
  | cons first rest ih =>
      have parts : first.holds facts = true ∧ Formula.allHold facts rest = true := by
        cases firstValue : first.holds facts
        · simp [Formula.allHold, firstValue] at enabled
        · exact ⟨rfl, by simpa only [Formula.allHold, firstValue, Bool.true_and] using enabled⟩
      cases member with
      | head => exact parts.1
      | tail _ member => exact ih parts.2 member

/-- Conservative duplicate rules cover the source occurrence selected by
    executable layout. This discharges selection/group compatibility; it does
    not assert that the field rule describes initialized runtime membership. -/
theorem groupedRule_execution_selected {α : Type} (rows : List α) (id : α → Nat)
    (rule : α → Formula) (facts : NatIndexTree Unit) (key position : Nat)
    (selected : (positionIndex rows id).find key = some position)
    (enabled : (Formula.all ((((definitionGroups rows id).find key).getD []).map rule)).holds facts = true) :
    ∃ row, (row, position) ∈ numbered rows ∧ (rule row).holds facts = true := by
  obtain ⟨row, member, grouped⟩ := positionIndex_group rows id key position selected
  exact ⟨row, member, Formula.allHold_member facts _ (by simpa only [Formula.holds] using enabled) (rule row)
    (List.mem_map.mpr ⟨row, grouped, rfl⟩)⟩

/-- First-occurrence shape lookup is covered by the same conservative rule,
    even when it selects a different duplicate from execution lookup. -/
theorem groupedRule_shape_selected {α : Type} (rows : List α) (id : α → Nat)
    (rule : α → Formula) (facts : NatIndexTree Unit) (key position : Nat)
    (selected : (firstPositionIndex rows id).find key = some position)
    (enabled : (Formula.all ((((definitionGroups rows id).find key).getD []).map rule)).holds facts = true) :
    ∃ row, (row, position) ∈ numbered rows ∧ (rule row).holds facts = true := by
  obtain ⟨row, member, grouped⟩ := firstPositionIndex_group rows id key position selected
  exact ⟨row, member, Formula.allHold_member facts _ (by simpa only [Formula.holds] using enabled) (rule row)
    (List.mem_map.mpr ⟨row, grouped, rfl⟩)⟩

/-- Provenance of an installed equation, retaining its exact numbered source
    occurrence, duplicate group and canonical-alias decision. These are the
    four forms emitted by the actual construction loops. -/
inductive SourceEquation (index : Index) : Nat → Formula → Prop where
  | typeRow (row : Option Ty) (position : Nat)
      (member : (row, position) ∈ numbered index.source.types) :
      SourceEquation index position
        (match row with | some ty => inhabitFormula index ty | none => .no)
  | structureRow (definition : StructDef) (position : Nat)
      (member : (definition, position) ∈ numbered index.source.structs) :
      SourceEquation index (index.structBase + position)
        (let definitions := (index.structDefinitions.find definition.id.index).getD []
         let rule := Formula.all (definitions.map (fun row =>
           Formula.any (inhabitFormulas index (row.fields.map (·.ty)))))
         let canonical := (index.structPositions.find definition.id.index).getD position
         if canonical == position then rule else .ref (index.structBase + canonical))
  | enumerationRow (definition : EnumDef) (position : Nat)
      (member : (definition, position) ∈ numbered index.source.enums) :
      SourceEquation index (index.enumBase + position)
        (let definitions := (index.enumDefinitions.find definition.id.index).getD []
         let rule := Formula.all (definitions.map (fun row => Formula.all (row.variants.map (fun variant =>
           Formula.any (inhabitFormulas index variant.fields)))))
         let canonical := (index.enumPositions.find definition.id.index).getD position
         if canonical == position then rule else .ref (index.enumBase + canonical))
  | recordRow (definition : RecordDef) (position : Nat)
      (member : (definition, position) ∈ numbered index.source.records) :
      SourceEquation index (index.closureBase + position)
        (let definitions := (index.recordDefinitions.find definition.id.index).getD []
         let rule := Formula.all (definitions.map (fun row =>
           Formula.any (inhabitFormulas index (row.fields.map (·.ty)))))
         let canonical := (index.recordPositions.find definition.id.index).getD position
         if canonical == position then rule else .ref (index.closureBase + canonical))

private def EquationSources (index : Index) (tree : NatIndexTree Formula) : Prop :=
  ∀ node formula, tree.find node = some formula → SourceEquation index node formula

private theorem EquationSources.insert (index : Index) (tree : NatIndexTree Formula)
    (valid : EquationSources index tree) (node : Nat) (formula : Formula)
    (source : SourceEquation index node formula) :
    EquationSources index (tree.insert node formula) := by
  intro key rule found
  rw [NatIndexTree.find_insert] at found
  split at found
  · rename_i same
    cases found
    exact same.symm ▸ source
  · exact valid key rule found

private theorem forIn_equationSources {α : Type} (index : Index) (rows : List α)
    (initial : NatIndexTree Formula)
    (body : α → NatIndexTree Formula → Id (ForInStep (NatIndexTree Formula)))
    (preserved : ∀ row, row ∈ rows → ∀ tree, EquationSources index tree →
      EquationSources index (match body row tree with | .done out | .yield out => out))
    (valid : EquationSources index initial) :
    EquationSources index (Id.run (forIn rows initial body)) := by
  induction rows generalizing initial with
  | nil => rw [List.forIn_nil]; exact valid
  | cons first rest ih =>
      have step := preserved first ((trustIrListMemConsSelf _ _)) initial valid
      rw [List.forIn_cons]
      cases outcome : body first initial with
      | done value =>
          simpa only [Bind.bind, outcome, Pure.pure] using step
      | yield value =>
          rw [outcome] at step
          have later := ih value (fun row member => preserved row (List.mem_cons_of_mem _ member)) step
          simpa only [Bind.bind, outcome] using later

/-- Every equation returned by the actual mutable construction has exact
    source provenance. This checks the loops, rather than assuming that a
    separately described rule system is what the solver executes. -/
theorem equations_source (index : Index) (node : Nat) (formula : Formula)
    (found : (equations index).find node = some formula) :
    SourceEquation index node formula := by
  have valid : EquationSources index (equations index) := by
    unfold equations
    dsimp only
    apply forIn_equationSources index
    · intro row member tree valid
      rcases row with ⟨definition, position⟩
      apply EquationSources.insert index tree valid
      exact SourceEquation.recordRow definition position member
    · apply forIn_equationSources index
      · intro row member tree valid
        rcases row with ⟨definition, position⟩
        apply EquationSources.insert index tree valid
        exact SourceEquation.enumerationRow definition position member
      · apply forIn_equationSources index
        · intro row member tree valid
          rcases row with ⟨definition, position⟩
          apply EquationSources.insert index tree valid
          exact SourceEquation.structureRow definition position member
        · apply forIn_equationSources index
          · intro row member tree valid
            rcases row with ⟨ty, position⟩
            apply EquationSources.insert index tree valid
            cases ty <;> exact SourceEquation.typeRow _ position member
          · intro key rule impossible
            cases impossible
  exact valid node formula found

/-- Interpret actual solver output by proving the four source-rule cases.
    Equation lookup authenticity is discharged by `equations_source`; source
    semantics and initialized-value emptiness remain obligations of `step`. -/
theorem uninhabitedFacts_source_induction (index : Index) (property : Nat → Prop)
    (step : ∀ facts node formula, SourceEquation index node formula →
      formula.holds facts = true →
      (∀ key, facts.find key = some () → property key) → property node)
    (node : Nat) (found : (uninhabitedFacts index).find node = some ()) : property node :=
  uninhabitedFacts_sound index property
    (fun facts key formula present => step facts key formula (equations_source index key formula present))
    node found

/-- Each emitted fact exposes an enabled source rule and finite evidence for
    all facts that enabled it. The source provenance is unconditional; the
    interpretation as emptiness is deliberately not assumed here. -/
theorem uninhabitedFacts_source_witness (index : Index) (node : Nat)
    (found : (uninhabitedFacts index).find node = some ()) :
    ∃ facts formula, SourceEquation index node formula ∧ formula.holds facts = true ∧
      (∀ key, facts.find key = some () → FactDerivation (equations index) key) := by
  cases uninhabitedFacts_derivation index node found with
  | rule facts node formula present enabled premises =>
      exact ⟨facts, formula, equations_source index node formula present, enabled, premises⟩

end TrustIr.SourceLayout
