-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.EnumOrigin
import TrustIr.Layout.Geometry

namespace TrustIr.SourceLayout

theorem zip_fst_exact {α β : Type} (left : List α) (right : List β) (same : left.length = right.length) :
    (left.zip right).map (·.1) = left := by
  induction left generalizing right with
  | nil => cases right <;> first | rfl | cases same
  | cons first rest ih =>
    cases right with
    | nil => cases same
    | cons head tail =>
      have sizes := Nat.succ.inj same
      change first :: (rest.zip tail).map (·.1) = first :: rest
      rw [ih tail sizes]

private theorem canonical_update_types (ty : Ty) (summary : Summary) (alignment : Result Nat)
    (before after : PlacementState)
    (updated : (do
      let align ← alignment
      let offset ← alignUp before.cursor align
      let cursor ← checked (offset + summary.size)
      pure ({ cursor, align := max before.align align, fields := { ty, offset, size := summary.size, align } :: before.fields } : PlacementState)) = .ok after) :
    after.fields.map (·.ty) = ty :: before.fields.map (·.ty) := by
  cases aligned : alignment with
  | error error => simp [aligned,Bind.bind,Except.bind] at updated
  | ok align =>
    simp only [aligned,Bind.bind,Except.bind,Pure.pure,Except.pure] at updated
    cases placed : alignUp before.cursor align with
    | error error => simp [placed] at updated
    | ok offset =>
      simp only [placed] at updated
      cases bounded : checked (offset + summary.size) with
      | error error => simp [bounded] at updated
      | ok cursor => simp only [bounded] at updated; cases updated; rfl

theorem canonicalFields_steps_types (graph : Graph) (mode : Mode) (kind : String) (id : Nat)
    (fields : List (Ty × Nat)) (first last : PlacementState)
    (steps : StepsDerivation graph (canonicalFields mode kind id fields).steps first last) :
    last.fields.map (·.ty) = (fields.map (·.1)).reverse ++ first.fields.map (·.ty) := by
  induction fields generalizing first with
  | nil => cases steps; rfl
  | cons entry rest ih =>
    obtain ⟨ty,child⟩ := entry
    cases steps with
    | child solved updated later =>
      have tail := ih _ later
      rw [canonical_update_types ty _ _ _ _ updated] at tail
      simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using tail

theorem Equation.Executes.canonicalFields_types {graph : Graph} {value : Summary}
    (mode : Mode) (kind : String) (id : Nat) (fields : List (Ty × Nat))
    (run : (canonicalFields mode kind id fields).Executes graph value) :
    value.fields.map (·.ty) = fields.map (·.1) := by
  obtain ⟨first,last,initial,steps,finished⟩ := run
  cases initial
  have ordered := canonicalFields_steps_types graph mode kind id fields _ _ steps
  dsimp only [canonicalFields] at finished
  cases aligned : alignUp last.cursor last.align with
  | error error => simp [aligned,Bind.bind,Except.bind] at finished
  | ok size =>
    simp only [aligned,Bind.bind,Except.bind] at finished
    rw [((finish_ok_iff mode _ value).mp finished).1]
    trustIrCompilerProof { rw [← List.reverse_map] } { rw [List.map_reverse] }
    simpa only [List.map_nil,List.append_nil,List.reverse_reverse] using congrArg List.reverse ordered

private theorem declared_update_types (mode : Mode) (kind : String) (id size align : Nat)
    (ty : Ty) (declared : Option Nat) (summary : Summary) (alignment : Result Nat)
    (before after : PlacementState)
    (updated : (do
      let fieldAlign ← alignment
      let offset ← match declared with
        | some offset => pure offset
        | none => if summary.size == 0 then pure 0 else throw (Error.incoherent kind id)
      let limit ← checked (offset + summary.size)
      if (declared.isSome || mode == Mode.shape || kind != "struct") &&
          (offset % fieldAlign != 0 || fieldAlign > align || limit > size) then
        throw (Error.incoherent kind id)
      pure ({ before with fields := { ty, offset, size := summary.size, align := fieldAlign } :: before.fields } : PlacementState)) = .ok after) :
    after.fields.map (·.ty) = ty :: before.fields.map (·.ty) := by
  cases aligned : alignment with
  | error error => simp [aligned,Bind.bind,Except.bind] at updated
  | ok fieldAlign =>
    cases declared with
    | some offset =>
      simp only [aligned,Bind.bind,Except.bind,Pure.pure,Except.pure] at updated
      cases bounded : checked (offset + summary.size) with
      | error error => simp [bounded] at updated
      | ok limit =>
        simp only [bounded] at updated
        split at updated
        · cases updated
        · cases updated; rfl
    | none =>
      by_cases zero : summary.size = 0
      · simp only [aligned,zero,beq_self_eq_true,ite_true,Bind.bind,Except.bind,Pure.pure,Except.pure] at updated
        cases bounded : checked (0 + 0) with
        | error error => simp [bounded] at updated
        | ok limit =>
          simp only [bounded] at updated
          split at updated
          · cases updated
          · cases updated; rfl
      · have nonzero : (summary.size == 0) = false := by simp [zero]
        simp [aligned,nonzero,Bind.bind,Except.bind,MonadExceptOf.throw] at updated

theorem declaredFields_steps_types (graph : Graph) (mode : Mode) (kind : String)
    (id size align clamp : Nat) (transparent : Bool) (fields : List (Ty × Option Nat × Nat))
    (first last : PlacementState)
    (steps : StepsDerivation graph (declaredFields mode kind id size align clamp transparent fields).steps first last) :
    last.fields.map (·.ty) = (fields.map (·.1)).reverse ++ first.fields.map (·.ty) := by
  induction fields generalizing first with
  | nil => cases steps; rfl
  | cons entry rest ih =>
    obtain ⟨ty,declared,child⟩ := entry
    cases steps with
    | child solved updated later =>
      have tail := ih _ later
      rw [declared_update_types mode kind id size align ty declared _ _ _ _ updated] at tail
      simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using tail

theorem Equation.Executes.declaredFields_types {graph : Graph} {value : Summary}
    (mode : Mode) (kind : String) (id size align clamp : Nat) (transparent : Bool)
    (fields : List (Ty × Option Nat × Nat))
    (run : (declaredFields mode kind id size align clamp transparent fields).Executes graph value) :
    value.fields.map (·.ty) = fields.map (·.1) := by
  obtain ⟨first,last,initial,steps,finished⟩ := run
  dsimp only [declaredFields] at initial
  split at initial
  · cases initial
  · cases initial
    have ordered := declaredFields_steps_types graph mode kind id size align clamp transparent fields _ _ steps
    rw [(declaredFields_finish_fields mode kind id size align clamp transparent fields _ _ finished).2.1]
    trustIrCompilerProof { rw [← List.reverse_map] } { rw [List.map_reverse] }
    simpa only [List.map_nil,List.append_nil,List.reverse_reverse] using congrArg List.reverse ordered

/-- Every original struct slot retains the declaration's logical field type
    order, independently of physical offsets and child layout values. -/
def StructSourceAt (index : Index) (node : Nat) (value : Summary) : Prop :=
  ∀ mode position definition, position < index.structCount →
    trustIrListGet? index.source.structs position = some definition →
    node = index.node mode (index.structBase + position) →
      value.fields.map (·.ty) = definition.fields.map (·.ty)

abbrev Graph.StructOriginInvariant (index : Index) (graph : Graph) := graph.IndexedInvariant (StructSourceAt index)

theorem StructSourceAt.above (index : Index) (node : Nat) (outside : 2 * index.count ≤ node)
    (value : Summary) : StructSourceAt index node value := by
  intro mode position definition bound row same
  have slot : index.structBase + position < index.count := by
    unfold Index.count Index.closureBase Index.enumBase
    omega
  have inside : index.node mode (index.structBase + position) < 2 * index.count := by
    cases mode <;> simp only [Index.node,show (Mode.shape == Mode.shape) = true from rfl,
      show (Mode.execution == Mode.shape) = false from rfl,ite_true,Bool.false_eq_true,ite_false,Nat.zero_add] <;> omega
  rw [← same] at inside
  omega

theorem StructSourceAt.other_slot (index : Index) (mode : Mode) (slot : Nat)
    (inside : slot < index.count) (outside : slot < index.structBase ∨ index.enumBase ≤ slot)
    (value : Summary) : StructSourceAt index (index.node mode slot) value := by
  intro otherMode position definition bound row same
  have target : index.structBase + position < index.count := by
    unfold Index.count Index.closureBase Index.enumBase
    omega
  have equal := (index.node_injective mode otherMode slot _ inside target same).2
  unfold Index.enumBase at outside
  rcases outside with before | after <;> omega

theorem Equation.IndexedRule.struct_types (index : Index) (mode : Mode) (definition : StructDef)
    (position : Nat) (bound : position < index.structCount) (row : trustIrListGet? index.source.structs position = some definition)
    (equation : Equation)
    (typed : ∀ graph value, equation.Executes graph value → value.fields.map (·.ty) = definition.fields.map (·.ty)) :
    equation.IndexedRule (StructSourceAt index) (index.node mode (index.structBase + position)) := by
  apply Equation.IndexedRule.guarded
  intro graph value run otherMode otherPosition otherDefinition otherBound otherRow same
  have left : index.structBase + position < index.count := by unfold Index.count Index.closureBase Index.enumBase; omega
  have right : index.structBase + otherPosition < index.count := by unfold Index.count Index.closureBase Index.enumBase; omega
  have equal := (index.node_injective mode otherMode _ _ left right same).2
  have positions : position = otherPosition := by omega
  subst otherPosition
  have definitions := Option.some.inj (row.symm.trans otherRow)
  subst otherDefinition
  exact typed graph value run

theorem Index.struct_selected_source (source : Environment) (mode : Mode) (id : StructId) (position : Nat)
    (selected : (if mode == .shape then (Index.ofEnvironment source).structShapePositions
      else (Index.ofEnvironment source).structPositions).find id.index = some position) :
    ∃ definition, trustIrListGet? source.structs position = some definition ∧ position < source.structs.length ∧ definition.id = id := by
  cases mode with
  | shape =>
    change (firstPositionIndex source.structs (·.id.index)).find id.index = some position at selected
    obtain ⟨definition, member, identity⟩ := firstPositionIndex_witness source.structs (·.id.index) id.index position selected
    exact ⟨definition, numbered_get _ _ _ member, numbered_position_bound _ _ _ member, congrArg StructId.mk identity⟩
  | execution =>
    change (positionIndex source.structs (·.id.index)).find id.index = some position at selected
    obtain ⟨definition, member, identity⟩ := positionIndex_witness source.structs (·.id.index) id.index position selected
    exact ⟨definition, numbered_get _ _ _ member, numbered_position_bound _ _ _ member, congrArg StructId.mk identity⟩


end TrustIr.SourceLayout
