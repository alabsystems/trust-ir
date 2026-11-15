-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.Eval

namespace TrustIr

/-- Deep initialization of actual runtime carriers. This is separate from
    typing, pointer validity and frame ownership. Poison and unwritten lanes
    have no constructor. Compact arrays are observed by logical lookup, so an
    unused template in a zero-length array imposes no initialization demand.
    New runtime carriers require an explicit admission rule here. -/
inductive Value.Initialized : Value → Prop where
  | int (width : Nat) (value : Int) : Initialized (.int width value)
  | float (value : Float) : Initialized (.float value)
  | bool (value : Bool) : Initialized (.bool value)
  | ptr (address : Nat) (provenance : Option AllocId) : Initialized (.ptr address provenance)
  | nullPtr : Initialized .nullPtr
  | fnDef (signature : FuncTyId) (function : FuncId) : Initialized (.fnDef signature function)
  | aggregate (values : List Value) (children : ∀ value ∈ values, Initialized value) :
      Initialized (.aggregate values)
  | vector (values : List Value) (children : ∀ value ∈ values, Initialized value) :
      Initialized (.vector values)
  | frame (lineage : Nat) (values : List Value) (children : ∀ value ∈ values, Initialized value) :
      Initialized (.frame lineage values)
  | set (values : List Value) (children : ∀ value ∈ values, Initialized value) :
      Initialized (.set values)
  | sequence (values : List Value) (children : ∀ value ∈ values, Initialized value) :
      Initialized (.sequence values)
  | closure (function : FuncId) (values : List Value) (children : ∀ value ∈ values, Initialized value) :
      Initialized (.closure function values)
  | typedClosure (ty : ClosureTyId) (function : FuncId) (values : List Value)
      (children : ∀ value ∈ values, Initialized value) :
      Initialized (.typedClosure ty function values)
  | record (fields : List (String × Value))
      (children : ∀ name value, (name, value) ∈ fields → Initialized value) :
      Initialized (.record fields)
  | array (values : CompactArray.Packed Value)
      (children : ∀ index value, values.get? index = some value → Initialized value) :
      Initialized (.array values)
  | fatPtr (address : Nat) (provenance : Option AllocId) (metadata : Value)
      (child : Initialized metadata) : Initialized (.fatPtr address provenance metadata)

theorem Value.Initialized.not_unwritten {value : Value} (valid : value.Initialized) :
    value.isUninit = false := by cases valid <;> rfl

theorem Value.Initialized.not_poison {value : Value} (valid : value.Initialized) :
    value.isPoison = false := by cases valid <;> rfl

theorem Value.Initialized.aggregate_child {values : List Value}
    (valid : (Value.aggregate values).Initialized) (value : Value) (member : value ∈ values) :
    value.Initialized := by
  cases valid with
  | aggregate _ children => exact children value member

theorem Value.Initialized.array_child {values : CompactArray.Packed Value}
    (valid : (Value.array values).Initialized) (index : Nat) (value : Value)
    (found : values.get? index = some value) : value.Initialized := by
  cases valid with
  | array _ children => exact children index value found

theorem Value.Initialized.record_child {fields : List (String × Value)}
    (valid : (Value.record fields).Initialized) (name : String) (value : Value)
    (member : (name, value) ∈ fields) : value.Initialized := by
  cases valid with
  | record _ children => exact children name value member

namespace SourceValueMembership

/-- A successful actual monadic traversal checked every retained occurrence. -/
theorem forM_checked_member {α ε : Type} (rows : List α) (check : α → Except ε Unit)
    (checked : rows.forM check = .ok ()) (row : α) (member : row ∈ rows) : check row = .ok () := by
  induction rows with
  | nil => cases member
  | cons first rest ih =>
      cases outcome : check first with
      | error error => simp [List.forM_cons, outcome, Except.bind, Bind.bind] at checked
      | ok unit =>
          cases unit
          have tail : rest.forM check = .ok () := by
            simpa [List.forM_cons, outcome, Except.bind, Bind.bind] using checked
          cases member with
          | head => exact outcome
          | tail _ member => exact ih tail member

/-- Never has no accepted runtime carrier at any structural budget. -/
theorem check_never_refuses (ctx : EvalContext) (fuel : Nat) (value : Value) :
    checkClosureValueAt ctx fuel .Never value ≠ .ok () := by
  cases fuel with
  | zero => simp [checkClosureValueAt]
  | succ fuel =>
      cases value <;>
        simp [checkClosureValueAt, Value.isPoison, Value.isUninit, Ty.isInteger]
      all_goals intro impossible; cases impossible

private theorem zip_value_member {α β : Type} (left : List α) (right : List β)
    (a : α) (b : β) (member : (a, b) ∈ left.zip right) : b ∈ right := by
  induction left generalizing right with
  | nil => cases member
  | cons first rest ih =>
      cases right with
      | nil => cases member
      | cons second tail =>
          cases member with
          | head => exact .head _
          | tail _ member => exact .tail _ (ih tail member)

/-- Success at a tuple checks its actual source-ordered lanes. Unwritten
    lanes remain permitted by this transport-level statement. -/
theorem tuple_checked (ctx : EvalContext) (fuel : Nat) (types : List Ty) (values : List Value)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Tuple types) (.aggregate values) = .ok ()) :
    types.length = values.length ∧
      (types.zip values).forM (fun (ty, value) =>
        if value.isUninit then pure () else checkClosureValueAt ctx fuel ty value) = .ok () := by
  change (if types.length != values.length then
    Except.error (SemError.typeError "closure value does not match its declared type")
    else (types.zip values).forM (fun (ty, value) =>
      if value.isUninit then pure () else checkClosureValueAt ctx fuel ty value)) = .ok () at checked
  by_cases same : types.length = values.length
  · exact ⟨same, by simpa [same] using checked⟩
  · have different : (types.length != values.length) = true := by simp [same]
    simp [different] at checked

/-- Deep initialization removes the tuple transport exception, so every
    selected lane passed the actual recursive checker at its declared type. -/
theorem tuple_child (ctx : EvalContext) (fuel : Nat) (types : List Ty) (values : List Value)
    (initialized : (Value.aggregate values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Tuple types) (.aggregate values) = .ok ())
    (ty : Ty) (value : Value) (member : (ty, value) ∈ types.zip values) :
    value.Initialized ∧ checkClosureValueAt ctx fuel ty value = .ok () := by
  have child := initialized.aggregate_child value (zip_value_member types values ty value member)
  have accepted := forM_checked_member _ _ (tuple_checked ctx fuel types values checked).2
    (ty, value) member
  exact ⟨child, by simpa only [child.not_unwritten, Bool.false_eq_true, ite_false] using accepted⟩

/-- The actual array checker resolves the declared element type and checks
    the total compact tree; this does not expand compressed representations. -/
theorem array_checked (ctx : EvalContext) (fuel : Nat) (id : TyId) (count : Nat)
    (values : CompactArray.Packed Value) (element : Ty) (resolved : ctx.types id = some element)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Array id count) (.array values) = .ok ()) :
    count = values.size ∧ values.tree.checkStored (checkClosureValueAt ctx fuel element) = .ok () := by
  change (do
    let ty ← match ctx.types id with
      | some ty => pure ty
      | none => throw (SemError.unsupported .enumDefTable "closure capture element type is absent")
    if count != values.size then
      Except.error (SemError.typeError "closure value does not match its declared type")
    else values.tree.checkStored (checkClosureValueAt ctx fuel ty)) = .ok () at checked
  rw [resolved] at checked
  change (if count != values.size then
    Except.error (SemError.typeError "closure value does not match its declared type")
    else values.tree.checkStored (checkClosureValueAt ctx fuel element)) = .ok () at checked
  by_cases same : count = values.size
  · exact ⟨same, by simpa [same] using checked⟩
  · have different : (count != values.size) = true := by simp [same]
    simp [different] at checked

theorem array_child (ctx : EvalContext) (fuel : Nat) (id : TyId) (count : Nat)
    (values : CompactArray.Packed Value) (element : Ty) (resolved : ctx.types id = some element)
    (initialized : (Value.array values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Array id count) (.array values) = .ok ())
    (index : Nat) (value : Value) (found : values.get? index = some value) :
    value.Initialized ∧ checkClosureValueAt ctx fuel element value = .ok () :=
  ⟨initialized.array_child index value found,
    values.tree.checkStored_get _ index value (array_checked ctx fuel id count values element resolved checked).2 found⟩

theorem tuple_shape (ctx : EvalContext) (fuel : Nat) (types : List Ty) (value : Value)
    (checked : checkClosureValueAt ctx fuel (.Tuple types) value = .ok ()) :
    ∃ values, value = .aggregate values := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      cases value
      case aggregate values => exact ⟨values, rfl⟩
      all_goals simp [checkClosureValueAt, Value.isPoison, Value.isUninit, Ty.isInteger] at checked
      all_goals cases checked

theorem array_shape (ctx : EvalContext) (fuel : Nat) (id : TyId) (count : Nat) (value : Value)
    (checked : checkClosureValueAt ctx fuel (.Array id count) value = .ok ()) :
    ∃ values, value = .array values := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      cases value
      case array values => exact ⟨values, rfl⟩
      all_goals simp [checkClosureValueAt, Value.isPoison, Value.isUninit, Ty.isInteger] at checked
      all_goals cases checked

private theorem zip_type_witness {α β : Type} (types : List α) (values : List β)
    (length : types.length = values.length) (ty : α) (member : ty ∈ types) :
    ∃ value, (ty, value) ∈ types.zip values := by
  induction types generalizing values with
  | nil => cases member
  | cons first rest ih =>
      cases values with
      | nil => cases length
      | cons value tail =>
          have same : rest.length = tail.length := Nat.succ.inj length
          cases member with
          | head => exact ⟨value, (trustIrListMemConsSelf _ _)⟩
          | tail _ member =>
              obtain ⟨found, present⟩ := ih tail same member
              exact ⟨found, List.mem_cons_of_mem _ present⟩

private theorem leaf_element {α : Type} {size : Nat} (leaf : CompactArray.Leaf α size)
    (index : Nat) (inside : index < size) : ∃ value, leaf.get? index = some value := by
  induction leaf generalizing index with
  | nil => omega
  | cons first rest ih =>
      cases index with
      | zero => exact ⟨first, rfl⟩
      | succ index => exact ih index (by omega)

private theorem tree_element {α : Type} {size : Nat} (tree : CompactArray.Tree α size)
    (index : Nat) (inside : index < size) : ∃ value, tree.get? index = some value := by
  induction tree generalizing index with
  | uniform count value => exact ⟨value, by simp [CompactArray.Tree.get?, inside]⟩
  | dense _small values => exact leaf_element values index inside
  | @split size large left right ihLeft ihRight =>
      by_cases side : index < size / 2
      · obtain ⟨value, found⟩ := ihLeft index side
        exact ⟨value, by simpa only [CompactArray.Tree.get?, if_pos side] using found⟩
      · obtain ⟨value, found⟩ := ihRight (index - size / 2) (by omega)
        exact ⟨value, by simpa only [CompactArray.Tree.get?, if_neg side] using found⟩
  | periodic unit positive phase count ih =>
      obtain ⟨value, found⟩ := ih _ (Nat.mod_lt _ positive)
      exact ⟨value, by simpa only [CompactArray.Tree.get?, if_pos inside] using found⟩

/-- Emptiness here means absence of deeply initialized values accepted by the
    actual capture checker at any budget. It is not an assertion about an
    independent typing judgment or about unsupported runtime interfaces. -/
def NoInitializedCapture (ctx : EvalContext) (ty : Ty) : Prop :=
  ∀ fuel value, value.Initialized → checkClosureValueAt ctx fuel ty value ≠ .ok ()

theorem never_empty (ctx : EvalContext) : NoInitializedCapture ctx .Never :=
  fun fuel value _ => check_never_refuses ctx fuel value

theorem tuple_empty_of_field (ctx : EvalContext) (types : List Ty) (ty : Ty)
    (member : ty ∈ types) (empty : NoInitializedCapture ctx ty) :
    NoInitializedCapture ctx (.Tuple types) := by
  intro fuel value initialized checked
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      obtain ⟨values, rfl⟩ := tuple_shape ctx _ types value checked
      obtain ⟨child, present⟩ := zip_type_witness types values
        (tuple_checked ctx fuel types values checked).1 ty member
      have accepted := tuple_child ctx fuel types values initialized checked ty child present
      exact empty fuel child accepted.1 accepted.2

/-- Nonempty arrays have an actual logical element witness even when their
    storage is uniform, split or periodic. No representation is expanded. -/
theorem array_empty_of_element (ctx : EvalContext) (id : TyId) (element : Ty)
    (resolved : ctx.types id = some element) (count : Nat) (positive : 0 < count)
    (empty : NoInitializedCapture ctx element) : NoInitializedCapture ctx (.Array id count) := by
  intro fuel value initialized checked
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      obtain ⟨values, rfl⟩ := array_shape ctx _ id count value checked
      have length := (array_checked ctx fuel id count values element resolved checked).1
      obtain ⟨child, found⟩ := tree_element values.tree 0 (by omega)
      have accepted := array_child ctx fuel id count values element resolved initialized checked 0 child found
      exact empty fuel child accepted.1 accepted.2

theorem struct_checked (ctx : EvalContext) (fuel : Nat) (id : StructId) (definition : StructDef)
    (resolved : ctx.structs id = some definition) (values : List Value)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Struct id) (.aggregate values) = .ok ()) :
    definition.fields.length = values.length ∧
      (definition.fields.zip values).forM (fun (field, value) =>
        if value.isUninit then pure () else checkClosureValueAt ctx fuel field.ty value) = .ok () := by
  change (do
    let row ← match ctx.structs id with
      | some row => pure row
      | none => throw (SemError.unsupported .enumDefTable "closure capture struct definition is absent")
    if row.fields.length != values.length then
      Except.error (SemError.typeError "closure value does not match its declared type")
    else (row.fields.zip values).forM (fun (field, value) =>
      if value.isUninit then pure () else checkClosureValueAt ctx fuel field.ty value)) = .ok () at checked
  rw [resolved] at checked
  change (if definition.fields.length != values.length then
    Except.error (SemError.typeError "closure value does not match its declared type")
    else (definition.fields.zip values).forM (fun (field, value) =>
      if value.isUninit then pure () else checkClosureValueAt ctx fuel field.ty value)) = .ok () at checked
  by_cases same : definition.fields.length = values.length
  · exact ⟨same, by simpa [same] using checked⟩
  · have different : (definition.fields.length != values.length) = true := by simp [same]
    simp [different] at checked

theorem struct_child (ctx : EvalContext) (fuel : Nat) (id : StructId) (definition : StructDef)
    (resolved : ctx.structs id = some definition) (values : List Value)
    (initialized : (Value.aggregate values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Struct id) (.aggregate values) = .ok ())
    (field : FieldDef) (value : Value) (member : (field, value) ∈ definition.fields.zip values) :
    value.Initialized ∧ checkClosureValueAt ctx fuel field.ty value = .ok () := by
  have child := initialized.aggregate_child value (zip_value_member _ _ field value member)
  have accepted := forM_checked_member _ _ (struct_checked ctx fuel id definition resolved values checked).2
    (field, value) member
  exact ⟨child, by simpa only [child.not_unwritten, Bool.false_eq_true, ite_false] using accepted⟩

theorem record_checked (ctx : EvalContext) (fuel : Nat) (id : RecordId) (definition : RecordDef)
    (resolved : ctx.records id = some definition) (fields : List (String × Value))
    (checked : checkClosureValueAt ctx (fuel + 1) (.Record id) (.record fields) = .ok ()) :
    definition.fields.length = fields.length ∧
      (definition.fields.zip fields).forM (fun (declared, (name, value)) =>
        if name != declared.name then
          Except.error (SemError.typeError "closure value does not match its declared type")
        else checkClosureValueAt ctx fuel declared.ty value) = .ok () := by
  change (do
    let row ← match ctx.records id with
      | some row => pure row
      | none => throw (SemError.unsupported .enumDefTable "closure capture record definition is absent")
    if row.fields.length != fields.length then
      Except.error (SemError.typeError "closure value does not match its declared type")
    else (row.fields.zip fields).forM (fun (declared, (name, value)) =>
      if name != declared.name then
        Except.error (SemError.typeError "closure value does not match its declared type")
      else checkClosureValueAt ctx fuel declared.ty value)) = .ok () at checked
  rw [resolved] at checked
  change (if definition.fields.length != fields.length then
    Except.error (SemError.typeError "closure value does not match its declared type")
    else (definition.fields.zip fields).forM (fun (declared, (name, value)) =>
      if name != declared.name then
        Except.error (SemError.typeError "closure value does not match its declared type")
      else checkClosureValueAt ctx fuel declared.ty value)) = .ok () at checked
  by_cases same : definition.fields.length = fields.length
  · exact ⟨same, by simpa [same] using checked⟩
  · have different : (definition.fields.length != fields.length) = true := by simp [same]
    simp [different] at checked

theorem record_child (ctx : EvalContext) (fuel : Nat) (id : RecordId) (definition : RecordDef)
    (resolved : ctx.records id = some definition) (fields : List (String × Value))
    (initialized : (Value.record fields).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Record id) (.record fields) = .ok ())
    (field : FieldDef) (name : String) (value : Value)
    (member : (field, (name, value)) ∈ definition.fields.zip fields) :
    name = field.name ∧ value.Initialized ∧ checkClosureValueAt ctx fuel field.ty value = .ok () := by
  have child := initialized.record_child name value (zip_value_member _ _ field (name, value) member)
  have accepted := forM_checked_member _ _ (record_checked ctx fuel id definition resolved fields checked).2
    (field, (name, value)) member
  by_cases same : name = field.name
  · exact ⟨same, child, by simpa [same] using accepted⟩
  · have different : (name != field.name) = true := by simp [same]
    simp [different] at accepted

theorem struct_shape (ctx : EvalContext) (fuel : Nat) (id : StructId) (value : Value)
    (checked : checkClosureValueAt ctx fuel (.Struct id) value = .ok ()) :
    ∃ values, value = .aggregate values := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      cases value
      case aggregate values => exact ⟨values, rfl⟩
      all_goals simp [checkClosureValueAt, Value.isPoison, Value.isUninit, Ty.isInteger] at checked
      all_goals cases checked

theorem record_shape (ctx : EvalContext) (fuel : Nat) (id : RecordId) (value : Value)
    (checked : checkClosureValueAt ctx fuel (.Record id) value = .ok ()) :
    ∃ fields, value = .record fields := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      cases value
      case record fields => exact ⟨fields, rfl⟩
      all_goals simp [checkClosureValueAt, Value.isPoison, Value.isUninit, Ty.isInteger] at checked
      all_goals cases checked

theorem struct_empty_of_field (ctx : EvalContext) (id : StructId) (definition : StructDef)
    (resolved : ctx.structs id = some definition) (field : FieldDef)
    (member : field ∈ definition.fields) (empty : NoInitializedCapture ctx field.ty) :
    NoInitializedCapture ctx (.Struct id) := by
  intro fuel value initialized checked
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      obtain ⟨values, rfl⟩ := struct_shape ctx _ id value checked
      obtain ⟨child, present⟩ := zip_type_witness definition.fields values
        (struct_checked ctx fuel id definition resolved values checked).1 field member
      have accepted := struct_child ctx fuel id definition resolved values initialized checked field child present
      exact empty fuel child accepted.1 accepted.2

theorem record_empty_of_field (ctx : EvalContext) (id : RecordId) (definition : RecordDef)
    (resolved : ctx.records id = some definition) (field : FieldDef)
    (member : field ∈ definition.fields) (empty : NoInitializedCapture ctx field.ty) :
    NoInitializedCapture ctx (.Record id) := by
  intro fuel value initialized checked
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      obtain ⟨fields, rfl⟩ := record_shape ctx _ id value checked
      obtain ⟨⟨name, child⟩, present⟩ := zip_type_witness definition.fields fields
        (record_checked ctx fuel id definition resolved fields checked).1 field member
      have accepted := record_child ctx fuel id definition resolved fields initialized checked field name child present
      exact empty fuel child accepted.2.1 accepted.2.2

theorem enum_checked (ctx : EvalContext) (fuel : Nat) (id : EnumId) (definition : EnumDef)
    (resolved : ctx.enums id = some definition) (values : List Value)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ tag payload index variant, values = tag :: payload ∧
      (trustIrListGet? definition.variants index) = some variant ∧ variant ∈ definition.variants ∧
      variant.fields.length = payload.length ∧
      (variant.fields.zip payload).forM (fun (ty, value) => checkClosureValueAt ctx fuel ty value) = .ok () := by
  trustIrCompilerProof { rw [checkClosureValueAt.eq_2] at checked } { rw [checkClosureValueAt] at checked }
  simp only [Value.isPoison, Value.isUninit, Bool.false_or, Bool.false_eq_true, ite_false,
    resolved, Except.bind, Except.pure, Bind.bind, Pure.pure] at checked
  split at checked
  · rename_i discs _discsEq
    split at checked
    · rename_i repr _reprEq
      cases values with
      | nil => cases checked
      | cons tag payload =>
          dsimp only at checked
          split at checked
          · cases checked
          · rename_i unit _tagChecked
            cases unit
            cases tag with
            | int width number =>
              dsimp only at checked
              split at checked
              · rename_i index _selected
                split at checked
                · rename_i variant found
                  have member : variant ∈ definition.variants := by
                    trustIrCompilerProof {
                      obtain ⟨inside, same⟩ := List.get?_eq_some.mp found
                      exact List.mem_iff_get.mpr ⟨⟨index, inside⟩, same⟩
                    } {
                      exact CompilerCompat.listGetConstructive_mem found
                    }
                  by_cases same : variant.fields.length = payload.length
                  · exact ⟨.int width number, payload, index, variant, rfl, found, member, same,
                      by simpa [same] using checked⟩
                  · have different : (variant.fields.length != payload.length) = true := by simp [same]
                    simp [different] at checked
                · cases checked
              · cases checked
            | _ => cases checked
    · cases checked
  · cases checked

/-- Success identifies the active variant of the exact resolved definition
    and checks every actual initialized payload lane. No agreement with a
    different layout-selected duplicate is assumed. -/
theorem enum_initialized_payload (ctx : EvalContext) (fuel : Nat) (id : EnumId) (definition : EnumDef)
    (resolved : ctx.enums id = some definition) (values : List Value)
    (initialized : (Value.aggregate values).Initialized)
    (checked : checkClosureValueAt ctx (fuel + 1) (.Enum id) (.aggregate values) = .ok ()) :
    ∃ tag payload index variant, values = tag :: payload ∧
      (trustIrListGet? definition.variants index) = some variant ∧ variant ∈ definition.variants ∧
      variant.fields.length = payload.length ∧
      (∀ ty value, (ty, value) ∈ variant.fields.zip payload →
        value.Initialized ∧ checkClosureValueAt ctx fuel ty value = .ok ()) := by
  obtain ⟨tag, payload, index, variant, shape, selected, member, length, traversal⟩ :=
    enum_checked ctx fuel id definition resolved values checked
  refine ⟨tag, payload, index, variant, shape, selected, member, length, ?_⟩
  intro ty value present
  have childMember : value ∈ values := by
    rw [shape]
    exact List.mem_cons_of_mem tag (zip_value_member _ _ ty value present)
  exact ⟨initialized.aggregate_child value childMember,
    forM_checked_member _ _ traversal (ty, value) present⟩

theorem enum_shape (ctx : EvalContext) (fuel : Nat) (id : EnumId) (value : Value)
    (checked : checkClosureValueAt ctx fuel (.Enum id) value = .ok ()) :
    ∃ values, value = .aggregate values := by
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      cases value
      case aggregate values => exact ⟨values, rfl⟩
      all_goals simp [checkClosureValueAt, Value.isPoison, Value.isUninit, Ty.isInteger] at checked
      all_goals cases checked

/-- If every source variant of the actually resolved enum has an empty
    payload field, no initialized enum value passes the actual checker. -/
theorem enum_empty_of_variants (ctx : EvalContext) (id : EnumId) (definition : EnumDef)
    (resolved : ctx.enums id = some definition)
    (empty : ∀ variant ∈ definition.variants,
      ∃ ty, ty ∈ variant.fields ∧ NoInitializedCapture ctx ty) :
    NoInitializedCapture ctx (.Enum id) := by
  intro fuel value initialized checked
  cases fuel with
  | zero => cases checked
  | succ fuel =>
      obtain ⟨values, rfl⟩ := enum_shape ctx _ id value checked
      obtain ⟨_tag, payload, _index, variant, _shape, _selected, member, length, children⟩ :=
        enum_initialized_payload ctx fuel id definition resolved values initialized checked
      obtain ⟨ty, present, noValue⟩ := empty variant member
      obtain ⟨child, found⟩ := zip_type_witness variant.fields payload length ty present
      have accepted := children ty child found
      exact noValue fuel child accepted.1 accepted.2

namespace Controls

theorem unwritten_never_tuple_accepted (ctx : EvalContext) :
    checkClosureValueAt ctx 2 (.Tuple [.Never]) (.aggregate [.uninit]) = .ok () := rfl

theorem unwritten_never_tuple_not_initialized : ¬ (Value.aggregate [.uninit]).Initialized := by
  intro valid
  have impossible := valid.aggregate_child .uninit ((trustIrListMemConsSelf _ _))
  cases impossible

theorem initialized_never_tuple_refuses (ctx : EvalContext) :
    NoInitializedCapture ctx (.Tuple [.Never]) :=
  tuple_empty_of_field ctx [.Never] .Never ((trustIrListMemConsSelf _ _)) (never_empty ctx)

theorem empty_array_initialized (template : Value) :
    (Value.array (CompactArray.Packed.uniform 0 template)).Initialized := by
  apply Value.Initialized.array
  intro index value found
  simp [CompactArray.Packed.get?, CompactArray.Packed.uniform, CompactArray.Tree.get?] at found
  trustIrCompilerProof { omega } { skip }

theorem empty_array_never_accepted (ctx : EvalContext) (id : TyId)
    (resolved : ctx.types id = some .Never) :
    checkClosureValueAt ctx 1 (.Array id 0)
      (.array (CompactArray.Packed.uniform 0 .uninit)) = .ok () := by
  trustIrCompilerProof { rw [checkClosureValueAt.eq_2] } { rw [checkClosureValueAt] }
  simp [Value.isPoison, Value.isUninit, resolved, Except.bind, Except.pure, Bind.bind, Pure.pure,
    CompactArray.Packed.uniform, CompactArray.Tree.checkStored]

theorem empty_array_is_not_empty (ctx : EvalContext) (id : TyId)
    (resolved : ctx.types id = some .Never) : ¬ NoInitializedCapture ctx (.Array id 0) := by
  intro empty
  exact empty 1 _ (empty_array_initialized .uninit) (empty_array_never_accepted ctx id resolved)

theorem uniform_unwritten_not_initialized (count : Nat) (positive : 0 < count) :
    ¬ (Value.array (CompactArray.Packed.uniform count .uninit)).Initialized := by
  intro valid
  have found : (CompactArray.Packed.uniform count Value.uninit).get? 0 = some .uninit := by
    simp [CompactArray.Packed.get?, CompactArray.Packed.uniform, CompactArray.Tree.get?, positive]
  have impossible := valid.array_child 0 .uninit found
  cases impossible

end Controls

end SourceValueMembership
end TrustIr
