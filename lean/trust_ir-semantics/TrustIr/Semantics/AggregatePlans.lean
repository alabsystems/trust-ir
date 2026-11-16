-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Layout.Service
import TrustIr.Semantics.Memory
import TrustIr.State.ByteImageTraversal

namespace TrustIr.AggregateMemory
open SourceLayout

/-- A finite source-derived image tree. Array counts do not expand the plan.
    Low-level image operations presuppose a plan returned by the authentic
    source Service; constructing a Plan manually grants no module admission. -/
inductive Plan where
  | leaf (ty : Ty) (layout : MemoryTypeLayout)
  | fields (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan))
  | array (ty : Ty) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
  | enumeration (ty : Ty) (layout : MemoryTypeLayout) (info : Enumeration)
      (variants : List (Option (List (Nat × Plan))))
  | fnItem (target : FuncId) (layout : MemoryTypeLayout)

def Plan.ty : Plan → Ty
  | .leaf ty _ | .fields ty _ _ | .array ty _ _ _ | .enumeration ty _ _ _ => ty
  | .fnItem target _ => .FnItem target

def Plan.layout : Plan → MemoryTypeLayout
  | .leaf _ layout | .fields _ layout _ | .array _ layout _ _
  | .enumeration _ layout _ _ | .fnItem _ layout => layout

/-- The exact field types supplied by the actual tuple/struct compiler branch. -/
def Plan.fieldInputTypes (ty : Ty) (value : Summary) : List Ty :=
  match ty with
  | .Tuple types => types
  | _ => value.fields.map (·.ty)

/-- Exact logical order, types and offsets of the actual compiled field list. -/
def FieldBindings (types : List Ty) (offsets : List Nat) (fields : List (Nat × Plan)) : Prop :=
  fields.map (fun field => field.2.ty) = types ∧ fields.map (·.1) = offsets

/-- Actual variant compilation preserves all rows and each live row's field inputs. -/
inductive VariantBindings : List (List Ty) → List (List Nat) → List Bool →
    List (Option (List (Nat × Plan))) → Prop where
  | nil : VariantBindings [] [] [] []
  | omitted {types offsets dead variants} (firstTypes : List Ty) (firstOffsets : List Nat)
      (rest : VariantBindings types offsets dead variants) :
      VariantBindings (firstTypes :: types) (firstOffsets :: offsets) (true :: dead) (none :: variants)
  | live {types offsets dead variants firstTypes firstOffsets fields}
      (first : FieldBindings firstTypes firstOffsets fields)
      (rest : VariantBindings types offsets dead variants) :
      VariantBindings (firstTypes :: types) (firstOffsets :: offsets) (false :: dead) (some fields :: variants)

/-- Every actual child image has the byte extent claimed by its source field. -/
def FieldExtents (metadata : List Field) (fields : List (Nat × Plan)) : Prop :=
  fields.map (fun field => field.2.layout.size) = metadata.map (·.size)

/-- Only retained live rows require child extent agreement; dead rows stay omitted. -/
def VariantExtents (metadata : List (List Field)) (variants : List (Option (List (Nat × Plan)))) : Prop :=
  ∀ position fields, (trustIrListGet? variants position) = some (some fields) →
    ∃ expected, (trustIrListGet? metadata position) = some expected ∧ FieldExtents expected fields

theorem VariantExtents.nil : VariantExtents [] [] := by
  intro position fields found
  cases position <;> cases found

theorem VariantExtents.omitted (first : List Field) {metadata : List (List Field)}
    {variants : List (Option (List (Nat × Plan)))} (later : VariantExtents metadata variants) :
    VariantExtents (first :: metadata) (none :: variants) := by
  intro position fields found
  cases position with
  | zero => cases found
  | succ position => exact later position fields found

theorem VariantExtents.live {first : List Field} {fields : List (Nat × Plan)}
    {metadata : List (List Field)} {variants : List (Option (List (Nat × Plan)))}
    (extent : FieldExtents first fields) (later : VariantExtents metadata variants) :
    VariantExtents (first :: metadata) (some fields :: variants) := by
  intro position actual found
  cases position with
  | zero =>
    simp only [trustIrListGetConsZero,Option.some.injEq] at found
    cases found
    exact ⟨first,rfl,extent⟩
  | succ position => exact later position actual found

/-- Exactly the source types dispatched to the compiler's leaf branch. -/
def Plan.LeafType : Ty → Prop
  | .Array _ _ | .Struct _ | .Tuple _ | .Enum _ | .FnItem _ => False
  | _ => True

/-- Exactly the source types dispatched to the compiler's field-list branch. -/
def Plan.FieldsType : Ty → Prop
  | .Struct _ | .Tuple _ => True
  | _ => False

theorem Plan.LeafType.not_fields {ty : Ty} (leaf : Plan.LeafType ty)
    (fields : Plan.FieldsType ty) : False := by
  cases ty <;> cases leaf <;> cases fields

/-- Exact source-kind dispatch, including the retained type and array count. -/
def Plan.SourceShape (ty : Ty) (plan : Plan) : Prop :=
  match ty with
  | .Array id count => ∃ layout element, plan = .array (.Array id count) layout count element
  | .Struct id => ∃ layout fields, plan = .fields (.Struct id) layout fields
  | .Tuple types => ∃ layout fields, plan = .fields (.Tuple types) layout fields
  | .Enum id => ∃ layout info variants, plan = .enumeration (.Enum id) layout info variants
  | .FnItem target => ∃ layout, plan = .fnItem target layout
  | _ => ∃ layout, plan = .leaf ty layout

/- The plan retains the actual typed summary used for enum metadata.
    Non-enum constructors cannot stand in for a nominal enum. Field layout
    authenticity against original source types remains a separate obligation. -/
mutual
  inductive Plan.Origin (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) : Ty → Plan → Prop where
    | leaf (ty : Ty) (layout : MemoryTypeLayout) (kind : Plan.LeafType ty)
        (value : Summary) (summary : valid ty value)
        (extent : layout.size = value.size ∧ value.align = some layout.alignment) :
        Plan.Origin resolves valid ty (.leaf ty layout)
    | fields (ty : Ty) (layout : MemoryTypeLayout) (fields : List (Nat × Plan))
        (kind : Plan.FieldsType ty)
        (children : ∀ field ∈ fields, Plan.Origin resolves valid field.2.ty field.2)
        (value : Summary) (summary : valid ty value)
        (extent : layout.size = value.size ∧ value.align = some layout.alignment)
        (bindings : FieldBindings (Plan.fieldInputTypes ty value) (value.fields.map (·.offset)) fields)
        (metadata : FieldBindings (value.fields.map (·.ty)) (value.fields.map (·.offset)) fields)
        (sizes : FieldExtents value.fields fields) :
        Plan.Origin resolves valid ty (.fields ty layout fields)
    | array (id : TyId) (layout : MemoryTypeLayout) (count : Nat) (element : Plan)
        (child : Plan.Origin resolves valid element.ty element)
        (binding : resolves id element.ty)
        (value : Summary) (summary : valid (.Array id count) value)
        (extent : layout.size = value.size ∧ value.align = some layout.alignment) :
        Plan.Origin resolves valid (.Array id count) (.array (.Array id count) layout count element)
    | enumeration (id : EnumId) (layout : MemoryTypeLayout) (info : Enumeration)
        (variants : List (Option (List (Nat × Plan)))) (value : Summary)
        (summary : valid (.Enum id) value) (present : value.enumeration = some info)
        (extent : layout.size = value.size ∧ value.align = some layout.alignment)
        (children : VariantOrigins resolves valid info.uninhabited variants)
        (bindings : VariantBindings (info.variants.map (fun fields => fields.map (·.ty)))
          (info.variants.map (fun fields => fields.map (·.offset))) info.uninhabited variants)
        (sizes : VariantExtents info.variants variants) :
        Plan.Origin resolves valid (.Enum id) (.enumeration (.Enum id) layout info variants)
    | fnItem (target : FuncId) (layout : MemoryTypeLayout)
        (value : Summary) (summary : valid (.FnItem target) value)
        (extent : layout.size = value.size ∧ value.align = some layout.alignment) :
        Plan.Origin resolves valid (.FnItem target) (.fnItem target layout)
  inductive VariantOrigins (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) :
      List Bool → List (Option (List (Nat × Plan))) → Prop where
    | nil : VariantOrigins resolves valid [] []
    | omitted {dead variants} (rest : VariantOrigins resolves valid dead variants) :
        VariantOrigins resolves valid (true :: dead) (none :: variants)
    | live {dead variants fields}
        (children : ∀ field ∈ fields, Plan.Origin resolves valid field.2.ty field.2)
        (rest : VariantOrigins resolves valid dead variants) :
        VariantOrigins resolves valid (false :: dead) (some fields :: variants)
end

theorem Plan.Origin.type {resolves : TyId → Ty → Prop} {valid : Ty → Summary → Prop} {ty : Ty} {plan : Plan}
    (origin : Plan.Origin resolves valid ty plan) : plan.ty = ty := by cases origin <;> rfl

theorem Plan.Origin.own {resolves : TyId → Ty → Prop} {valid : Ty → Summary → Prop} {ty : Ty} {plan : Plan}
    (origin : Plan.Origin resolves valid ty plan) : Plan.Origin resolves valid plan.ty plan := by
  rw [origin.type]; exact origin

/-- Every actual compiler-origin certificate uses exactly its source type's
plan constructor. The predicate covers every source type, not just arrays. -/
theorem Plan.Origin.source_shape {resolves : TyId → Ty → Prop}
    {valid : Ty → Summary → Prop} {ty : Ty} {plan : Plan}
    (origin : Plan.Origin resolves valid ty plan) : Plan.SourceShape ty plan := by
  cases origin with
  | leaf ty layout kind value summary extent =>
    cases ty <;> cases kind <;> exact ⟨layout,rfl⟩
  | fields ty layout fields kind children value summary extent bindings metadata sizes =>
    cases ty <;> cases kind <;> exact ⟨layout,fields,rfl⟩
  | array id layout count element child binding value summary extent => exact ⟨layout,element,rfl⟩
  | enumeration id layout info variants value summary present extent children bindings sizes =>
    exact ⟨layout,info,variants,rfl⟩
  | fnItem target layout value summary extent => exact ⟨layout,rfl⟩

/-- A nominal item plan retains its exact queried type and source summary;
an ordinary scalar leaf cannot stand in for the dedicated item constructor. -/
theorem Plan.Origin.fnItem_view {resolves : TyId → Ty → Prop}
    {valid : Ty → Summary → Prop} {target : FuncId} {plan : Plan}
    (origin : Plan.Origin resolves valid (.FnItem target) plan) :
    ∃ layout value, plan = .fnItem target layout ∧ valid (.FnItem target) value ∧
      layout.size = value.size ∧ value.align = some layout.alignment := by
  cases origin with
  | leaf ty layout kind value summary extent => exact False.elim kind
  | fields ty layout fields kind children value summary extent bindings metadata sizes => exact False.elim kind
  | fnItem target layout value summary extent => exact ⟨layout,value,rfl,summary,extent⟩

/-- An array origin retains the actual source array constructor and its count. -/
theorem Plan.Origin.array_type {resolves : TyId → Ty → Prop} {valid : Ty → Summary → Prop} {ty : Ty}
    {layout : MemoryTypeLayout} {count : Nat} {element : Plan}
    (origin : Plan.Origin resolves valid ty (.array ty layout count element)) :
    ∃ id : TyId, ty = .Array id count := by
  cases origin
  exact ⟨_,rfl⟩

/-- An array plan's request type, retained type, logical count, child origin
and typed layout all come from the same actual compilation certificate. -/
theorem Plan.Origin.array_view {resolves : TyId → Ty → Prop} {valid : Ty → Summary → Prop} {sourceTy planTy : Ty}
    {layout : MemoryTypeLayout} {count : Nat} {element : Plan}
    (origin : Plan.Origin resolves valid sourceTy (.array planTy layout count element)) :
    ∃ id : TyId, sourceTy = .Array id count ∧ planTy = .Array id count ∧
      Plan.Origin resolves valid element.ty element ∧
      ∃ value, valid sourceTy value ∧ layout.size = value.size ∧
        value.align = some layout.alignment := by
  cases origin
  exact ⟨_,rfl,rfl,by assumption,_,by assumption,(by assumption : _ ∧ _).1,
    (by assumption : _ ∧ _).2⟩

/-- The same array origin retains resolution of its source type-row ID. -/
theorem Plan.Origin.array_binding_view {resolves : TyId → Ty → Prop}
    {valid : Ty → Summary → Prop} {sourceTy planTy : Ty}
    {layout : MemoryTypeLayout} {count : Nat} {element : Plan}
    (origin : Plan.Origin resolves valid sourceTy (.array planTy layout count element)) :
    ∃ id : TyId, sourceTy = .Array id count ∧ planTy = .Array id count ∧
      resolves id element.ty ∧ Plan.Origin resolves valid element.ty element ∧
      ∃ value, valid sourceTy value ∧ layout.size = value.size ∧
        value.align = some layout.alignment := by
  cases origin
  exact ⟨_,rfl,rfl,by assumption,by assumption,_,by assumption,
    (by assumption : _ ∧ _).1,(by assumption : _ ∧ _).2⟩

/-- Plan compilation has only static source/layout refusals. Runtime errors
and unwind worlds cannot inhabit either compiler cache. -/
private inductive CompilerLayoutFeature where
  | layout

private inductive CompilerError where
  | typeError (message : String)
  | unsupported (feature : CompilerLayoutFeature) (message : String)

private def CompilerError.toSemError : CompilerError → SemError
  | .typeError message => .typeError message
  | .unsupported .layout message => .unsupported .layout message

private def semanticResult {α : Type} : Except CompilerError α → Except SemError α
  | .ok value => .ok value
  | .error failure => .error failure.toSemError

private theorem semanticResult_ok {α : Type} (result : Except CompilerError α) (value : α)
    (run : semanticResult result = .ok value) : result = .ok value := by
  cases result with
  | error failure => cases run
  | ok actual => cases run; rfl

private def layoutError (error : SourceLayout.Error) : CompilerError :=
  match error with
  | .unsupported _ => .unsupported .layout s!"memory: {repr error}"
  | _ => .typeError s!"memory layout: {repr error}"

private abbrev PlanCache := NatIndexTree (List (Ty × Except CompilerError Plan))
private abbrev SummaryCache := NatIndexTree (List (Ty × Except CompilerError Summary))

private def SummaryCache.findType (cache : SummaryCache) (ty : Ty) : Option (Except CompilerError Summary) :=
  ((cache.find (typeBucket ty)).getD []).find? (fun row => closureTyEq row.1 ty) |>.map (·.2)

private def SummaryCache.insertType (cache : SummaryCache) (ty : Ty)
    (result : Except CompilerError Summary) : SummaryCache :=
  let bucket := typeBucket ty
  cache.insert bucket ((ty, result) :: (cache.find bucket).getD [])

private def PlanCache.findType (cache : PlanCache) (ty : Ty) : Option (Except CompilerError Plan) :=
  ((cache.find (typeBucket ty)).getD []).find? (fun row => closureTyEq row.1 ty) |>.map (·.2)

private def PlanCache.insertType (cache : PlanCache) (ty : Ty)
    (result : Except CompilerError Plan) : PlanCache :=
  let bucket := typeBucket ty
  cache.insert bucket ((ty, result) :: (cache.find bucket).getD [])

private structure Compiler where
  source : Session
  cache : PlanCache := .empty
  layouts : SummaryCache := .empty

private abbrev Compile := ExceptT CompilerError (StateM Compiler)

private def summary (ty : Ty) : Compile Summary := do
  let state ← get
  if let some result := state.layouts.findType ty then
    match result with | .ok value => return value | .error error => throw error
  match state.source.query .execution ty with
  | .error error =>
    let error := layoutError error
    set { state with layouts := state.layouts.insertType ty (.error error) }
    throw error
  | .ok (value, next) =>
    set { state with source := next, layouts := state.layouts.insertType ty (.ok value) }
    pure value

/-- Exact cache and source-query transitions for staged kernel proofs. -/
theorem summary_eq (ty : Ty) :
    summary ty = (do
      let state ← get
      if let some result := state.layouts.findType ty then
        match result with | .ok value => return value | .error error => throw error
      match state.source.query .execution ty with
      | .error error =>
        let error := layoutError error
        set { state with layouts := state.layouts.insertType ty (.error error) }
        throw error
      | .ok (value, next) =>
        set { state with source := next, layouts := state.layouts.insertType ty (.ok value) }
        pure value) := rfl

/-- A nominal edge consumes its actual finite source position, never fuel. -/
private def descend (available : NatIndexTree Unit) (key : Nat) :
    Except CompilerError { rest : NatIndexTree Unit // Available.size rest < Available.size available } :=
  match present : available.find key with
  | none => .error (.typeError "memory layout: by-value source cycle")
  | some _ => .ok ⟨Available.erase available key, Available.erase_size_lt available key
      (by rw [present]; rfl)⟩

private def fromExcept {α : Type} (result : Except CompilerError α) : Compile α :=
  match result with | .ok value => pure value | .error error => throw error

mutual
  private def compile (available : NatIndexTree Unit) (ty : Ty) : Compile Plan := do
    let initial ← get
    if let some result := initial.cache.findType ty then return ← fromExcept result
    let value ← summary ty
    let alignment ← match value.align with
      | some alignment => pure alignment
      | none => throw (.unsupported .layout "memory: type has no byte alignment")
    let layout : MemoryTypeLayout := { size := value.size, alignment }
    let index := initial.source.index
    let plan ← match ty with
      -- `summary` above has already resolved the one actual function header
      -- and its signature. A pointer-address table is not a substitute.
      | .FnItem target => pure (.fnItem target layout)
      | .Array id count => do
        let smaller ← fromExcept (descend available id.index)
        let element ← match ((trustIrArrayGet? index.typeRows id.index)).join with
          | some element => pure element
          | none => throw (.typeError "memory: array element type is missing")
        pure (.array ty layout count (← compile smaller.val element))
      | .Struct id => do
        let position ← match index.structPositions.find id.index with
          | some position => pure position
          | none => throw (.typeError "memory: struct definition is missing")
        let smaller ← fromExcept (descend available (index.structBase + position))
        let fields ← compileFields smaller.val (value.fields.map (·.ty)) value.fields
        pure (.fields ty layout fields)
      | .Tuple types => do
        let fields ← compileFields available types value.fields
        pure (.fields ty layout fields)
      | .Enum id => do
        let position ← match index.enumPositions.find id.index with
          | some position => pure position
          | none => throw (.typeError "memory: enum definition is missing")
        let smaller ← fromExcept (descend available (index.enumBase + position))
        let info ← match value.enumeration with
          | some info => pure info
          | none => throw (.typeError "memory: enum layout has no variants")
        let variants ← compileVariants smaller.val
          (info.variants.map (fun fields => fields.map (·.ty)))
          info.variants info.uninhabited
        pure (.enumeration ty layout info variants)
      | _ => pure (.leaf ty layout)
    modify fun state => { state with cache := state.cache.insertType ty (.ok plan) }
    pure plan
  termination_by (Available.size available, sizeOf ty)
  private def compileFields (available : NatIndexTree Unit) (types : List Ty)
      (metadata : List Field) : Compile (List (Nat × Plan)) := do
    match types, metadata with
    | [], [] => pure []
    | ty :: rest, field :: later =>
      if closureTyEq ty field.ty = true then
        let first ← compile available ty
        if first.layout.size = field.size then
          let following ← compileFields available rest later
          pure ((field.offset, first) :: following)
        else throw (.typeError "memory: child byte extent disagrees with source field")
      else throw (.typeError "memory: child type disagrees with source field")
    | _, _ => throw (.typeError "memory: field/metadata census mismatch")
  termination_by (Available.size available, sizeOf types)
  /-- Layout validates source fields except inactive SingleInhabited rows,
      whose structural impossibility and empty physical offsets are checked
      first. An uninhabited variant cannot require an image codec
      for its descriptor-only Never field (or another impossible payload). -/
  private def compileVariants (available : NatIndexTree Unit) (types : List (List Ty))
      (offsets : List (List Field)) (uninhabited : List Bool) :
      Compile (List (Option (List (Nat × Plan)))) := do
    match types, offsets, uninhabited with
    | [], [], [] => pure []
    | first :: rest, offsets :: later, impossible :: remaining =>
      let fields ← if impossible then pure none
        else do pure (some (← compileFields available first offsets))
      let variants ← compileVariants available rest later remaining
      pure (fields :: variants)
    | _, _, _ => throw (.typeError "memory: variant/offset/inhabitedness census mismatch")
  termination_by (Available.size available, sizeOf types)
end

private def CacheErrors {α : Type} (error : CompilerError → Prop)
    (cache : NatIndexTree (List (Ty × Except CompilerError α))) : Prop :=
  ∀ key rows, cache.find key = some rows → ∀ row ∈ rows, ByteImage.BlockResult (fun _ => True) error row.2

private theorem cache_empty_errors {α : Type} (error : CompilerError → Prop) :
    CacheErrors error (NatIndexTree.empty : NatIndexTree (List (Ty × Except CompilerError α))) := by
  intro key rows found
  cases found

private theorem find_row_mem {α : Type} (test : α → Bool) (rows : List α) (row : α)
    (found : rows.find? test = some row) : row ∈ rows := by
  induction rows with
  | nil => cases found
  | cons first rest ih =>
    rw [List.find?_cons] at found
    cases selected : test first <;> simp only [selected] at found
    · exact List.mem_cons_of_mem _ (ih found)
    · cases found; exact (trustIrListMemConsSelf _ _)

private theorem cache_rows_errors {α : Type} (error : CompilerError → Prop)
    (cache : NatIndexTree (List (Ty × Except CompilerError α))) (safe : CacheErrors error cache) (key : Nat) :
    ∀ row ∈ (cache.find key).getD [], ByteImage.BlockResult (fun _ => True) error row.2 := by
  cases found : cache.find key with
  | none => intro row member; cases member
  | some rows => exact safe key rows found

private theorem cache_find_errors {α : Type} (error : CompilerError → Prop)
    (cache : NatIndexTree (List (Ty × Except CompilerError α))) (safe : CacheErrors error cache)
    (ty : Ty) (result : Except CompilerError α)
    (found : (((cache.find (typeBucket ty)).getD []).find? (fun row => closureTyEq row.1 ty)).map (·.2) = some result) :
    ByteImage.BlockResult (fun _ => True) error result := by
  cases selected : ((cache.find (typeBucket ty)).getD []).find? (fun row => closureTyEq row.1 ty) with
  | none => simp [selected] at found
  | some row =>
    simp only [selected,Option.map,Option.some.injEq] at found
    subst result
    exact cache_rows_errors error cache safe _ row (find_row_mem _ _ row selected)

private theorem cache_insert_errors {α : Type} (error : CompilerError → Prop)
    (cache : NatIndexTree (List (Ty × Except CompilerError α))) (safe : CacheErrors error cache)
    (ty : Ty) (result : Except CompilerError α) (held : ByteImage.BlockResult (fun _ => True) error result) :
    CacheErrors error (cache.insert (typeBucket ty) ((ty,result) :: (cache.find (typeBucket ty)).getD [])) := by
  intro key rows found row member
  rw [NatIndexTree.find_insert] at found
  split at found
  · cases found
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact held
    · exact cache_rows_errors error cache safe _ row member
  · exact safe key rows found row member

private def CompilerErrors (error : CompilerError → Prop) (state : Compiler) : Prop :=
  CacheErrors error state.cache ∧ CacheErrors error state.layouts

private def CompileInvariant {α : Type} (error : CompilerError → Prop) (post : α → Prop) (action : Compile α) : Prop :=
  ∀ state, CompilerErrors error state →
    ByteImage.BlockResult post error (action.run state).1 ∧ CompilerErrors error (action.run state).2

private theorem CompileInvariant.bind {α β : Type} (error : CompilerError → Prop) (post : α → Prop) (nextPost : β → Prop)
    (action : Compile α) (next : α → Compile β) (first : CompileInvariant error post action)
    (rest : ∀ value, post value → CompileInvariant error nextPost (next value)) :
    CompileInvariant error nextPost (action >>= next) := by
  intro state safe
  have held := first state safe
  cases executed : action.run state with
  | mk result middle =>
    have ran : action state = (result,middle) := executed
    rw [executed] at held
    cases result with
    | error failure =>
      simpa [Bind.bind,Pure.pure,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.run,StateT.bind,StateT.pure,ran] using held
    | ok value =>
      simpa [Bind.bind,Pure.pure,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.run,StateT.bind,StateT.pure,ran] using rest value held.1 middle held.2

private theorem CompileInvariant.pure {α : Type} (error : CompilerError → Prop) (post : α → Prop)
    (value : α) (held : post value) : CompileInvariant error post (pure value) := by
  intro state safe
  exact ⟨held,safe⟩

private theorem CompileInvariant.throw {α : Type} (error : CompilerError → Prop) (post : α → Prop)
    (failure : CompilerError) (held : error failure) : CompileInvariant error post (throw failure : Compile α) := by
  intro state safe
  exact ⟨held,safe⟩

private theorem CompileInvariant.get (error : CompilerError → Prop) :
    CompileInvariant error (CompilerErrors error) (get : Compile Compiler) := by
  intro state safe
  exact ⟨safe,safe⟩

private theorem CompileInvariant.set (error : CompilerError → Prop) (state : Compiler) (safe : CompilerErrors error state) :
    CompileInvariant error (fun _ => True) (set state : Compile Unit) := by
  intro before _
  exact ⟨True.intro,safe⟩

private theorem CompileInvariant.modify (error : CompilerError → Prop) (update : Compiler → Compiler)
    (preserves : ∀ state, CompilerErrors error state → CompilerErrors error (update state)) :
    CompileInvariant error (fun _ => True) (modify update : Compile Unit) := by
  intro state safe
  exact ⟨True.intro,preserves state safe⟩

private theorem CompileInvariant.fromExcept {α : Type} (error : CompilerError → Prop) (post : α → Prop)
    (result : Except CompilerError α) (held : ByteImage.BlockResult post error result) :
    CompileInvariant error post (fromExcept result) := by
  cases result
  · exact CompileInvariant.throw error post _ held
  · exact CompileInvariant.pure error post _ held

private theorem layout_error_allowed (error : CompilerError → Prop)
    (typeErrors : ∀ message, error (.typeError message))
    (unsupported : ∀ message, error (.unsupported .layout message)) (failure : SourceLayout.Error) :
    error (layoutError failure) := by
  cases failure <;> first | exact typeErrors _ | exact unsupported _

private theorem compile_throw_bind {α β : Type} (failure : CompilerError) (next : α → Compile β) :
    (throw failure : Compile α) >>= next = (throw failure : Compile β) := by
  funext state
  rfl

private theorem summary_errors (error : CompilerError → Prop)
    (typeErrors : ∀ message, error (.typeError message))
    (unsupported : ∀ message, error (.unsupported .layout message)) (ty : Ty) :
    CompileInvariant error (fun _ => True) (summary ty) := by
  unfold summary
  apply CompileInvariant.bind error (CompilerErrors error) (fun _ => True) _ _ (CompileInvariant.get error)
  intro snapshot safe
  cases cached : snapshot.layouts.findType ty with
  | some result =>
    have allowed := cache_find_errors error snapshot.layouts safe.2 ty result cached
    cases result with
    | ok value =>
      dsimp only
      exact CompileInvariant.pure error _ value True.intro
    | error failure =>
      dsimp only
      simp only [compile_throw_bind]
      exact CompileInvariant.throw error _ failure allowed
  | none =>
    cases queried : snapshot.source.query .execution ty with
    | error failure =>
      dsimp only
      simp only [pure_bind]
      have allowed := layout_error_allowed error typeErrors unsupported failure
      apply CompileInvariant.bind error (fun _ => True) (fun _ => True) _ _
        (CompileInvariant.set error {snapshot with layouts := snapshot.layouts.insertType ty (.error (layoutError failure))}
          ⟨safe.1,cache_insert_errors error snapshot.layouts safe.2 ty (.error (layoutError failure)) allowed⟩)
      intro _ _
      exact CompileInvariant.throw error _ _ allowed
    | ok pair =>
      obtain ⟨value,next⟩ := pair
      dsimp only
      simp only [pure_bind]
      apply CompileInvariant.bind error (fun _ => True) (fun _ => True) _ _
        (CompileInvariant.set error {snapshot with source := next,layouts := snapshot.layouts.insertType ty (.ok value)}
          ⟨safe.1,cache_insert_errors error snapshot.layouts safe.2 ty (.ok value) True.intro⟩)
      intro _ _
      exact CompileInvariant.pure error _ value True.intro

private theorem descend_errors (error : CompilerError → Prop) (typeErrors : ∀ message, error (.typeError message))
    (available : NatIndexTree Unit) (key : Nat) : ByteImage.BlockResult (fun _ => True) error (descend available key) := by
  unfold descend
  split
  · exact typeErrors _
  · exact True.intro

private theorem cache_plan_errors (error : CompilerError → Prop) (ty : Ty) (plan : Plan) :
    CompileInvariant error (fun _ => True) (modify fun state => {state with cache := state.cache.insertType ty (.ok plan)}) :=
  CompileInvariant.modify error _ (fun state safe =>
    ⟨cache_insert_errors error state.cache safe.1 ty (.ok plan) True.intro,safe.2⟩)

mutual
  private theorem compile_errors (error : CompilerError → Prop)
      (typeErrors : ∀ message, error (.typeError message))
      (unsupported : ∀ message, error (.unsupported .layout message)) (available : NatIndexTree Unit) (ty : Ty) :
      CompileInvariant error (fun _ => True) (compile available ty) := by
    rw [compile]
    apply CompileInvariant.bind error (CompilerErrors error) (fun _ => True) _ _ (CompileInvariant.get error)
    intro snapshot safe
    cases cached : snapshot.cache.findType ty with
    | some result =>
      have allowed := cache_find_errors error snapshot.cache safe.1 ty result cached
      cases result with
      | ok plan =>
        dsimp only [fromExcept]
        exact CompileInvariant.pure error _ plan True.intro
      | error failure =>
        dsimp only [fromExcept]
        simp only [compile_throw_bind]
        exact CompileInvariant.throw error _ failure allowed
    | none =>
      dsimp only
      simp only [pure_bind]
      apply CompileInvariant.bind error (fun _ => True) (fun _ => True) _ _ (summary_errors error typeErrors unsupported ty)
      intro value _
      repeat' first
        | (simp only [compile_throw_bind,pure_bind])
        | (solve | exact CompileInvariant.pure error _ _ True.intro)
        | (solve | exact CompileInvariant.throw error _ _ (typeErrors _))
        | (solve | exact CompileInvariant.throw error _ _ (unsupported _))
        | (refine CompileInvariant.bind error (fun _ => True) (fun _ => True) _ _ (cache_plan_errors error _ _) ?_; intro _ _)
        | (refine CompileInvariant.bind error (fun _ => True) (fun _ => True) _ _
            (CompileInvariant.fromExcept error (fun _ => True) _ (descend_errors error typeErrors available _)) ?_; intro smaller _)
        | (with_reducible refine (CompileInvariant.bind error (fun _ => True) (fun _ => True) _ _
            (compile_errors error typeErrors unsupported _ _) ?_); intro plan _)
        | (with_reducible refine (CompileInvariant.bind error (fun _ => True) (fun _ => True) _ _
            (compileFields_errors error typeErrors unsupported _ _ _) ?_); intro fields _)
        | (with_reducible refine (CompileInvariant.bind error (fun _ => True) (fun _ => True) _ _
            (compileVariants_errors error typeErrors unsupported _ _ _ _) ?_); intro variants _)
        | split
        | (dsimp only; split)
  termination_by (Available.size available,sizeOf ty)

  private theorem compileFields_errors (error : CompilerError → Prop)
      (typeErrors : ∀ message, error (.typeError message))
      (unsupported : ∀ message, error (.unsupported .layout message)) (available : NatIndexTree Unit)
      (types : List Ty) (offsets : List Field) :
      CompileInvariant error (fun _ => True) (compileFields available types offsets) := by
    cases types <;> cases offsets <;> rw [compileFields]
    all_goals repeat' first
      | (solve | simp)
      | (solve | exact CompileInvariant.pure error _ _ True.intro)
      | (solve | exact CompileInvariant.throw error _ _ (typeErrors _))
      | (with_reducible refine (CompileInvariant.bind error (fun _ => True) (fun _ => True) _ _
          (compile_errors error typeErrors unsupported _ _) ?_); intro first _)
      | (with_reducible refine (CompileInvariant.bind error (fun _ => True) (fun _ => True) _ _
          (compileFields_errors error typeErrors unsupported _ _ _) ?_); intro rest _)
      | split
      | (dsimp only; split)
  termination_by (Available.size available,sizeOf types)

  private theorem compileVariants_errors (error : CompilerError → Prop)
      (typeErrors : ∀ message, error (.typeError message))
      (unsupported : ∀ message, error (.unsupported .layout message)) (available : NatIndexTree Unit)
      (types : List (List Ty)) (offsets : List (List Field)) (dead : List Bool) :
      CompileInvariant error (fun _ => True) (compileVariants available types offsets dead) := by
    cases types <;> cases offsets <;> cases dead <;> rw [compileVariants]
    all_goals repeat' first
      | (solve | simp)
      | (solve | exact CompileInvariant.pure error _ _ True.intro)
      | (solve | exact CompileInvariant.throw error _ _ (typeErrors _))
      | (simp only [pure_bind])
      | (with_reducible refine (CompileInvariant.bind error (fun _ => True) (fun _ => True) _ _
          (compileFields_errors error typeErrors unsupported _ _ _) ?_); intro first _)
      | (with_reducible refine (CompileInvariant.bind error (fun _ => True) (fun _ => True) _ _
          (compileVariants_errors error typeErrors unsupported _ _ _ _) ?_); intro rest _)
      | split
      | (dsimp only; split)
  termination_by (Available.size available,sizeOf types)
end

/-- Exact array compiler clause. Its abstract count avoids normalizing the
    recursive compiler's termination rank at a huge literal logical length. -/
theorem compile_array (available : NatIndexTree Unit) (element : TyId) (count : Nat) :
    compile available (.Array element count) = (do
      let ty := Ty.Array element count
      let initial ← get
      if let some result := initial.cache.findType ty then return ← fromExcept result
      let value ← summary ty
      let alignment ← match value.align with
        | some alignment => pure alignment
        | none => throw (.unsupported .layout "memory: type has no byte alignment")
      let layout : MemoryTypeLayout := { size := value.size, alignment }
      let index := initial.source.index
      let plan ← do
        let smaller ← fromExcept (descend available element.index)
        let child ← match (trustIrArrayGet? index.typeRows element.index).join with
          | some child => pure child
          | none => throw (.typeError "memory: array element type is missing")
        pure (.array ty layout count (← compile smaller.val child))
      modify fun state => { state with cache := state.cache.insertType ty (.ok plan) }
      pure plan) := by
  trustIrCompilerProof {
    conv =>
      lhs
      delta compile compile._mutual
      rw [WellFounded.fix_eq]
    rfl
  } {
    rw [compile]
  }

/-- The authenticated layout query remains part of compiling an item leaf. -/
theorem compile_fnItem (available : NatIndexTree Unit) (target : FuncId) :
    compile available (.FnItem target) = (do
      let ty := Ty.FnItem target
      let initial ← get
      if let some result := initial.cache.findType ty then return ← fromExcept result
      let value ← summary ty
      let alignment ← match value.align with
        | some alignment => pure alignment
        | none => throw (.unsupported .layout "memory: type has no byte alignment")
      let plan := Plan.fnItem target { size := value.size, alignment }
      modify fun state => { state with cache := state.cache.insertType ty (.ok plan) }
      pure plan) := by
  conv =>
    lhs
    delta compile compile._mutual
    rw [WellFounded.fix_eq]
  rfl

/-- Module-static memory roots retain both successful plans and refusals. -/
structure Service where
  private compiler : Compiler
  private available : NatIndexTree Unit

private def runCompile (service : Service) (ty : Ty) : Except CompilerError Plan × Service :=
  match service.compiler.cache.findType ty with
  | some result => (result, service)
  | none =>
    let (result, state) := (compile service.available ty).run service.compiler
    let state := { state with cache := state.cache.insertType ty result }
    (result, { service with compiler := state })

/-- Expose the actual cached compiler, including memoized refusals. -/
theorem runCompile_eq (service : Service) (ty : Ty) :
    runCompile service ty =
      (match service.compiler.cache.findType ty with
      | some result => (result, service)
      | none =>
        let (result, state) := (compile service.available ty).run service.compiler
        let state := { state with cache := state.cache.insertType ty result }
        (result, { service with compiler := state })) := rfl

def prepare (source : Environment) (roots : List Ty) : Service := Id.run do
  let session := SourceLayout.prepare source
  let mut available := NatIndexTree.empty
  for node in List.range session.index.count do available := available.insert node ()
  let mut service : Service := { compiler := { source := session }, available }
  for ty in roots do service := (runCompile service ty).2
  pure service

/-- Decoded roots hit the prepared cache. Uncached manual questions compute
    honestly; there is no refusal-to-legacy fallback. -/
private def Service.queryStatic (service : Service) (ty : Ty) : Except CompilerError Plan :=
  match service.compiler.cache.findType ty with
  | some result => result
  | none => (runCompile service ty).1

/-- Public runtime integration embeds the intrinsically static compiler result. -/
def Service.query (service : Service) (ty : Ty) : Except SemError Plan :=
  semanticResult (service.queryStatic ty)

def Service.model (service : Service) : ByteModel := service.compiler.source.index.source.model

private def summaryLayout (result : Except CompilerError Summary) : Except CompilerError MemoryTypeLayout := do
  let value ← result
  match value.align with
  | some alignment => pure { size := value.size, alignment }
  | none => .error (.unsupported .layout "memory: type has no byte alignment")

/-- Layout queries do not require an executable image codec. In particular,
    allocation, GEP and BSS use producer tuple size/alignment even when an
    embedded Closure/Refine byte codec remains explicitly unsupported. -/
private def Service.queryStaticLayoutWithWork (service : Service) (ty : Ty) : Except CompilerError MemoryTypeLayout × Nat :=
  match service.compiler.layouts.findType ty with
  | some result => (summaryLayout result, 0)
  | none =>
    let result := match service.compiler.source.query .execution ty with
      | .ok (value, _) => .ok value
      | .error error => .error (layoutError error)
    (summaryLayout result, 1)

private def Service.queryStaticLayout (service : Service) (ty : Ty) : Except CompilerError MemoryTypeLayout :=
  (service.queryStaticLayoutWithWork ty).1

def Service.queryLayoutWithWork (service : Service) (ty : Ty) : Except SemError MemoryTypeLayout × Nat :=
  let (result, work) := service.queryStaticLayoutWithWork ty
  (semanticResult result, work)

def Service.queryLayout (service : Service) (ty : Ty) : Except SemError MemoryTypeLayout :=
  (service.queryLayoutWithWork ty).1

/-- Diagnostic counts actual plan-compiler invocations. A cached request
    executes neither source layout traversal nor plan compilation. -/
def Service.queryWithWork (service : Service) (ty : Ty) : Except SemError Plan × Nat :=
  match service.compiler.cache.findType ty with
  | some result => (semanticResult result, 0)
  | none => (semanticResult (runCompile service ty).1, 1)

private def ServiceCompilerErrors (error : CompilerError → Prop) (service : Service) : Prop :=
  CompilerErrors error service.compiler

private theorem runCompile_errors (error : CompilerError → Prop)
    (typeErrors : ∀ message, error (.typeError message))
    (unsupported : ∀ message, error (.unsupported .layout message)) (service : Service) (ty : Ty)
    (safe : ServiceCompilerErrors error service) :
    ByteImage.BlockResult (fun _ => True) error (runCompile service ty).1 ∧
      ServiceCompilerErrors error (runCompile service ty).2 := by
  unfold runCompile
  cases cached : service.compiler.cache.findType ty with
  | some result => exact ⟨cache_find_errors error service.compiler.cache safe.1 ty result cached,safe⟩
  | none =>
    have held := compile_errors error typeErrors unsupported service.available ty service.compiler safe
    cases executed : (compile service.available ty).run service.compiler with
    | mk result state =>
      rw [executed] at held
      exact ⟨held.1,cache_insert_errors error state.cache held.2.1 ty result held.1,held.2.2⟩

private theorem roots_errors (error : CompilerError → Prop)
    (typeErrors : ∀ message, error (.typeError message))
    (unsupported : ∀ message, error (.unsupported .layout message)) (roots : List Ty) (service : Service)
    (safe : ServiceCompilerErrors error service) :
    ServiceCompilerErrors error (Id.run (forIn roots service (fun ty current =>
      pure (.yield (runCompile current ty).2)))) := by
  induction roots generalizing service with
  | nil => exact safe
  | cons ty rest ih =>
    rw [List.forIn_cons]
    exact ih _ (runCompile_errors error typeErrors unsupported service ty safe).2

private theorem prepare_compiler_errors (error : CompilerError → Prop)
    (typeErrors : ∀ message, error (.typeError message))
    (unsupported : ∀ message, error (.unsupported .layout message)) (source : Environment) (roots : List Ty) :
    ServiceCompilerErrors error (prepare source roots) := by
  unfold prepare
  dsimp only
  apply roots_errors error typeErrors unsupported roots
  exact ⟨cache_empty_errors error,cache_empty_errors error⟩

private theorem query_errors (error : CompilerError → Prop)
    (typeErrors : ∀ message, error (.typeError message))
    (unsupported : ∀ message, error (.unsupported .layout message)) (service : Service) (ty : Ty)
    (safe : ServiceCompilerErrors error service) : ByteImage.BlockResult (fun _ => True) error (service.queryStatic ty) := by
  unfold Service.queryStatic
  cases cached : service.compiler.cache.findType ty with
  | some result => exact cache_find_errors error service.compiler.cache safe.1 ty result cached
  | none => exact (runCompile_errors error typeErrors unsupported service ty safe).1

private theorem summary_layout_errors (error : CompilerError → Prop)
    (unsupported : ∀ message, error (.unsupported .layout message)) (result : Except CompilerError Summary)
    (safe : ByteImage.BlockResult (fun _ => True) error result) :
    ByteImage.BlockResult (fun _ => True) error (summaryLayout result) := by
  unfold summaryLayout
  apply ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _ safe
  intro value _
  cases value.align with
  | none => exact unsupported _
  | some alignment => exact True.intro

private theorem query_layout_errors (error : CompilerError → Prop)
    (typeErrors : ∀ message, error (.typeError message))
    (unsupported : ∀ message, error (.unsupported .layout message)) (service : Service) (ty : Ty)
    (safe : ServiceCompilerErrors error service) : ByteImage.BlockResult (fun _ => True) error (service.queryStaticLayout ty) := by
  unfold Service.queryStaticLayout Service.queryStaticLayoutWithWork
  cases cached : service.compiler.layouts.findType ty with
  | some result => exact summary_layout_errors error unsupported result (cache_find_errors error service.compiler.layouts safe.2 ty result cached)
  | none =>
    apply summary_layout_errors error unsupported
    cases queried : service.compiler.source.query .execution ty with
    | error failure => exact layout_error_allowed error typeErrors unsupported failure
    | ok pair => exact True.intro

/-- Plan and byte-layout requests may retain static source refusals; their
error policy is explicit for both prepared cache hits and uncached questions. -/
def ServiceErrorPolicy (error : SemError → Prop) (service : Service) : Prop :=
  ∀ ty, ByteImage.BlockResult (fun _ => True) error (service.query ty) ∧
    ByteImage.BlockResult (fun _ => True) error (service.queryLayout ty)

private theorem semanticResult_error_policy {α : Type} (error : SemError → Prop)
    (typeErrors : ∀ message, error (.typeError message))
    (unsupported : ∀ message, error (.unsupported .layout message)) (result : Except CompilerError α) :
    ByteImage.BlockResult (fun _ => True) error (semanticResult result) := by
  cases result with
  | ok value => exact True.intro
  | error failure =>
    cases failure with
    | typeError message => exact typeErrors message
    | unsupported feature message => cases feature; exact unsupported message

/-- Every service value has a static error domain, including arbitrary cached
refusals and uncached questions. No preparation or context premise is required. -/
theorem Service.error_policy (error : SemError → Prop)
    (typeErrors : ∀ message, error (.typeError message))
    (unsupported : ∀ message, error (.unsupported .layout message)) (service : Service) :
    ServiceErrorPolicy error service := by
  intro ty
  constructor
  · exact semanticResult_error_policy error typeErrors unsupported (service.queryStatic ty)
  · change ByteImage.BlockResult (fun _ => True) error (semanticResult (service.queryStaticLayout ty))
    exact semanticResult_error_policy error typeErrors unsupported (service.queryStaticLayout ty)

/-- Original preparation discharges the cache invariant for every source
and root list, including negative cache entries and later uncached queries. -/
theorem prepare_error_policy (error : SemError → Prop)
    (typeErrors : ∀ message, error (.typeError message))
    (unsupported : ∀ message, error (.unsupported .layout message)) (source : Environment) (roots : List Ty) :
    ServiceErrorPolicy error (prepare source roots) :=
  Service.error_policy error typeErrors unsupported (prepare source roots)

/-- Typed cache invariants authenticate equality matches, not hash buckets. -/
private def CacheOrigins {α : Type} (property : Ty → α → Prop)
    (cache : NatIndexTree (List (Ty × Except CompilerError α))) : Prop :=
  ∀ key rows, cache.find key = some rows → ∀ row ∈ rows,
    ByteImage.BlockResult (property row.1) (fun _ => True) row.2

private theorem cache_origins_empty {α : Type} (property : Ty → α → Prop) :
    CacheOrigins property (.empty : NatIndexTree (List (Ty × Except CompilerError α))) := by
  intro key rows found; cases found

private theorem find_row_true {α : Type} (test : α → Bool) (rows : List α) (row : α)
    (found : rows.find? test = some row) : test row = true := by
  induction rows with
  | nil => cases found
  | cons first rest ih =>
    rw [List.find?_cons] at found
    cases selected : test first <;> simp only [selected] at found
    · exact ih found
    · cases found; exact selected

private theorem cache_origins_rows {α : Type} (property : Ty → α → Prop)
    (cache : NatIndexTree (List (Ty × Except CompilerError α))) (safe : CacheOrigins property cache) (key : Nat) :
    ∀ row ∈ (cache.find key).getD [], ByteImage.BlockResult (property row.1) (fun _ => True) row.2 := by
  cases found : cache.find key with
  | none => intro row member; cases member
  | some rows => exact safe key rows found

private theorem cache_origins_find {α : Type} (property : Ty → α → Prop)
    (cache : NatIndexTree (List (Ty × Except CompilerError α))) (safe : CacheOrigins property cache)
    (ty : Ty) (result : Except CompilerError α)
    (found : (((cache.find (typeBucket ty)).getD []).find? (fun row => closureTyEq row.1 ty)).map (·.2) = some result) :
    ByteImage.BlockResult (property ty) (fun _ => True) result := by
  cases selected : ((cache.find (typeBucket ty)).getD []).find? (fun row => closureTyEq row.1 ty) with
  | none => simp [selected] at found
  | some row =>
    simp only [selected,Option.map,Option.some.injEq] at found
    subst result
    have same := closureTyEq_sound row.1 ty (find_row_true _ _ row selected)
    have held := cache_origins_rows property cache safe _ row (find_row_mem _ _ row selected)
    rw [same] at held
    exact held

private theorem cache_origins_insert {α : Type} (property : Ty → α → Prop)
    (cache : NatIndexTree (List (Ty × Except CompilerError α))) (safe : CacheOrigins property cache)
    (ty : Ty) (result : Except CompilerError α) (held : ByteImage.BlockResult (property ty) (fun _ => True) result) :
    CacheOrigins property (cache.insert (typeBucket ty) ((ty,result) :: (cache.find (typeBucket ty)).getD [])) := by
  intro key rows found row member
  rw [NatIndexTree.find_insert] at found
  split at found
  · cases found
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact held
    · exact cache_origins_rows property cache safe _ row member
  · exact safe key rows found row member

private def CompilerOrigins (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (sessions : Session → Prop) (state : Compiler) : Prop :=
  sessions state.source ∧ CacheOrigins (Plan.Origin resolves valid) state.cache ∧ CacheOrigins valid state.layouts

private def OriginAction {α : Type} (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (sessions : Session → Prop)
    (post : α → Prop) (action : Compile α) : Prop :=
  ∀ state, CompilerOrigins resolves valid sessions state →
    ByteImage.BlockResult post (fun _ => True) (action.run state).1 ∧ CompilerOrigins resolves valid sessions (action.run state).2

private theorem OriginAction.bind {α β : Type} (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (sessions : Session → Prop)
    (post : α → Prop) (nextPost : β → Prop) (action : Compile α) (next : α → Compile β)
    (first : OriginAction resolves valid sessions post action)
    (rest : ∀ value, post value → OriginAction resolves valid sessions nextPost (next value)) :
    OriginAction resolves valid sessions nextPost (action >>= next) := by
  intro state safe
  have held := first state safe
  cases executed : action.run state with
  | mk result middle =>
    have ran : action state = (result,middle) := executed
    rw [executed] at held
    cases result with
    | error failure =>
      simpa [Bind.bind,Pure.pure,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.run,StateT.bind,StateT.pure,ran] using held
    | ok value =>
      simpa [Bind.bind,Pure.pure,ExceptT.bind,ExceptT.bindCont,ExceptT.run,ExceptT.mk,StateT.run,StateT.bind,StateT.pure,ran] using rest value held.1 middle held.2

private theorem OriginAction.pure {α : Type} (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (sessions : Session → Prop)
    (post : α → Prop) (value : α) (held : post value) : OriginAction resolves valid sessions post (pure value) := by
  intro state safe; exact ⟨held,safe⟩

private theorem OriginAction.throw {α : Type} (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (sessions : Session → Prop)
    (post : α → Prop) (failure : CompilerError) : OriginAction resolves valid sessions post (throw failure : Compile α) := by
  intro state safe; exact ⟨True.intro,safe⟩

private theorem OriginAction.get (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (sessions : Session → Prop) :
    OriginAction resolves valid sessions (CompilerOrigins resolves valid sessions) (get : Compile Compiler) := by
  intro state safe; exact ⟨safe,safe⟩

private theorem OriginAction.set (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (sessions : Session → Prop)
    (state : Compiler) (safe : CompilerOrigins resolves valid sessions state) :
    OriginAction resolves valid sessions (fun _ => True) (set state : Compile Unit) := by
  intro before _; exact ⟨True.intro,safe⟩

private theorem OriginAction.modify (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (sessions : Session → Prop)
    (update : Compiler → Compiler)
    (preserves : ∀ state, CompilerOrigins resolves valid sessions state → CompilerOrigins resolves valid sessions (update state)) :
    OriginAction resolves valid sessions (fun _ => True) (modify update : Compile Unit) := by
  intro state safe; exact ⟨True.intro,preserves state safe⟩

private theorem OriginAction.fromExcept {α : Type} (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (sessions : Session → Prop)
    (result : Except CompilerError α) : OriginAction resolves valid sessions (fun _ => True) (fromExcept result) := by
  cases result
  · exact OriginAction.throw resolves valid sessions _ _
  · exact OriginAction.pure resolves valid sessions _ _ True.intro

/-- The generic compiler proof needs the real successful source transition.
    Logical reachability and exact query witnesses instantiate this later. -/
structure QueryOriginPolicy (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop)
    (sessions : Session → Prop) : Prop where
  query : ∀ session, sessions session → ∀ ty value next,
    session.query .execution ty = .ok (value,next) → valid ty value ∧ sessions next
  resolve : ∀ session, sessions session → ∀ id ty,
    ((trustIrArrayGet? session.index.typeRows id.index)).join = some ty → resolves id ty

private theorem summary_origins (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (sessions : Session → Prop)
    (policy : QueryOriginPolicy resolves valid sessions) (ty : Ty) : OriginAction resolves valid sessions (valid ty) (summary ty) := by
  unfold summary
  apply OriginAction.bind resolves valid sessions (CompilerOrigins resolves valid sessions) (valid ty) _ _ (OriginAction.get resolves valid sessions)
  intro snapshot safe
  cases cached : snapshot.layouts.findType ty with
  | some result =>
    have allowed := cache_origins_find valid snapshot.layouts safe.2.2 ty result cached
    cases result with
    | ok value =>
      dsimp only
      exact OriginAction.pure resolves valid sessions _ value allowed
    | error failure =>
      dsimp only
      simp only [compile_throw_bind]
      exact OriginAction.throw resolves valid sessions _ failure
  | none =>
    cases queried : snapshot.source.query .execution ty with
    | error failure =>
      dsimp only
      simp only [pure_bind]
      apply OriginAction.bind resolves valid sessions (fun _ => True) (valid ty) _ _
        (OriginAction.set resolves valid sessions {snapshot with layouts := snapshot.layouts.insertType ty (.error (layoutError failure))}
          ⟨safe.1,safe.2.1,cache_origins_insert valid snapshot.layouts safe.2.2 ty _ True.intro⟩)
      intro _ _
      exact OriginAction.throw resolves valid sessions _ _
    | ok pair =>
      obtain ⟨value,next⟩ := pair
      have origin := policy.query snapshot.source safe.1 ty value next queried
      dsimp only
      simp only [pure_bind]
      apply OriginAction.bind resolves valid sessions (fun _ => True) (valid ty) _ _
        (OriginAction.set resolves valid sessions {snapshot with source := next,layouts := snapshot.layouts.insertType ty (.ok value)}
          ⟨origin.2,safe.2.1,cache_origins_insert valid snapshot.layouts safe.2.2 ty _ origin.1⟩)
      intro _ _
      exact OriginAction.pure resolves valid sessions _ value origin.1

private theorem cache_plan_origin (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (sessions : Session → Prop)
    (ty : Ty) (plan : Plan) (origin : Plan.Origin resolves valid ty plan) :
    OriginAction resolves valid sessions (fun _ => True) (modify fun state => {state with cache := state.cache.insertType ty (.ok plan)}) :=
  OriginAction.modify resolves valid sessions _ (fun state safe =>
    ⟨safe.1,cache_origins_insert (Plan.Origin resolves valid) state.cache safe.2.1 ty (.ok plan) origin,safe.2.2⟩)

private def FieldOrigins (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (fields : List (Nat × Plan)) : Prop :=
  ∀ field ∈ fields, Plan.Origin resolves valid field.2.ty field.2

private theorem field_origins_nil (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) : FieldOrigins resolves valid [] := by
  intro field member; cases member

private theorem field_origins_cons (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (ty : Ty) (plan : Plan) (offset : Nat)
    (rest : List (Nat × Plan)) (first : Plan.Origin resolves valid ty plan) (later : FieldOrigins resolves valid rest) :
    FieldOrigins resolves valid ((offset,plan) :: rest) := by
  intro field member
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · exact first.own
  · exact later field member

private structure FieldCompilation (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (types : List Ty)
    (metadata : List Field) (fields : List (Nat × Plan)) : Prop where
  children : FieldOrigins resolves valid fields
  inputs : FieldBindings types (metadata.map (·.offset)) fields
  sourceTypes : types = metadata.map (·.ty)
  extents : FieldExtents metadata fields

private theorem FieldCompilation.metadata {resolves : TyId → Ty → Prop} {valid : Ty → Summary → Prop} {types : List Ty}
    {metadata : List Field} {fields : List (Nat × Plan)} (compiled : FieldCompilation resolves valid types metadata fields) :
    FieldBindings (metadata.map (·.ty)) (metadata.map (·.offset)) fields := by
  rw [← compiled.sourceTypes]
  exact compiled.inputs

private theorem FieldCompilation.nil (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) : FieldCompilation resolves valid [] [] [] :=
  ⟨field_origins_nil resolves valid,⟨rfl,rfl⟩,rfl,rfl⟩

private theorem FieldCompilation.cons (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (ty : Ty) (plan : Plan)
    (field : Field) (types : List Ty) (metadata : List Field) (rest : List (Nat × Plan))
    (first : Plan.Origin resolves valid ty plan) (later : FieldCompilation resolves valid types metadata rest)
    (typed : ty = field.ty) (sized : plan.layout.size = field.size) :
    FieldCompilation resolves valid (ty :: types) (field :: metadata) ((field.offset,plan) :: rest) := by
  refine ⟨field_origins_cons resolves valid ty plan field.offset rest first later.children,?_,?_,?_⟩
  · constructor
    · change plan.ty :: rest.map (fun field => field.2.ty) = ty :: types
      rw [first.type,later.inputs.1]
    · change field.offset :: rest.map (·.1) = field.offset :: metadata.map (·.offset)
      rw [later.inputs.2]
  · change ty :: types = field.ty :: metadata.map (·.ty)
    rw [typed,later.sourceTypes]
  · change plan.layout.size :: rest.map (fun field => field.2.layout.size) = field.size :: metadata.map (·.size)
    rw [sized,later.extents]

private structure VariantCompilation (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (types : List (List Ty))
    (metadata : List (List Field)) (dead : List Bool) (variants : List (Option (List (Nat × Plan)))) : Prop where
  children : VariantOrigins resolves valid dead variants
  bindings : VariantBindings types (metadata.map (fun fields => fields.map (·.offset))) dead variants
  extents : VariantExtents metadata variants

private theorem VariantCompilation.nil (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) : VariantCompilation resolves valid [] [] [] [] :=
  ⟨.nil,.nil,VariantExtents.nil⟩

private theorem VariantCompilation.omitted (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (firstTypes : List Ty)
    (firstMetadata : List Field) {types : List (List Ty)} {metadata : List (List Field)} {dead : List Bool}
    {variants : List (Option (List (Nat × Plan)))} (later : VariantCompilation resolves valid types metadata dead variants) :
    VariantCompilation resolves valid (firstTypes :: types) (firstMetadata :: metadata) (true :: dead) (none :: variants) :=
  ⟨.omitted later.children,
    by simpa only [List.map_cons] using
      (VariantBindings.omitted firstTypes (firstMetadata.map (fun (field : Field) => field.offset)) later.bindings),
    VariantExtents.omitted firstMetadata later.extents⟩

private theorem VariantCompilation.live (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) {firstTypes : List Ty}
    {firstMetadata : List Field} {fields : List (Nat × Plan)} {types : List (List Ty)}
    {metadata : List (List Field)} {dead : List Bool} {variants : List (Option (List (Nat × Plan)))}
    (first : FieldCompilation resolves valid firstTypes firstMetadata fields)
    (later : VariantCompilation resolves valid types metadata dead variants) :
    VariantCompilation resolves valid (firstTypes :: types) (firstMetadata :: metadata) (false :: dead) (some fields :: variants) :=
  ⟨.live first.children later.children,.live first.inputs later.bindings,
    VariantExtents.live first.extents later.extents⟩

private theorem cache_yield_origin (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (sessions : Session → Prop)
    (ty : Ty) (plan : Plan) (origin : Plan.Origin resolves valid ty plan) :
    OriginAction resolves valid sessions (Plan.Origin resolves valid ty) (do
      modify fun state => {state with cache := state.cache.insertType ty (.ok plan)}
      pure plan) := by
  apply OriginAction.bind resolves valid sessions (fun _ => True) (Plan.Origin resolves valid ty) _ _
    (cache_plan_origin resolves valid sessions ty plan origin)
  intro _ _
  exact OriginAction.pure resolves valid sessions _ plan origin

set_option maxHeartbeats 2000000 in
mutual
  private theorem compile_origins (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (sessions : Session → Prop)
      (policy : QueryOriginPolicy resolves valid sessions) (available : NatIndexTree Unit) (ty : Ty) :
      OriginAction resolves valid sessions (Plan.Origin resolves valid ty) (compile available ty) := by
    rw [compile]
    apply OriginAction.bind resolves valid sessions (CompilerOrigins resolves valid sessions) (Plan.Origin resolves valid ty) _ _ (OriginAction.get resolves valid sessions)
    intro snapshot safe
    cases cached : snapshot.cache.findType ty with
    | some result =>
      have origin := cache_origins_find (Plan.Origin resolves valid) snapshot.cache safe.2.1 ty result cached
      cases result with
      | ok plan =>
        dsimp only [fromExcept]
        exact OriginAction.pure resolves valid sessions _ plan origin
      | error failure =>
        dsimp only [fromExcept]
        simp only [compile_throw_bind]
        exact OriginAction.throw resolves valid sessions _ failure
    | none =>
      dsimp only
      simp only [pure_bind]
      apply OriginAction.bind resolves valid sessions (valid ty) (Plan.Origin resolves valid ty) _ _ (summary_origins resolves valid sessions policy ty)
      intro value valueOrigin
      cases aligned : value.align with
      | none =>
        dsimp only
        simp only [compile_throw_bind]
        exact OriginAction.throw resolves valid sessions _ _
      | some alignment =>
        dsimp only
        try simp only [pure_bind]
        cases ty <;> dsimp only
        all_goals repeat' first
          | (solve | simp)
          | (simp only [compile_throw_bind,pure_bind])
          | (solve | apply cache_yield_origin resolves valid sessions; exact .fnItem _ _ value valueOrigin ⟨rfl,aligned⟩)
          | (solve | apply cache_yield_origin resolves valid sessions; exact .leaf _ _ True.intro value valueOrigin ⟨rfl,aligned⟩)
          | (solve | apply cache_yield_origin resolves valid sessions; exact .fields _ _ _ True.intro fieldsOrigin.children value valueOrigin ⟨rfl,aligned⟩ (by simpa only [Plan.fieldInputTypes] using fieldsOrigin.inputs) fieldsOrigin.metadata fieldsOrigin.extents)
          | (solve | apply cache_yield_origin resolves valid sessions; exact .array _ _ _ _ (by apply Plan.Origin.own; assumption) (by
              apply policy.resolve snapshot.source safe.1
              first | assumption | simpa only [childOrigin.type] using (by assumption)) value valueOrigin ⟨rfl,aligned⟩)
          | (solve | apply cache_yield_origin resolves valid sessions; exact .enumeration _ _ _ _ value valueOrigin (by assumption) ⟨rfl,aligned⟩ variantsOrigin.children variantsOrigin.bindings variantsOrigin.extents)
          | (solve | exact OriginAction.throw resolves valid sessions _ _)
          | (refine OriginAction.bind resolves valid sessions (fun _ => True) _ _ _
              (OriginAction.fromExcept resolves valid sessions _) ?_; intro smaller _)
          | (with_reducible refine (OriginAction.bind resolves valid sessions (Plan.Origin resolves valid _) _ _ _
              (compile_origins resolves valid sessions policy _ _) ?_); intro child childOrigin)
          | (with_reducible refine (OriginAction.bind resolves valid sessions (FieldCompilation resolves valid _ _) _ _ _
              (compileFields_origins resolves valid sessions policy _ _ _) ?_); intro fields fieldsOrigin)
          | (with_reducible refine (OriginAction.bind resolves valid sessions (VariantCompilation resolves valid _ _ _) _ _ _
              (compileVariants_origins resolves valid sessions policy _ _ _ _) ?_); intro variants variantsOrigin)
          | (simp_all only [Bool.not_eq_true])
          | split
          | (dsimp only; split)
  termination_by (Available.size available,sizeOf ty)

  private theorem compileFields_origins (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (sessions : Session → Prop)
      (policy : QueryOriginPolicy resolves valid sessions) (available : NatIndexTree Unit) (types : List Ty) (offsets : List Field) :
      OriginAction resolves valid sessions (FieldCompilation resolves valid types offsets) (compileFields available types offsets) := by
    cases types <;> cases offsets <;> rw [compileFields]
    all_goals repeat' first
      | (solve | simp)
      | (simp only [compile_throw_bind,pure_bind])
      | (solve | exact OriginAction.pure resolves valid sessions _ _ (FieldCompilation.nil resolves valid))
      | (solve | apply OriginAction.pure resolves valid sessions; exact FieldCompilation.cons resolves valid _ _ _ _ _ _ firstOrigin restOrigin (by apply closureTyEq_sound; assumption) (by assumption))
      | (solve | exact OriginAction.throw resolves valid sessions _ _)
      | (with_reducible refine (OriginAction.bind resolves valid sessions (Plan.Origin resolves valid _) _ _ _
          (compile_origins resolves valid sessions policy _ _) ?_); intro first firstOrigin)
      | (with_reducible refine (OriginAction.bind resolves valid sessions (FieldCompilation resolves valid _ _) _ _ _
          (compileFields_origins resolves valid sessions policy _ _ _) ?_); intro rest restOrigin)
      | (simp_all only [Bool.not_eq_true])
      | split
      | (dsimp only; split)
  termination_by (Available.size available,sizeOf types)

  private theorem compileVariants_origins (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (sessions : Session → Prop)
      (policy : QueryOriginPolicy resolves valid sessions) (available : NatIndexTree Unit)
      (types : List (List Ty)) (offsets : List (List Field)) (dead : List Bool) :
      OriginAction resolves valid sessions (VariantCompilation resolves valid types offsets dead) (compileVariants available types offsets dead) := by
    cases types <;> cases offsets <;> cases dead <;> rw [compileVariants]
    all_goals repeat' first
      | (solve | simp)
      | (simp only [compile_throw_bind,pure_bind])
      | (solve | exact OriginAction.pure resolves valid sessions _ _ (VariantCompilation.nil resolves valid))
      | (solve | apply OriginAction.pure resolves valid sessions; exact VariantCompilation.omitted resolves valid _ _ restOrigin)
      | (solve | apply OriginAction.pure resolves valid sessions; exact VariantCompilation.live resolves valid firstOrigin restOrigin)
      | (solve | exact OriginAction.throw resolves valid sessions _ _)
      | (with_reducible refine (OriginAction.bind resolves valid sessions (FieldCompilation resolves valid _ _) _ _ _
          (compileFields_origins resolves valid sessions policy _ _ _) ?_); intro first firstOrigin)
      | (with_reducible refine (OriginAction.bind resolves valid sessions (VariantCompilation resolves valid _ _ _) _ _ _
          (compileVariants_origins resolves valid sessions policy _ _ _ _) ?_); intro rest restOrigin)
      | (simp_all only [Bool.not_eq_true])
      | split
      | (dsimp only; split)
  termination_by (Available.size available,sizeOf types)
end

private theorem runCompile_origins (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (sessions : Session → Prop)
    (policy : QueryOriginPolicy resolves valid sessions) (service : Service) (ty : Ty)
    (safe : CompilerOrigins resolves valid sessions service.compiler) :
    ByteImage.BlockResult (Plan.Origin resolves valid ty) (fun _ => True) (runCompile service ty).1 ∧
      CompilerOrigins resolves valid sessions (runCompile service ty).2.compiler := by
  unfold runCompile
  cases cached : service.compiler.cache.findType ty with
  | some result => exact ⟨cache_origins_find (Plan.Origin resolves valid) service.compiler.cache safe.2.1 ty result cached,safe⟩
  | none =>
    have held := compile_origins resolves valid sessions policy service.available ty service.compiler safe
    cases executed : (compile service.available ty).run service.compiler with
    | mk result state =>
      rw [executed] at held
      exact ⟨held.1,held.2.1,cache_origins_insert (Plan.Origin resolves valid) state.cache held.2.2.1 ty result held.1,held.2.2.2⟩

private theorem roots_origins (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (sessions : Session → Prop)
    (policy : QueryOriginPolicy resolves valid sessions) (roots : List Ty) (service : Service)
    (safe : CompilerOrigins resolves valid sessions service.compiler) :
    CompilerOrigins resolves valid sessions (Id.run (forIn roots service (fun ty current =>
      pure (.yield (runCompile current ty).2)))).compiler := by
  induction roots generalizing service with
  | nil => exact safe
  | cons ty rest ih =>
    rw [List.forIn_cons]
    exact ih _ (runCompile_origins resolves valid sessions policy service ty safe).2

private theorem prepare_compiler_origins (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (sessions : Session → Prop)
    (policy : QueryOriginPolicy resolves valid sessions) (source : Environment)
    (initial : sessions (SourceLayout.prepare source)) (roots : List Ty) :
    CompilerOrigins resolves valid sessions (prepare source roots).compiler := by
  unfold prepare
  dsimp only
  apply roots_origins resolves valid sessions policy roots
  exact ⟨initial,cache_origins_empty (Plan.Origin resolves valid),cache_origins_empty valid⟩

/-- Every successful prepared or uncached plan preserves typed enum origins,
    including nested fields, arrays and the exact omitted/live flag census. -/
theorem prepare_query_origin (resolves : TyId → Ty → Prop) (valid : Ty → Summary → Prop) (sessions : Session → Prop)
    (policy : QueryOriginPolicy resolves valid sessions) (source : Environment)
    (initial : sessions (SourceLayout.prepare source)) (roots : List Ty) (ty : Ty) (plan : Plan)
    (run : (prepare source roots).query ty = .ok plan) : Plan.Origin resolves valid ty plan := by
  have safe := prepare_compiler_origins resolves valid sessions policy source initial roots
  have staticRun : (prepare source roots).queryStatic ty = .ok plan :=
    semanticResult_ok _ plan run
  unfold Service.queryStatic at staticRun
  cases cached : (prepare source roots).compiler.cache.findType ty with
  | some result =>
    rw [cached] at staticRun
    have origin := cache_origins_find (Plan.Origin resolves valid) _ safe.2.1 ty result cached
    dsimp only at staticRun
    rw [staticRun] at origin
    exact origin
  | none =>
    rw [cached] at staticRun
    have origin := (runCompile_origins resolves valid sessions policy _ ty safe).1
    dsimp only at staticRun
    rw [staticRun] at origin
    exact origin

theorem Service.queryWithWork_result (service : Service) (ty : Ty) :
    (service.queryWithWork ty).1 = service.query ty := by
  unfold Service.queryWithWork Service.query Service.queryStatic
  split <;> rfl

theorem Plan.Origin.enum_view {resolves : TyId → Ty → Prop} {valid : Ty → Summary → Prop} {id : EnumId} {plan : Plan}
    (origin : Plan.Origin resolves valid (.Enum id) plan) :
    ∃ layout info variants value, plan = .enumeration (.Enum id) layout info variants ∧
      valid (.Enum id) value ∧ value.enumeration = some info ∧ VariantOrigins resolves valid info.uninhabited variants := by
  cases origin with
  | leaf ty layout kind value summary extent => exact False.elim kind
  | fields ty layout fields kind children value summary extent bindings metadata sizes => exact False.elim kind
  | enumeration id layout info variants value summary present extent children bindings sizes =>
    exact ⟨layout,info,variants,value,rfl,summary,present,children⟩

theorem VariantOrigins.live_at {resolves : TyId → Ty → Prop} {valid : Ty → Summary → Prop} {dead : List Bool}
    {variants : List (Option (List (Nat × Plan)))} (origin : VariantOrigins resolves valid dead variants)
    (position : Nat) (live : (trustIrListGet? dead position) = some false) :
    ∃ fields, (trustIrListGet? variants position) = some (some fields) ∧
      ∀ field ∈ fields, Plan.Origin resolves valid field.2.ty field.2 := by
  induction position generalizing dead variants with
  | zero =>
    cases origin with
    | nil => cases live
    | omitted rest => cases live
    | @live dead variants fields children rest => exact ⟨fields,rfl,children⟩
  | succ position ih =>
    cases origin with
    | nil => cases live
    | omitted rest => exact ih rest live
    | live children rest => exact ih rest live

theorem VariantOrigins.absent_iff {resolves : TyId → Ty → Prop} {valid : Ty → Summary → Prop} {dead : List Bool}
    {variants : List (Option (List (Nat × Plan)))} (origin : VariantOrigins resolves valid dead variants)
    (position : Nat) : (trustIrListGet? variants position) = some none ↔ (trustIrListGet? dead position) = some true := by
  induction position generalizing dead variants with
  | zero => cases origin <;> simp
  | succ position ih =>
    cases origin with
    | nil => simp
    | omitted rest => exact ih rest
    | live children rest => exact ih rest

theorem VariantOrigins.length {resolves : TyId → Ty → Prop} {valid : Ty → Summary → Prop} {dead : List Bool}
    {variants : List (Option (List (Nat × Plan)))} (origin : VariantOrigins resolves valid dead variants) :
    variants.length = dead.length := by
  induction dead generalizing variants with
  | nil => cases origin; rfl
  | cons flag rest ih =>
    cases origin with
    | omitted later => exact congrArg Nat.succ (ih later)
    | live children later => exact congrArg Nat.succ (ih later)

/-- The actual queried enum summary also owns the plan's extent and alignment. -/
theorem Plan.Origin.enum_layout_view {resolves : TyId → Ty → Prop} {valid : Ty → Summary → Prop} {id : EnumId} {plan : Plan}
    (origin : Plan.Origin resolves valid (.Enum id) plan) :
    ∃ layout info variants value, plan = .enumeration (.Enum id) layout info variants ∧
      valid (.Enum id) value ∧ value.enumeration = some info ∧
      (layout.size = value.size ∧ value.align = some layout.alignment) ∧
      VariantOrigins resolves valid info.uninhabited variants := by
  cases origin with
  | leaf ty layout kind value summary extent => exact False.elim kind
  | fields ty layout fields kind children value summary extent bindings metadata sizes => exact False.elim kind
  | enumeration id layout info variants value summary present extent children bindings sizes =>
    exact ⟨layout,info,variants,value,rfl,summary,present,extent,children⟩

/-- Every retained plan size/alignment comes from its actual typed query. -/
theorem Plan.Origin.layout_view {resolves : TyId → Ty → Prop} {valid : Ty → Summary → Prop} {ty : Ty} {plan : Plan}
    (origin : Plan.Origin resolves valid ty plan) :
    ∃ value, valid ty value ∧ plan.layout.size = value.size ∧ value.align = some plan.layout.alignment := by
  cases origin <;> exact ⟨_,by assumption,(by assumption : _ ∧ _).1,(by assumption : _ ∧ _).2⟩

theorem FieldBindings.length {types : List Ty} {offsets : List Nat} {fields : List (Nat × Plan)}
    (bindings : FieldBindings types offsets fields) : fields.length = types.length ∧ fields.length = offsets.length := by
  have typesLength := congrArg List.length bindings.1
  have offsetsLength := congrArg List.length bindings.2
  simpa only [List.length_map] using And.intro typesLength offsetsLength

theorem FieldBindings.at {types : List Ty} {offsets : List Nat} {fields : List (Nat × Plan)}
    (bindings : FieldBindings types offsets fields) (position : Nat) (offset : Nat) (child : Plan)
    (found : (trustIrListGet? fields position) = some (offset,child)) :
    (trustIrListGet? types position) = some child.ty ∧ (trustIrListGet? offsets position) = some offset := by
  rw [← bindings.1,← bindings.2]
  simp [trustIrListGetMap,found]

theorem FieldBindings.source_at {expected : List Field} {fields : List (Nat × Plan)}
    (bindings : FieldBindings (expected.map (·.ty)) (expected.map (·.offset)) fields)
    (position : Nat) (sourceField : Field) (offset : Nat) (child : Plan)
    (sourceRow : (trustIrListGet? expected position) = some sourceField)
    (found : (trustIrListGet? fields position) = some (offset,child)) :
    child.ty = sourceField.ty ∧ offset = sourceField.offset := by
  have tied := bindings.at position offset child found
  simp only [trustIrListGetMap,sourceRow,Option.map,Option.some.injEq] at tied
  exact ⟨tied.1.symm,tied.2.symm⟩

theorem VariantBindings.fields_at {types : List (List Ty)} {offsets : List (List Nat)}
    {dead : List Bool} {variants : List (Option (List (Nat × Plan)))}
    (bindings : VariantBindings types offsets dead variants) (position : Nat) (fields : List (Nat × Plan))
    (found : (trustIrListGet? variants position) = some (some fields)) :
    ∃ firstTypes firstOffsets, (trustIrListGet? types position) = some firstTypes ∧ (trustIrListGet? offsets position) = some firstOffsets ∧
      FieldBindings firstTypes firstOffsets fields := by
  induction position generalizing types offsets dead variants with
  | zero =>
    cases bindings with
    | nil => cases found
    | omitted firstTypes firstOffsets rest => cases found
    | live first rest =>
      simp only [trustIrListGetConsZero,Option.some.injEq] at found
      cases found
      exact ⟨_,_,rfl,rfl,first⟩
  | succ position ih =>
    cases bindings with
    | nil => cases found
    | omitted firstTypes firstOffsets rest => exact ih rest found
    | live first rest => exact ih rest found

/-- The actual enum plan retains exact live-row types and physical offsets. -/
theorem Plan.Origin.enum_binding_view {resolves : TyId → Ty → Prop} {valid : Ty → Summary → Prop} {id : EnumId} {plan : Plan}
    (origin : Plan.Origin resolves valid (.Enum id) plan) :
    ∃ layout info variants value, plan = .enumeration (.Enum id) layout info variants ∧
      valid (.Enum id) value ∧ value.enumeration = some info ∧
      (layout.size = value.size ∧ value.align = some layout.alignment) ∧
      VariantOrigins resolves valid info.uninhabited variants ∧
      VariantBindings (info.variants.map (fun fields => fields.map (·.ty)))
        (info.variants.map (fun fields => fields.map (·.offset))) info.uninhabited variants := by
  cases origin with
  | leaf ty layout kind value summary extent => exact False.elim kind
  | fields ty layout fields kind children value summary extent bindings metadata sizes => exact False.elim kind
  | enumeration id layout info variants value summary present extent children bindings sizes =>
    exact ⟨layout,info,variants,value,rfl,summary,present,extent,children,bindings⟩

theorem FieldBindings.source_child {expected : List Field} {fields : List (Nat × Plan)}
    (bindings : FieldBindings (expected.map (·.ty)) (expected.map (·.offset)) fields)
    (position : Nat) (offset : Nat) (child : Plan)
    (found : (trustIrListGet? fields position) = some (offset,child)) :
    ∃ sourceField, (trustIrListGet? expected position) = some sourceField ∧
      child.ty = sourceField.ty ∧ offset = sourceField.offset := by
  have tied := bindings.at position offset child found
  cases sourceRow : (trustIrListGet? expected position) with
  | none => simp [trustIrListGetMap,sourceRow] at tied
  | some sourceField =>
    exact ⟨sourceField,rfl,bindings.source_at position sourceField offset child sourceRow found⟩

theorem VariantBindings.source_at {expected : List (List Field)}
    {dead : List Bool} {variants : List (Option (List (Nat × Plan)))}
    (bindings : VariantBindings (expected.map (fun fields => fields.map (·.ty)))
      (expected.map (fun fields => fields.map (·.offset))) dead variants)
    (position : Nat) (fields : List (Nat × Plan))
    (found : (trustIrListGet? variants position) = some (some fields)) :
    ∃ sourceFields, (trustIrListGet? expected position) = some sourceFields ∧
      FieldBindings (sourceFields.map (·.ty)) (sourceFields.map (·.offset)) fields := by
  obtain ⟨types,offsets,typesRow,offsetsRow,fieldBindings⟩ := bindings.fields_at position fields found
  cases sourceRow : (trustIrListGet? expected position) with
  | none => simp [trustIrListGetMap,sourceRow] at typesRow
  | some sourceFields =>
    simp only [trustIrListGetMap,sourceRow,Option.map,Option.some.injEq] at typesRow offsetsRow
    subst types
    subst offsets
    exact ⟨sourceFields,rfl,fieldBindings⟩

theorem VariantOrigins.children_at {resolves : TyId → Ty → Prop} {valid : Ty → Summary → Prop} {dead : List Bool}
    {variants : List (Option (List (Nat × Plan)))} (origin : VariantOrigins resolves valid dead variants)
    (position : Nat) (fields : List (Nat × Plan)) (found : (trustIrListGet? variants position) = some (some fields)) :
    ∀ field ∈ fields, Plan.Origin resolves valid field.2.ty field.2 := by
  induction position generalizing dead variants with
  | zero =>
    cases origin with
    | nil => cases found
    | omitted rest => cases found
    | live children rest =>
      simp only [trustIrListGetConsZero,Option.some.injEq] at found
      cases found
      exact children
  | succ position ih =>
    cases origin with
    | nil => cases found
    | omitted rest => exact ih rest found
    | live children rest => exact ih rest found

theorem FieldExtents.at {metadata : List Field} {fields : List (Nat × Plan)}
    (extents : FieldExtents metadata fields) (position : Nat) (sourceField : Field)
    (offset : Nat) (child : Plan) (sourceRow : (trustIrListGet? metadata position) = some sourceField)
    (found : (trustIrListGet? fields position) = some (offset,child)) : child.layout.size = sourceField.size := by
  have same := congrArg (fun rows => (trustIrListGet? rows position)) extents
  simpa only [trustIrListGetMap,sourceRow,found,Option.map,Option.some.injEq] using same

/-- Successful enum compilation retains checked child byte extents for every live row. -/
theorem Plan.Origin.enum_extent_view {resolves : TyId → Ty → Prop} {valid : Ty → Summary → Prop} {id : EnumId} {plan : Plan}
    (origin : Plan.Origin resolves valid (.Enum id) plan) :
    ∃ layout info variants value, plan = .enumeration (.Enum id) layout info variants ∧
      valid (.Enum id) value ∧ value.enumeration = some info ∧
      (layout.size = value.size ∧ value.align = some layout.alignment) ∧
      VariantOrigins resolves valid info.uninhabited variants ∧
      VariantBindings (info.variants.map (fun fields => fields.map (·.ty)))
        (info.variants.map (fun fields => fields.map (·.offset))) info.uninhabited variants ∧
      VariantExtents info.variants variants := by
  cases origin with
  | leaf ty layout kind value summary extent => exact False.elim kind
  | fields ty layout fields kind children value summary extent bindings metadata sizes => exact False.elim kind
  | enumeration id layout info variants value summary present extent children bindings sizes =>
    exact ⟨layout,info,variants,value,rfl,summary,present,extent,children,bindings,sizes⟩

end TrustIr.AggregateMemory
