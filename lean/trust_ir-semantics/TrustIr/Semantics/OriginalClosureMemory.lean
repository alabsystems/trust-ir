-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.DecodedClosureStorage
import TrustIr.Semantics.AggregateAccess

namespace TrustIr.OriginalClosureMemory

/-- The module and capture memory service have one original source. No public
constructor accepts a selected binding, callback or independently prepared
service. Geometry alone remains insufficient to obtain a closure target. -/
structure Service where
  private mk ::
  private source : TrustIrEval.Module
  private model : ByteModel
  private roots : List Ty
  private memory : AggregateMemory.Service
  private memoryOrigin : memory.sourceEnvironment = TrustIrEval.layoutSourceOf source model

def prepare (source : TrustIrEval.Module) (model : ByteModel) (roots : List Ty) : Service :=
  ⟨source, model, roots, AggregateMemory.prepare (TrustIrEval.layoutSourceOf source model) roots,
    AggregateMemory.prepare_sourceEnvironment _ _⟩

/-- Ordinary memory and capture memory share the same authentic preparer. -/
def Service.memoryService (service : Service) : AggregateMemory.Service := service.memory

/-- The source/capture-compiler relation is an actual retained equality, not
an unenforced convention about a private constructor. -/
theorem Service.original_source (service : Service) :
    ∃ source model, service.memoryService.sourceEnvironment =
      TrustIrEval.layoutSourceOf source model :=
  ⟨service.source, service.model, service.memoryOrigin⟩

theorem prepared_memory (source : TrustIrEval.Module) (model : ByteModel) (roots : List Ty) :
    (prepare source model roots).memoryService =
      AggregateMemory.prepare (TrustIrEval.layoutSourceOf source model) roots := rfl

private def binding (service : Service) (model : ByteModel) (closure : ClosureTyId) :
    Except SemError (TrustIrEval.ClosureStorage.Binding service.source closure) := do
  if model != service.model then
    throw (.typeError "memory: original closure source target does not match evaluator target")
  let held ← match TrustIrEval.ClosureStorage.bindingOf service.source closure with
    | .ok held => pure held
    | .error (.malformed message) => throw (.typeError message)
    | .error (.unsupported feature) => throw (.unsupported .layout feature)
  if held.model != service.model then
    throw (.typeError "memory: original closure source target does not match evaluator target")
  pure held

private def layout (shape : SourceLayout.Summary) : Except SemError MemoryTypeLayout :=
  match shape.align with
  | none => .error (.unsupported .layout "closure storage has no byte alignment")
  | some alignment => .ok ⟨shape.size, alignment⟩

/-- Obtain every child from the same authentic memory compiler, retaining exact
source types, offsets and shape extents. Unsupported children remain refusals;
no aggregate Plan is manufactured by this adapter. -/
def capturePlans (service : Service) (extent : Nat) :
    List Ty → List Nat → List SourceLayout.Field → Except SemError (List (Nat × AggregateMemory.Plan))
  | [], [], [] => pure []
  | ty :: types, offset :: offsets, field :: fields => do
    if !closureTyEq field.ty ty || field.offset != offset || offset + field.size > extent then
      throw (.typeError "closure storage capture metadata mismatch")
    let child ← service.memory.query ty
    if !closureTyEq child.ty ty || child.layout.size != field.size || child.layout.alignment != field.align then
      throw (.typeError "closure storage capture codec layout mismatch")
    let later ← capturePlans service extent types offsets fields
    pure ((offset, child) :: later)
  | _, _, _ => throw (.typeError "closure storage capture census mismatch")

/-- Actual successful binding checks retain both the evaluator model and the
existing whole-module binding query. No source lookup is reconstructed. -/
theorem binding_facts (service : Service) (model : ByteModel) (closure : ClosureTyId)
    (held : TrustIrEval.ClosureStorage.Binding service.source closure)
    (run : binding service model closure = .ok held) :
    held.model = model ∧ TrustIrEval.ClosureStorage.bindingOf service.source closure = .ok held := by
  unfold binding at run
  by_cases mismatch : (model != service.model) = true
  · simp only [mismatch,ite_true,Bind.bind,Except.bind,Pure.pure,Except.pure,pure_bind] at run
    all_goals cases run
  · simp only [mismatch,ite_false,Bind.bind,Except.bind,Pure.pure,Except.pure,pure_bind] at run
    have callerModel : model = service.model := by
      cases model <;> cases selected : service.model
      all_goals first | rfl | exact False.elim (mismatch (by rw [selected]; rfl))
    cases queried : TrustIrEval.ClosureStorage.bindingOf service.source closure with
    | error error =>
      cases error <;> simp only [queried,Bind.bind,Except.bind,Pure.pure,Except.pure,pure_bind] at run
      all_goals cases run
    | ok actual =>
      simp only [queried,Bind.bind,Except.bind,Pure.pure,Except.pure,pure_bind] at run
      by_cases targetMismatch : (actual.model != service.model) = true
      · simp only [targetMismatch,ite_true,Bind.bind,Except.bind,Pure.pure,Except.pure,pure_bind] at run
        all_goals cases run
      · simp only [targetMismatch,ite_false,Bind.bind,Except.bind,Pure.pure,Except.pure,pure_bind] at run
        have actualModel : actual.model = service.model := by
          cases observed : actual.model <;> cases selected : service.model
          all_goals first | rfl | exact False.elim (targetMismatch (by rw [observed,selected]; rfl))
        have same : actual = held := Except.ok.inj run
        cases same
        exact ⟨actualModel.trans callerModel.symm,rfl⟩

/-- The existing exact original-module query and target model are sufficient
for the actual preparer's checked binding; errors are never erased. -/
theorem prepared_binding (source : TrustIrEval.Module) (model : ByteModel) (roots : List Ty)
    (closure : ClosureTyId) (held : TrustIrEval.ClosureStorage.Binding source closure)
    (queried : TrustIrEval.ClosureStorage.bindingOf source closure = .ok held)
    (selected : held.model = model) : binding (prepare source model roots) model closure = .ok held := by
  unfold binding
  dsimp only [prepare]
  rw [queried]
  simp only [Bind.bind,Except.bind,Pure.pure,Except.pure,pure_bind,selected]
  cases model <;> rfl

/-- Reconstruct only the actual shape-to-layout projection. This supplies no
codec, code identity, pointer or execution authority. -/
theorem layout_of_fields (shape : SourceLayout.Summary) (storage : MemoryTypeLayout)
    (size : storage.size = shape.size) (alignment : shape.align = some storage.alignment) :
    layout shape = .ok storage := by
  unfold layout
  rw [alignment]
  cases storage with
  | mk count align => simp only at size; cases size; rfl

/-- The actual capture query retains source field order, extents, and each
successful child query. This proof interface creates no parent Plan or target. -/
theorem capturePlans_facts (service : Service) (extent : Nat) (types : List Ty)
    (offsets : List Nat) (metadata : List SourceLayout.Field)
    (fields : List (Nat × AggregateMemory.Plan))
    (run : capturePlans service extent types offsets metadata = .ok fields) :
    AggregateMemory.FieldBindings (metadata.map (·.ty)) (metadata.map (·.offset)) fields ∧
    AggregateMemory.FieldExtents metadata fields ∧ fields.length = types.length ∧
    AggregateMemory.FieldBindings types offsets fields ∧
    ∀ offset child, (offset,child) ∈ fields →
      service.memoryService.query child.ty = .ok child ∧ offset + child.layout.size ≤ extent := by
  induction types generalizing offsets metadata fields with
  | nil =>
    cases offsets with
    | nil =>
      cases metadata with
      | nil =>
        simp only [capturePlans] at run
        cases run
        exact ⟨⟨rfl,rfl⟩,rfl,rfl,⟨rfl,rfl⟩,by intro offset child member; cases member⟩
      | cons field metadata => simp [capturePlans] at run
    | cons offset offsets => cases metadata <;> simp [capturePlans] at run
  | cons ty types ih =>
    cases offsets with
    | nil => cases metadata <;> simp [capturePlans] at run
    | cons offset offsets =>
      cases metadata with
      | nil => simp [capturePlans] at run
      | cons field metadata =>
        rw [capturePlans] at run
        split at run
        · cases run
        · rename_i bad
          simp only [Bind.bind,Except.bind,Pure.pure,Except.pure,pure_bind] at run
          cases queried : service.memory.query ty with
          | error error =>
            simp only [queried,Bind.bind,Except.bind] at run
            all_goals cases run
          | ok child =>
            simp only [queried,Bind.bind,Except.bind,Pure.pure,Except.pure,pure_bind] at run
            split at run
            · cases run
            · rename_i childBad
              try simp only [Bind.bind,Except.bind,Pure.pure,Except.pure,pure_bind] at run
              cases laterRun : capturePlans service extent types offsets metadata with
              | error error =>
                simp only [laterRun,Bind.bind,Except.bind] at run
                all_goals cases run
              | ok later =>
                simp only [laterRun,Bind.bind,Except.bind,Pure.pure,Except.pure,pure_bind] at run
                cases run
                have fieldTyped : field.ty = ty := closureTyEq_sound _ _ (by
                  cases checked : closureTyEq field.ty ty <;> simp_all)
                have childTyped : child.ty = ty := closureTyEq_sound _ _ (by
                  cases checked : closureTyEq child.ty ty <;> simp_all)
                have placed : field.offset = offset := by
                  by_cases same : field.offset = offset
                  · exact same
                  · exact False.elim (bad (by simp [same]))
                have sized : child.layout.size = field.size := by
                  by_cases same : child.layout.size = field.size
                  · exact same
                  · exact False.elim (childBad (by simp [same]))
                have bounded : offset + child.layout.size ≤ extent := by
                  by_cases fits : offset + field.size ≤ extent
                  · omega
                  · have tooLarge : offset + field.size > extent := by omega
                    exact False.elim (bad (by simp [tooLarge]))
                obtain ⟨bindings,extents,census,inputs,queries⟩ := ih offsets metadata later laterRun
                refine ⟨⟨?_,?_⟩,?_,?_,⟨?_,?_⟩,?_⟩
                · change child.ty :: later.map (fun row => row.2.ty) = field.ty :: metadata.map (·.ty)
                  rw [childTyped,fieldTyped,bindings.1]
                · change offset :: later.map (·.1) = field.offset :: metadata.map (·.offset)
                  rw [placed,bindings.2]
                · change child.layout.size :: later.map (fun row => row.2.layout.size) = field.size :: metadata.map (·.size)
                  rw [sized,extents]
                · exact congrArg Nat.succ census
                · change child.ty :: later.map (fun row => row.2.ty) = ty :: types
                  rw [childTyped,inputs.1]
                · change offset :: later.map (·.1) = offset :: offsets
                  rw [inputs.2]
                · intro actualOffset actualChild member
                  rcases List.mem_cons.mp member with same | tail
                  · cases same
                    refine ⟨?_,bounded⟩
                    simpa only [Service.memoryService,childTyped] using queried
                  · exact queries actualOffset actualChild tail

/-- Source/decode refusals cannot inject a caller-provided unwind state. -/
theorem binding_errors (error : SemError → Prop)
    (typeErrors : ∀ message, error (.typeError message))
    (unsupported : ∀ message, error (.unsupported .layout message))
    (service : Service) (model : ByteModel) (closure : ClosureTyId) :
    ByteImage.BlockResult (fun _ => True) error (binding service model closure) := by
  unfold binding
  repeat' first
    | exact True.intro
    | exact typeErrors _
    | exact unsupported _
    | (simp only [pure_bind])
    | split
    | (dsimp only; split)

theorem layout_errors (error : SemError → Prop)
    (unsupported : ∀ message, error (.unsupported .layout message)) (shape : SourceLayout.Summary) :
    ByteImage.BlockResult (fun _ => True) error (layout shape) := by
  unfold layout
  cases shape.align <;> first | exact True.intro | exact unsupported _

theorem capturePlans_errors (error : SemError → Prop)
    (typeErrors : ∀ message, error (.typeError message))
    (unsupported : ∀ message, error (.unsupported .layout message))
    (service : Service) (extent : Nat) (types : List Ty) (offsets : List Nat)
    (fields : List SourceLayout.Field) :
    ByteImage.BlockResult (fun _ => True) error (capturePlans service extent types offsets fields) := by
  cases types <;> cases offsets <;> cases fields <;> rw [capturePlans]
  all_goals repeat' first
    | exact True.intro
    | exact typeErrors _
    | (simp only [pure_bind])
    | (refine ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _
        ((AggregateMemory.Service.error_policy error typeErrors unsupported service.memory _).1) ?_; intro child _)
    | (refine ByteImage.BlockResult.bind (fun _ => True) (fun _ => True) error _ _
        (capturePlans_errors error typeErrors unsupported service extent _ _ _) ?_; intro _later _)
    | split
    | (dsimp only; split)
  all_goals simp_all
  termination_by types.length

/-- Direct nominal load mirrors the reference interpreter's capture-only image:
the exact original binding supplies code identity, authentic child codecs read
captures, and whole-parent access checks remain mandatory even for zero bytes. -/
def loadValue (service : Service) (order : FunctionAddressOrder) (closure : ClosureTyId)
    (pointer : Value) (_strict : Bool := false) (align : Option Nat := none)
    (model : ByteModel := .le64) : Sem Value := do
  let held ← Sem.fromMemoryExcept (binding service model closure)
  let storage ← Sem.fromMemoryExcept (layout held.shape)
  let fields ← Sem.fromMemoryExcept (capturePlans service storage.size
    held.nominal.captures held.descriptor.captureOffsets held.shape.fields)
  let alignment ← Sem.fromMemoryExcept (checkedMemoryAlign "Load" storage.alignment align)
  Sem.rejectPartial pointer "Load"
  let (address, allocation) ← Sem.expectPointer "Load" pointer
  let address ← Sem.checkedAccess "Load" address allocation storage.size alignment model
  let state ← Sem.getState
  let image := state.memory.readImage address storage.size
  let missing ← Sem.fromMemoryExcept (AggregateMemory.coveredCaptureImage fields image)
  if missing.isSome then Sem.throwUB "Load: reading uninitialized covered memory"
  let captures ← Sem.fromMemoryExcept (AggregateMemory.decodeCaptureImage model order state.memory fields image)
  pure (.typedClosure closure held.target.value captures)

def load (service : Service) (order : FunctionAddressOrder) (closure : ClosureTyId)
    (pointer : ValueId) (strict : Bool := false) (align : Option Nat := none)
    (model : ByteModel := .le64) : Sem ValueId := do
  let pointer ← Sem.lookupValue pointer
  let value ← loadValue service order closure pointer strict align model
  Sem.bindFresh value

/-- Store checks the actual nominal/code identity and capture count, then
writes the whole declared footprint through the existing canonical field
encoder. Padding remains unwritten; no private image compiler is introduced. -/
def storeValue (service : Service) (order : FunctionAddressOrder) (closure : ClosureTyId)
    (pointer value : Value) (strict : Bool := false) (align : Option Nat := none)
    (model : ByteModel := .le64) : Sem Unit := do
  if strict && (value.isPoison || AggregateMemory.carriesUnwritten value) then
    Sem.throwUB "Store: strict store of poison or unwritten aggregate lane"
  let held ← Sem.fromMemoryExcept (binding service model closure)
  let storage ← Sem.fromMemoryExcept (layout held.shape)
  let fields ← Sem.fromMemoryExcept (capturePlans service storage.size
    held.nominal.captures held.descriptor.captureOffsets held.shape.fields)
  let alignment ← Sem.fromMemoryExcept (checkedMemoryAlign "Store" storage.alignment align)
  Sem.rejectPartial pointer "Store"
  let (address, allocation) ← Sem.expectPointer "Store" pointer
  let address ← Sem.checkedAccess "Store" address allocation storage.size alignment model
  let image ← match value with
    | .typedClosure nominal target captures =>
      if nominal != closure || target != held.target.value || captures.length != held.nominal.captures.length then
        Sem.throwTypeError "closure Store nominal, target or capture count mismatch"
      Sem.fromMemoryExcept (AggregateMemory.encodeCaptureImage model order storage.size fields captures)
    | .undef ty =>
      if !closureTyEq ty (.Closure closure) then
        Sem.throwTypeError "Store: poison source type does not match store type"
      pure ({ bytes := ByteImage.fill storage.size none } : AggregateMemory.Image)
    | _ => Sem.throwTypeError "closure Store requires a nominal closure value"
  if image.bytes.size != storage.size then
    Sem.throwTypeError "Store: image byte count does not match source layout"
  Sem.modifyState fun state =>
    let memory := state.memory.writeImage address image.bytes
    { state with memory := memory.recordUnwritten allocation address image.unwritten }

def store (service : Service) (order : FunctionAddressOrder) (closure : ClosureTyId)
    (pointer value : ValueId) (strict : Bool := false) (align : Option Nat := none)
    (model : ByteModel := .le64) : Sem Unit := do
  let pointer ← Sem.lookupValue pointer
  let value ← Sem.lookupValue value
  storeValue service order closure pointer value strict align model

end TrustIr.OriginalClosureMemory
