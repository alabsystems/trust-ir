-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.LoadInstructionExecution

namespace TrustIr.AggregateMemory

/-- The actual allocation-specific unwritten explanation fold. This does not
    change memory: it supplies only the coverage check's temporary image. -/
def explainedLoadImage (memory : Memory) (allocation : AllocId) (address : Nat) (image : ByteImage) : ByteImage :=
  memory.unwritten.foldl (fun current lane =>
    if lane.allocation == allocation then
      let start := max address lane.start
      let stop := min (address + image.size) lane.stop
      if start < stop then
        let offset := start - address
        (current.slice 0 offset).append ((ByteImage.fill (stop - start) (some 0)).append
          (current.slice (stop - address) (image.size - (stop - address))))
      else current
    else current) image

/-- Pure result selected by the original descriptor Load after access checks.
    The decoder always sees the original image, even after unwritten coverage
    is explained with a temporary zero-filled image. -/
def loadImageResult (model : ByteModel) (order : FunctionAddressOrder) (ty : Ty) (strict : Bool)
    (memory : Memory) (allocation : AllocId) (address : Nat) (plan : Plan) (image : ByteImage) : Except SemError Value :=
  if (firstMissing image).isNone then decode model order memory plan image
  else if !strict && isPartialLoadTyFor model ty then .ok (.partial image.toList)
  else do
    match ← covered plan image with
    | none => decode model order memory plan image
    | some _ =>
      match plan with
      | .fields _ _ _ => do
        match ← covered plan (explainedLoadImage memory allocation address image) with
        | none => decodeUnwritten model order memory plan image
        | some _ => .error (.ub "Load: reading uninitialized covered memory")
      | _ => .error (.ub "Load: reading uninitialized covered memory")

private def loadPlanResult (service : Service) (model : ByteModel) (ty : Ty) : Except SemError Plan :=
  if model == service.model then service.query ty
  else .error (.typeError "memory: source layout target does not match evaluator target")

private theorem except_bind_action {α β : Type} (first : Except SemError α) (next : α → Except SemError β) :
    Sem.fromMemoryExcept (first >>= next) = (Sem.fromMemoryExcept first >>= fun value => Sem.fromMemoryExcept (next value)) := by
  cases first <;> rfl

private def imageAction (model : ByteModel) (order : FunctionAddressOrder) (ty : Ty) (strict : Bool)
    (memory : Memory) (allocation : AllocId) (address : Nat) (plan : Plan) (image : ByteImage) : Sem Value := do
  if (firstMissing image).isNone then Sem.fromMemoryExcept (decode model order memory plan image)
  else if !strict && isPartialLoadTyFor model ty then pure (.partial image.toList)
  else
    match ← Sem.fromMemoryExcept (covered plan image) with
    | none => Sem.fromMemoryExcept (decode model order memory plan image)
    | some _ =>
      match plan with
      | .fields _ _ _ =>
        match ← Sem.fromMemoryExcept (covered plan (explainedLoadImage memory allocation address image)) with
        | none => Sem.fromMemoryExcept (decodeUnwritten model order memory plan image)
        | some _ => Sem.throwUB "Load: reading uninitialized covered memory"
      | _ => Sem.throwUB "Load: reading uninitialized covered memory"

private theorem imageAction_result (model : ByteModel) (order : FunctionAddressOrder) (ty : Ty) (strict : Bool)
    (memory : Memory) (allocation : AllocId) (address : Nat) (plan : Plan) (image : ByteImage) :
    imageAction model order ty strict memory allocation address plan image =
      Sem.fromMemoryExcept (loadImageResult model order ty strict memory allocation address plan image) := by
  unfold imageAction loadImageResult
  split
  · rfl
  · split
    · rfl
    · rw [except_bind_action]
      congr 1
      funext missing
      cases missing with
      | none => rfl
      | some index =>
        cases plan <;> try rfl
        dsimp only
        rw [except_bind_action]
        congr 1
        funext missing
        cases missing <;> rfl

/-- Exact operational connection to the original implementation; no alternate
    decoder is assumed or installed. All error and initialization branches stay. -/
theorem loadValue_image_action (service : Service) (order : FunctionAddressOrder) (ty : Ty) (pointer : Value)
    (strict : Bool) (align : Option Nat) (model : ByteModel) :
    loadValue service order ty pointer strict align model = (do
      let plan ← Sem.fromMemoryExcept (loadPlanResult service model ty)
      let alignment ← Sem.fromMemoryExcept (checkedMemoryAlign "Load" plan.layout.alignment align)
      Sem.rejectPartial pointer "Load"
      let pair ← Sem.expectPointer "Load" pointer
      let address ← Sem.checkedAccess "Load" pair.1 pair.2 plan.layout.size alignment model
      let state ← Sem.getState
      Sem.fromMemoryExcept (loadImageResult model order ty strict state.memory pair.2 address plan
        (state.memory.readImage address plan.layout.size))) := by
  have original : loadValue service order ty pointer strict align model = (do
      let plan ← Sem.fromMemoryExcept (loadPlanResult service model ty)
      let alignment ← Sem.fromMemoryExcept (checkedMemoryAlign "Load" plan.layout.alignment align)
      Sem.rejectPartial pointer "Load"
      let pair ← Sem.expectPointer "Load" pointer
      let address ← Sem.checkedAccess "Load" pair.1 pair.2 plan.layout.size alignment model
      let state ← Sem.getState
      imageAction model order ty strict state.memory pair.2 address plan
        (state.memory.readImage address plan.layout.size)) := rfl
  rw [original]
  simp only [imageAction_result]

private theorem run_bind_success {α β : Type} (first : Sem α) (next : α → Sem β)
    (before after : MachineState) (result : β)
    (run : Sem.run (first >>= next) before = .ok (result,after)) :
    ∃ value middle, Sem.run first before = .ok (value,middle) ∧
      Sem.run (next value) middle = .ok (result,after) := by
  trustIrCompilerProof {
    rw [Sem.run_bind] at run
    cases accepted : Sem.run first before with
    | error error => simp only [accepted,Except.bind] at run
    | ok pair =>
      obtain ⟨value,middle⟩ := pair
      simp only [accepted,Except.bind] at run
      exact ⟨value,middle,rfl,run⟩
  } {
    rw [Sem.run_bind] at run
    cases accepted : Sem.run first before with
    | error error => simp only [accepted,Except.bind] at run; cases run
    | ok pair =>
      obtain ⟨value,middle⟩ := pair
      simp only [accepted,Except.bind] at run
      exact ⟨value,middle,rfl,run⟩
  }

private theorem except_bind_success {α β : Type} (first : Except SemError α) (next : α → Sem β)
    (before after : MachineState) (result : β)
    (run : Sem.run (Sem.fromMemoryExcept first >>= next) before = .ok (result,after)) :
    ∃ value, first = .ok value ∧ Sem.run (next value) before = .ok (result,after) := by
  cases first with
  | error error => cases run
  | ok value => exact ⟨value,rfl,run⟩

private theorem except_action_success {α : Type} (first : Except SemError α)
    (before after : MachineState) (value : α)
    (run : Sem.run (Sem.fromMemoryExcept first) before = .ok (value,after)) :
    first = .ok value ∧ after = before := by
  cases first with
  | error error => cases run
  | ok actual => cases run; exact ⟨rfl,rfl⟩

private theorem model_beq_sound (left right : ByteModel) (same : (left == right) = true) : left = right := by
  cases left <;> cases right <;> first | rfl | cases same

/-- Actual successful held Load derives its target, queried plan, instruction
    alignment, provenance pointer, checked access and selected image result.
    No assumed image, decoder result or intermediate state is supplied. -/
theorem loadValue_success_steps (service : Service) (order : FunctionAddressOrder) (ty : Ty)
    (pointer : Value) (strict : Bool) (align : Option Nat) (model : ByteModel)
    (before after : MachineState) (value : Value)
    (run : Sem.run (loadValue service order ty pointer strict align model) before = .ok (value,after)) :
    ∃ plan alignment address allocation,
      model = service.model ∧ service.query ty = .ok plan ∧
      checkedMemoryAlign "Load" plan.layout.alignment align = .ok alignment ∧
      pointer = .ptr address (some allocation) ∧
      Sem.run (Sem.checkedAccess "Load" address allocation plan.layout.size alignment model) before = .ok (address,before) ∧
      loadImageResult model order ty strict before.memory allocation address plan
        (before.memory.readImage address plan.layout.size) = .ok value ∧ after = before := by
  rw [loadValue_image_action] at run
  obtain ⟨plan,query,run⟩ := except_bind_success _ _ before after value run
  obtain ⟨target,query⟩ : model = service.model ∧ service.query ty = .ok plan := by
    unfold loadPlanResult at query
    split at query
    · rename_i same
      exact ⟨model_beq_sound model service.model same,query⟩
    · cases query
  obtain ⟨alignment,aligned,run⟩ := except_bind_success _ _ before after value run
  obtain ⟨unit,middle,inspected,run⟩ := run_bind_success _ _ before after value run
  have same := rejectPartial_ok_state "Load" pointer before middle unit inspected
  subst middle
  cases unit
  obtain ⟨pair,middle,pointerRun,run⟩ := run_bind_success _ _ before after value run
  obtain ⟨same,pointerShape⟩ := expectPointer_ok_inv "Load" pointer before middle pair pointerRun
  subst middle
  obtain ⟨address,allocation⟩ := pair
  obtain ⟨actual,middle,accessed,run⟩ := run_bind_success _ _ before after value run
  obtain ⟨same,addressSame⟩ : middle = before ∧ actual = address := by
    cases model with
    | le64 =>
      obtain ⟨same,addressSame,_⟩ := checkedAccess_ok_inv "Load" address allocation plan.layout.size alignment before middle actual accessed
      exact ⟨same,addressSame⟩
    | le32 =>
      obtain ⟨same,addressSame,_⟩ := checkedAccess32_names_live_provenance "Load" address allocation plan.layout.size alignment before middle actual accessed
      exact ⟨same,addressSame⟩
  subst middle
  subst actual
  change Sem.run (Sem.fromMemoryExcept (loadImageResult model order ty strict before.memory allocation address plan
    (before.memory.readImage address plan.layout.size))) before = .ok (value,after) at run
  obtain ⟨decoded,same⟩ := except_action_success _ before after value run
  exact ⟨plan,alignment,address,allocation,target,query,aligned,pointerShape,accessed,decoded,same⟩

/-- Exactly the four successful initialization paths. The unwritten path
    checks its explanation image but decodes the original image. -/
def LoadImageAccepted (model : ByteModel) (order : FunctionAddressOrder) (ty : Ty) (strict : Bool)
    (memory : Memory) (allocation : AllocId) (address : Nat) (plan : Plan) (image : ByteImage) (value : Value) : Prop :=
  ((firstMissing image).isNone = true ∧ decode model order memory plan image = .ok value) ∨
  ((firstMissing image).isNone = false ∧ (!strict && isPartialLoadTyFor model ty) = true ∧ value = .partial image.toList) ∨
  ((firstMissing image).isNone = false ∧ (!strict && isPartialLoadTyFor model ty) = false ∧
    covered plan image = .ok none ∧ decode model order memory plan image = .ok value) ∨
  ((firstMissing image).isNone = false ∧ (!strict && isPartialLoadTyFor model ty) = false ∧
    ∃ missing, covered plan image = .ok (some missing) ∧
      (∃ fieldTy layout fields, plan = .fields fieldTy layout fields) ∧
      covered plan (explainedLoadImage memory allocation address image) = .ok none ∧
      decodeUnwritten model order memory plan image = .ok value)

theorem loadImageResult_success_cases (model : ByteModel) (order : FunctionAddressOrder) (ty : Ty) (strict : Bool)
    (memory : Memory) (allocation : AllocId) (address : Nat) (plan : Plan) (image : ByteImage) (value : Value)
    (run : loadImageResult model order ty strict memory allocation address plan image = .ok value) :
    LoadImageAccepted model order ty strict memory allocation address plan image value := by
  unfold loadImageResult at run
  cases initialized : (firstMissing image).isNone with
  | true =>
    simp only [initialized,ite_true] at run
    exact Or.inl ⟨initialized,run⟩
  | false =>
    simp only [initialized,Bool.false_eq_true,ite_false] at run
    cases partialAllowed : !strict && isPartialLoadTyFor model ty with
    | true =>
      simp only [partialAllowed,ite_true] at run
      cases run
      exact Or.inr (Or.inl ⟨initialized,partialAllowed,rfl⟩)
    | false =>
      simp only [partialAllowed,Bool.false_eq_true,ite_false] at run
      cases coverage : covered plan image with
      | error error => simp only [coverage,Except.bind] at run; cases run
      | ok missing =>
        simp only [coverage,Except.bind] at run
        cases missing with
        | none => exact Or.inr (Or.inr (Or.inl ⟨initialized,partialAllowed,coverage,run⟩))
        | some index =>
          cases plan <;> try cases run
          case fields fieldTy layout fields =>
            dsimp only at run
            cases explained : covered (.fields fieldTy layout fields) (explainedLoadImage memory allocation address image) with
            | error error => simp only [explained,Except.bind] at run; cases run
            | ok missing =>
              simp only [explained,Except.bind] at run
              cases missing with
              | some index => cases run
              | none =>
                exact Or.inr (Or.inr (Or.inr ⟨initialized,partialAllowed,index,coverage,
                  ⟨fieldTy,layout,fields,rfl⟩,explained,run⟩))

theorem loadValue_success_image (service : Service) (order : FunctionAddressOrder) (ty : Ty)
    (pointer : Value) (strict : Bool) (align : Option Nat) (model : ByteModel)
    (before after : MachineState) (value : Value)
    (run : Sem.run (loadValue service order ty pointer strict align model) before = .ok (value,after)) :
    ∃ plan alignment address allocation,
      model = service.model ∧ service.query ty = .ok plan ∧
      checkedMemoryAlign "Load" plan.layout.alignment align = .ok alignment ∧
      pointer = .ptr address (some allocation) ∧
      Sem.run (Sem.checkedAccess "Load" address allocation plan.layout.size alignment model) before = .ok (address,before) ∧
      LoadImageAccepted model order ty strict before.memory allocation address plan
        (before.memory.readImage address plan.layout.size) value ∧ after = before := by
  obtain ⟨plan,alignment,address,allocation,target,query,aligned,pointerShape,accessed,decoded,same⟩ :=
    loadValue_success_steps service order ty pointer strict align model before after value run
  exact ⟨plan,alignment,address,allocation,target,query,aligned,pointerShape,accessed,
    loadImageResult_success_cases model order ty strict before.memory allocation address plan _ value decoded,same⟩

theorem loadImageAccepted_result (model : ByteModel) (order : FunctionAddressOrder) (ty : Ty) (strict : Bool)
    (memory : Memory) (allocation : AllocId) (address : Nat) (plan : Plan) (image : ByteImage) (value : Value)
    (accepted : LoadImageAccepted model order ty strict memory allocation address plan image value) :
    loadImageResult model order ty strict memory allocation address plan image = .ok value := by
  rcases accepted with complete | transported | padding | unwritten
  · obtain ⟨initialized,decoded⟩ := complete
    simpa only [loadImageResult,initialized,ite_true] using decoded
  · obtain ⟨initialized,allowed,rfl⟩ := transported
    simp only [loadImageResult,initialized,Bool.false_eq_true,ite_false,allowed,ite_true]
  · obtain ⟨initialized,allowed,coverage,decoded⟩ := padding
    simpa only [loadImageResult,initialized,Bool.false_eq_true,ite_false,allowed,coverage,Except.bind] using decoded
  · obtain ⟨initialized,allowed,missing,coverage,shape,explained,decoded⟩ := unwritten
    obtain ⟨fieldTy,layout,fields,rfl⟩ := shape
    simpa only [loadImageResult,initialized,Bool.false_eq_true,ite_false,allowed,coverage,Except.bind,explained] using decoded

theorem loadImageResult_success_iff (model : ByteModel) (order : FunctionAddressOrder) (ty : Ty) (strict : Bool)
    (memory : Memory) (allocation : AllocId) (address : Nat) (plan : Plan) (image : ByteImage) (value : Value) :
    loadImageResult model order ty strict memory allocation address plan image = .ok value ↔
      LoadImageAccepted model order ty strict memory allocation address plan image value :=
  ⟨loadImageResult_success_cases model order ty strict memory allocation address plan image value,
    loadImageAccepted_result model order ty strict memory allocation address plan image value⟩

/-- The actual held descriptor Load succeeds from its selected checks and
original-image result. No intermediate execution or state equality is assumed. -/
theorem loadValue_of_checks (service : Service) (order : FunctionAddressOrder) (ty : Ty)
    (strict : Bool) (align : Option Nat) (model : ByteModel) (before : MachineState)
    (plan : Plan) (alignment address : Nat) (allocation : AllocId) (value : Value)
    (target : model = service.model) (query : service.query ty = .ok plan)
    (aligned : checkedMemoryAlign "Load" plan.layout.alignment align = .ok alignment)
    (accessed : Sem.run (Sem.checkedAccess "Load" address allocation plan.layout.size alignment model)
      before = .ok (address,before))
    (decoded : loadImageResult model order ty strict before.memory allocation address plan
      (before.memory.readImage address plan.layout.size) = .ok value) :
    Sem.run (loadValue service order ty (.ptr address (some allocation)) strict align model)
      before = .ok (value,before) := by
  have same : (model == model) = true := by cases model <;> rfl
  rw [loadValue_image_action]
  simp only [loadPlanResult,← target,same,ite_true,query,Sem.fromMemoryExcept,
    pure_bind,aligned,Sem.rejectPartial,Sem.expectPointer]
  rw [Sem.run_bind,accessed]
  simp only [Except.bind]
  change Sem.run (Sem.fromMemoryExcept (loadImageResult model order ty strict before.memory allocation address plan
    (before.memory.readImage address plan.layout.size))) before = .ok (value,before)
  simp only [decoded,Sem.fromMemoryExcept,Sem.run_pure]

end TrustIr.AggregateMemory

namespace TrustIr

/-- The original descriptor Load node authenticates all image/check witnesses
    to its original SSA pointer, original memory and actual published value. -/
theorem stepLoad_descriptor_image (ctx : EvalContext) (ty : Ty) (pointer : ValueId)
    (strict : Bool) (align : Option Nat) (service : AggregateMemory.Service)
    (selected : ctx.memoryServiceFor ty = some service) (before after : MachineState) (result : InstrResult)
    (run : Sem.run (stepInstWithContext ctx (.Load ty pointer strict align)) before = .ok (result,after)) :
    ∃ heldPointer value plan alignment address allocation,
      before.lookupValue pointer = some heldPointer ∧
      ctx.byteModel = service.model ∧ service.query ty = .ok plan ∧
      checkedMemoryAlign "Load" plan.layout.alignment align = .ok alignment ∧
      heldPointer = .ptr address (some allocation) ∧
      Sem.run (Sem.checkedAccess "Load" address allocation plan.layout.size alignment ctx.byteModel) before = .ok (address,before) ∧
      AggregateMemory.LoadImageAccepted ctx.byteModel ctx.functionOrder ty strict before.memory allocation address plan
        (before.memory.readImage address plan.layout.size) value ∧
      result = .value (some ⟨before.nextValueId⟩) ∧ after.memory = before.memory ∧
      after.lookupValue ⟨before.nextValueId⟩ = some value ∧ after.nextValueId = before.nextValueId + 1 := by
  obtain ⟨heldPointer,value,found,loaded,memory,published,next⟩ :=
    stepLoad_descriptor_execution ctx ty pointer strict align service selected before after result run
  obtain ⟨plan,alignment,address,allocation,target,query,aligned,pointerShape,accessed,accepted,_⟩ :=
    AggregateMemory.loadValue_success_image service ctx.functionOrder ty heldPointer strict align ctx.byteModel before before value loaded
  obtain ⟨_,_,_,_,shape,_⟩ := stepLoad_success_publication ctx ty pointer strict align before after result run
  exact ⟨heldPointer,value,plan,alignment,address,allocation,found,target,query,aligned,pointerShape,accessed,
    accepted,shape,memory,published,next⟩

end TrustIr
