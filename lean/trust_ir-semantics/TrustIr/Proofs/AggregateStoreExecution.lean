-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.UnwrittenOverwrite
import TrustIr.Proofs.TargetStepProps

namespace TrustIr.AggregateMemory

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

/-- Exact image selection made by the actual Store implementation. Partial
    and typed poison transport keep their own branches and are not assumed to
    have passed the ordinary encoder. -/
def StoreImageAccepted (model : ByteModel) (order : FunctionAddressOrder) (ty : Ty) (plan : Plan)
    (value : Value) (image : Image) : Prop :=
  match value with
  | .partial bytes => image = { bytes := ByteImage.ofList bytes }
  | .undef held => closureTyEq held ty = true ∧ image = { bytes := ByteImage.fill plan.layout.size none }
  | _ => encode model order plan value (carriesUnwritten value) = .ok image

private def storeImageAction (model : ByteModel) (order : FunctionAddressOrder) (ty : Ty) (plan : Plan)
    (value : Value) : Sem Image :=
  match value with
  | .partial bytes => pure { bytes := ByteImage.ofList bytes }
  | .undef held =>
    if closureTyEq held ty then pure { bytes := ByteImage.fill plan.layout.size none }
    else Sem.throwTypeError "Store: poison source type does not match store type"
  | _ => Sem.fromMemoryExcept (encode model order plan value (carriesUnwritten value))

private theorem image_action_success (model : ByteModel) (order : FunctionAddressOrder) (ty : Ty) (plan : Plan)
    (value : Value) (image : Image) (before after : MachineState)
    (run : Sem.run (storeImageAction model order ty plan value) before = .ok (image,after)) :
    after = before ∧ StoreImageAccepted model order ty plan value image := by
  cases value
  case «partial» bytes => cases run; exact ⟨rfl,rfl⟩
  case undef held =>
    change Sem.run (if closureTyEq held ty then pure { bytes := ByteImage.fill plan.layout.size none }
      else Sem.throwTypeError "Store: poison source type does not match store type") before = .ok (image,after) at run
    by_cases same : closureTyEq held ty = true
    · simp only [same,ite_true] at run
      cases run
      exact ⟨rfl,same,rfl⟩
    · simp only [same,ite_false] at run
      cases run
  all_goals
    obtain ⟨encoded,rfl⟩ := except_action_success _ before after image run
    exact ⟨rfl,encoded⟩

private def publishStore (address : Nat) (allocation : AllocId) (plan : Plan) (image : Image) : Sem Unit := do
  if image.bytes.size != plan.layout.size then
    Sem.throwTypeError "Store: image byte count does not match source layout"
  Sem.modifyState fun state => { state with memory :=
    (state.memory.writeImage address image.bytes).recordUnwritten allocation address image.unwritten }

private theorem image_tail_eq (model : ByteModel) (order : FunctionAddressOrder) (ty : Ty) (plan : Plan)
    (value : Value) (address : Nat) (allocation : AllocId) :
    (storeImageAction model order ty plan value >>= publishStore address allocation plan) =
      (match value with
      | .partial bytes => publishStore address allocation plan { bytes := ByteImage.ofList bytes }
      | .undef held =>
        if closureTyEq held ty then publishStore address allocation plan { bytes := ByteImage.fill plan.layout.size none }
        else Sem.throwTypeError "Store: poison source type does not match store type"
      | _ => Sem.fromMemoryExcept (encode model order plan value (carriesUnwritten value)) >>=
          publishStore address allocation plan) := by
  cases value <;> try rfl
  rename_i held
  by_cases same : closureTyEq held ty = true
  all_goals simp only [storeImageAction,same,ite_true,ite_false,pure_bind] <;> rfl

private theorem model_beq_sound (left right : ByteModel) (same : (left == right) = true) : left = right := by
  cases left <;> cases right <;> first | rfl | cases same

private def storePlanResult (service : Service) (model : ByteModel) (ty : Ty) : Except SemError Plan :=
  if model == service.model then service.query ty
  else .error (.typeError "memory: source layout target does not match evaluator target")

private def storeAccessPart (model : ByteModel) (order : FunctionAddressOrder) (ty : Ty)
    (pointer value : Value) (plan : Plan) (alignment : Nat) : Sem Unit := do
  Sem.rejectPartial pointer "Store"
  let pair ← Sem.expectPointer "Store" pointer
  let address ← Sem.checkedAccess "Store" pair.1 pair.2 plan.layout.size alignment model
  let image ← storeImageAction model order ty plan value
  publishStore address pair.2 plan image

private theorem access_success (model : ByteModel) (address : Nat) (allocation : AllocId)
    (size alignment : Nat) (before after : MachineState) (actual : Nat)
    (run : Sem.run (Sem.checkedAccess "Store" address allocation size alignment model) before = .ok (actual,after)) :
    after = before ∧ actual = address := by
  cases model with
  | le64 =>
    obtain ⟨same,addressSame,_⟩ := checkedAccess_ok_inv "Store" address allocation size alignment before after actual run
    exact ⟨same,addressSame⟩
  | le32 =>
    obtain ⟨same,addressSame,_⟩ := checkedAccess32_names_live_provenance "Store" address allocation size alignment before after actual run
    exact ⟨same,addressSame⟩

/-- A successful actual aggregate Store derives every selected check and its
    complete memory update. Callers supply neither an assumed child decoder nor
    a manually selected plan, pointer, byte image or intermediate state. -/
theorem storeValue_success_steps (service : Service) (order : FunctionAddressOrder) (ty : Ty)
    (pointer value : Value) (strict : Bool) (align : Option Nat) (model : ByteModel)
    (before after : MachineState)
    (run : Sem.run (storeValue service order ty pointer value strict align model) before = .ok ((),after)) :
    (strict && (value.isPoison || carriesUnwritten value)) = false ∧
    ∃ plan alignment address allocation image,
      model = service.model ∧ service.query ty = .ok plan ∧
      checkedMemoryAlign "Store" plan.layout.alignment align = .ok alignment ∧
      pointer = .ptr address (some allocation) ∧
      Sem.run (Sem.checkedAccess "Store" address allocation plan.layout.size alignment model) before = .ok (address,before) ∧
      StoreImageAccepted model order ty plan value image ∧ image.bytes.size = plan.layout.size ∧
      after = { before with memory :=
        (before.memory.writeImage address image.bytes).recordUnwritten allocation address image.unwritten } := by
  unfold storeValue at run
  by_cases rejected : (strict && (value.isPoison || carriesUnwritten value)) = true
  · simp only [rejected,ite_true] at run
    cases run
  · have clean : (strict && (value.isPoison || carriesUnwritten value)) = false := by
      cases flag : strict && (value.isPoison || carriesUnwritten value) with
      | false => rfl
      | true => exact False.elim (rejected flag)
    simp only [rejected,ite_false,pure_bind] at run
    have normalized : Sem.run (do
        let plan ← Sem.fromMemoryExcept (storePlanResult service model ty)
        let alignment ← Sem.fromMemoryExcept (checkedMemoryAlign "Store" plan.layout.alignment align)
        storeAccessPart model order ty pointer value plan alignment) before = .ok ((),after) := by
      simp only [storeAccessPart]
      simp only [image_tail_eq]
      simpa only [publishStore,pure_bind,storePlanResult] using run
    obtain ⟨plan,query,run⟩ := except_bind_success (storePlanResult service model ty)
      (fun plan => do
        let alignment ← Sem.fromMemoryExcept (checkedMemoryAlign "Store" plan.layout.alignment align)
        storeAccessPart model order ty pointer value plan alignment) before after () normalized
    obtain ⟨target,query⟩ : model = service.model ∧ service.query ty = .ok plan := by
      unfold storePlanResult at query
      split at query
      · rename_i same
        have equal : model = service.model := model_beq_sound model service.model same
        exact ⟨equal,query⟩
      · cases query
    obtain ⟨alignment,aligned,run⟩ := except_bind_success (checkedMemoryAlign "Store" plan.layout.alignment align)
      (storeAccessPart model order ty pointer value plan) before after () run
    unfold storeAccessPart at run
    obtain ⟨unit,middle,inspected,run⟩ := run_bind_success (Sem.rejectPartial pointer "Store")
      (fun _ => do
        let pair ← Sem.expectPointer "Store" pointer
        let address ← Sem.checkedAccess "Store" pair.1 pair.2 plan.layout.size alignment model
        let image ← storeImageAction model order ty plan value
        publishStore address pair.2 plan image) before after () run
    have same := rejectPartial_ok_state "Store" pointer before middle unit inspected
    subst middle
    cases unit
    obtain ⟨pair,middle,pointerRun,run⟩ := run_bind_success (Sem.expectPointer "Store" pointer)
      (fun pair => do
        let address ← Sem.checkedAccess "Store" pair.1 pair.2 plan.layout.size alignment model
        let image ← storeImageAction model order ty plan value
        publishStore address pair.2 plan image) before after () run
    obtain ⟨same,pointerShape⟩ := expectPointer_ok_inv "Store" pointer before middle pair pointerRun
    subst middle
    obtain ⟨address,allocation⟩ := pair
    obtain ⟨actual,middle,accessed,run⟩ := run_bind_success
      (Sem.checkedAccess "Store" address allocation plan.layout.size alignment model)
      (fun actual => storeImageAction model order ty plan value >>= publishStore actual allocation plan)
      before after () run
    obtain ⟨same,addressSame⟩ := access_success model address allocation plan.layout.size alignment before middle actual accessed
    subst middle
    subst actual
    obtain ⟨image,middle,selected,run⟩ := run_bind_success (storeImageAction model order ty plan value)
      (publishStore address allocation plan) before after () run
    obtain ⟨same,imageReady⟩ := image_action_success model order ty plan value image before middle selected
    subst middle
    unfold publishStore at run
    by_cases extent : image.bytes.size = plan.layout.size
    · simp only [extent,bne_self_eq_false,Bool.false_eq_true,ite_false,pure_bind] at run
      have finalState : after = { before with memory :=
          (before.memory.writeImage address image.bytes).recordUnwritten allocation address image.unwritten } := by
        change Except.ok ((), { before with memory :=
          (before.memory.writeImage address image.bytes).recordUnwritten allocation address image.unwritten }) = .ok ((),after) at run
        cases run
        rfl
      exact ⟨clean,plan,alignment,address,allocation,image,target,query,aligned,pointerShape,accessed,imageReady,extent,finalState⟩
    · have mismatch : (image.bytes.size != plan.layout.size) = true := by simp [extent]
      simp only [mismatch,ite_true] at run
      cases run

theorem StoreImageAccepted.unwritten_bounded {model : ByteModel} {order : FunctionAddressOrder}
    {ty : Ty} {plan : Plan} {value : Value} {image : Image}
    (accepted : StoreImageAccepted model order ty plan value image) : image.UnwrittenBounded := by
  cases value
  case «partial» bytes => cases accepted; exact Image.unwritten_bounded_of_empty _ rfl
  case undef held => cases accepted.2; exact Image.unwritten_bounded_of_empty _ rfl
  all_goals exact encode_unwritten_bounded model order plan _ _ image accepted

theorem StoreImageAccepted.unwritten_empty {model : ByteModel} {order : FunctionAddressOrder}
    {ty : Ty} {plan : Plan} {value : Value} {image : Image}
    (accepted : StoreImageAccepted model order ty plan value image) (clear : carriesUnwritten value = false) :
    image.unwritten = [] := by
  cases value
  case «partial» bytes => cases accepted; rfl
  case undef held => cases accepted.2; rfl
  all_goals
    unfold StoreImageAccepted at accepted
    rw [clear] at accepted
    exact encode_ordinary_unwritten_empty model order plan _ image accepted

private theorem access_live (model : ByteModel) (address : Nat) (allocation : AllocId)
    (size alignment : Nat) (before : MachineState)
    (run : Sem.run (Sem.checkedAccess "Store" address allocation size alignment model) before = .ok (address,before)) :
    ∃ live, before.memory.lookup allocation = some live ∧ live.alive = true ∧
      (alignment = 0 ∨ address % alignment = 0) ∧ live.base ≤ address ∧
      address - live.base + size ≤ live.size ∧
      (model = .le32 → address < ByteModel.le32.addressLimit ∧ address + size ≤ ByteModel.le32.addressLimit) := by
  cases model with
  | le64 =>
    obtain ⟨_,_,live,found,alive,aligned,base,extent⟩ :=
      checkedAccess_ok_inv "Store" address allocation size alignment before before address run
    exact ⟨live,found,alive,aligned,base,extent,by intro impossible; cases impossible⟩
  | le32 =>
    obtain ⟨legacy,targetStart,targetEnd⟩ :=
      checkedAccess32_retains_legacy "Store" address allocation size alignment before before address run
    obtain ⟨_,_,live,found,alive,aligned,base,extent⟩ :=
      checkedAccess_ok_inv "Store" address allocation size alignment before before address legacy
    exact ⟨live,found,alive,aligned,base,extent,fun _ => ⟨targetStart,targetEnd⟩⟩

/-- Actual Store success names its live provenance allocation and exact source
    extent, with the real alignment and 32-bit target checks retained. -/
theorem storeValue_success_live_allocation (service : Service) (order : FunctionAddressOrder) (ty : Ty)
    (pointer value : Value) (strict : Bool) (align : Option Nat) (model : ByteModel)
    (before after : MachineState)
    (run : Sem.run (storeValue service order ty pointer value strict align model) before = .ok ((),after)) :
    ∃ plan alignment address allocation live,
      model = service.model ∧ service.query ty = .ok plan ∧
      checkedMemoryAlign "Store" plan.layout.alignment align = .ok alignment ∧
      pointer = .ptr address (some allocation) ∧ before.memory.lookup allocation = some live ∧
      live.alive = true ∧ (alignment = 0 ∨ address % alignment = 0) ∧ live.base ≤ address ∧
      address - live.base + plan.layout.size ≤ live.size ∧
      (model = .le32 → address < ByteModel.le32.addressLimit ∧ address + plan.layout.size ≤ ByteModel.le32.addressLimit) := by
  obtain ⟨_clean,plan,alignment,address,allocation,image,target,query,aligned,pointerShape,accessed,_image,_extent,_state⟩ :=
    storeValue_success_steps service order ty pointer value strict align model before after run
  obtain ⟨live,found,alive,alignmentOk,base,extent,targetRange⟩ :=
    access_live model address allocation plan.layout.size alignment before accessed
  exact ⟨plan,alignment,address,allocation,live,target,query,aligned,pointerShape,found,alive,alignmentOk,base,extent,targetRange⟩

/-- A successful Store of a carrier without explicit unwritten children clears
    old coverage inside the actual written extent and preserves it outside.
    Partial-byte and typed-poison transport remain covered by this law. -/
theorem storeValue_success_unwritten_coverage (service : Service) (order : FunctionAddressOrder) (ty : Ty)
    (pointer value : Value) (strict : Bool) (align : Option Nat) (model : ByteModel)
    (before after : MachineState) (clear : carriesUnwritten value = false)
    (run : Sem.run (storeValue service order ty pointer value strict align model) before = .ok ((),after)) :
    ∃ plan address allocation, service.query ty = .ok plan ∧ pointer = .ptr address (some allocation) ∧
      ∀ queryAllocation query, after.memory.isUnwritten queryAllocation query =
        (before.memory.isUnwritten queryAllocation query && !(address ≤ query && query < address + plan.layout.size)) := by
  obtain ⟨_clean,plan,alignment,address,allocation,image,_target,query,_aligned,pointerShape,_accessed,accepted,extent,state⟩ :=
    storeValue_success_steps service order ty pointer value strict align model before after run
  have empty := accepted.unwritten_empty clear
  refine ⟨plan,address,allocation,query,pointerShape,?_⟩
  intro queryAllocation queried
  rw [state]
  dsimp only
  rw [empty]
  change (before.memory.writeImage address image.bytes).isUnwritten queryAllocation queried = _
  rw [Memory.writeImage_unwritten_coverage,extent]

/-- Every new range actually registered by a successful Store belongs to its
    accessed live allocation and remains inside that allocation's footprint.
    Old clipped records retain a separate origin instead of gaining new credit. -/
theorem storeValue_success_registered_bounds (service : Service) (order : FunctionAddressOrder) (ty : Ty)
    (pointer value : Value) (strict : Bool) (align : Option Nat) (model : ByteModel)
    (before after : MachineState)
    (run : Sem.run (storeValue service order ty pointer value strict align model) before = .ok ((),after)) :
    ∃ (plan : Plan) (address : Nat) (allocation : AllocId) (image : Image) (live : Allocation),
      service.query ty = .ok plan ∧ pointer = .ptr address (some allocation) ∧
      before.memory.lookup allocation = some live ∧ live.alive = true ∧
      StoreImageAccepted model order ty plan value image ∧ image.bytes.size = plan.layout.size ∧
      after = { before with memory := (before.memory.writeImage address image.bytes).recordUnwritten allocation address image.unwritten } ∧
      ∀ lane ∈ after.memory.unwritten,
        lane ∈ (before.memory.writeImage address image.bytes).unwritten ∨
          lane.allocation = allocation ∧ live.base ≤ lane.start ∧ lane.start < lane.stop ∧
            lane.stop ≤ live.base + live.size := by
  obtain ⟨_clean,plan,alignment,address,allocation,image,_target,query,_aligned,pointerShape,accessed,accepted,extent,state⟩ :=
    storeValue_success_steps service order ty pointer value strict align model before after run
  obtain ⟨live,found,alive,_alignment,base,accessEnd,_targetRange⟩ :=
    access_live model address allocation plan.layout.size alignment before accessed
  have endBound : address + plan.layout.size ≤ live.base + live.size := by omega
  refine ⟨plan,address,allocation,image,live,query,pointerShape,found,alive,accepted,extent,state,?_⟩
  intro lane member
  rw [state] at member
  dsimp only at member
  have bound := image.recordUnwritten_bounds accepted.unwritten_bounded
    (before.memory.writeImage address image.bytes) allocation address lane member
  rcases bound with old | ⟨same,low,nonempty,high⟩
  · exact Or.inl old
  · refine Or.inr ⟨same,Nat.le_trans base low,nonempty,?_⟩
    rw [extent] at high
    exact Nat.le_trans high endBound

end TrustIr.AggregateMemory
