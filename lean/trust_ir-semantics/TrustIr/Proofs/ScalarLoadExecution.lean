-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.AggregateLoadExecution

namespace TrustIr

/-- Successful scalar loads either decode actual initialized bytes from the
    original memory or transport its actual partial image when allowed. -/
def ScalarLoadImageAccepted (decode : Memory → List UInt8 → Except SemError Value)
    (ty : Ty) (strict : Bool) (model : ByteModel) (memory : Memory) (address size : Nat) (value : Value) : Prop :=
  (∃ bytes, memory.readBytes address size = some bytes ∧ decode memory bytes = .ok value) ∨
  (memory.readBytes address size = none ∧ (!strict && isPartialLoadTyFor model ty) = true ∧
    value = .partial (memory.readBytesMaybeUninit address size))

private theorem scalar_run_bind_success {α β : Type} (first : Sem α) (next : α → Sem β)
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

private theorem scalar_alignment_success (ty : Ty) (align : Option Nat) (model : ByteModel)
    (before after : MachineState) (alignment : Nat)
    (run : Sem.run (Sem.accessAlign "Load" ty align model) before = .ok (alignment,after)) :
    after = before := by
  unfold Sem.accessAlign Sem.declaredOrNaturalAlign at run
  dsimp only at run
  split at run <;> cases run
  rfl

/-- Derive every selected scalar check and actual byte/decode outcome from
    held execution. No assumed read, decoder answer or intermediate state. -/
theorem scalarLoadValue_success_steps (decode : Memory → List UInt8 → Except SemError Value)
    (ty : Ty) (pointer : Value) (strict : Bool) (align : Option Nat) (model : ByteModel)
    (before after : MachineState) (value : Value)
    (run : Sem.run (semLoadValueUsing decode ty pointer strict align model) before = .ok (value,after)) :
    ∃ size alignment address allocation,
      pointer = .ptr address (some allocation) ∧ ty.byteSizeFor model = some size ∧
      Sem.run (Sem.accessAlign "Load" ty align model) before = .ok (alignment,before) ∧
      Sem.run (Sem.checkedAccess "Load" address allocation size alignment model) before = .ok (address,before) ∧
      ScalarLoadImageAccepted decode ty strict model before.memory address size value ∧ after = before := by
  unfold semLoadValueUsing at run
  obtain ⟨unit,middle,inspected,run⟩ := scalar_run_bind_success _ _ before after value run
  have same := rejectPartial_ok_state "Load" pointer before middle unit inspected
  subst middle
  cases unit
  obtain ⟨pair,middle,pointerRun,run⟩ := scalar_run_bind_success _ _ before after value run
  obtain ⟨same,pointerShape⟩ := expectPointer_ok_inv "Load" pointer before middle pair pointerRun
  subst middle
  obtain ⟨address,allocation⟩ := pair
  cases sized : ty.byteSizeFor model with
  | none => simp only [sized] at run; cases run
  | some size =>
    simp only [sized,pure_bind] at run
    obtain ⟨alignment,middle,aligned,run⟩ := scalar_run_bind_success _ _ before after value run
    have same := scalar_alignment_success ty align model before middle alignment aligned
    subst middle
    obtain ⟨actual,middle,accessed,run⟩ := scalar_run_bind_success _ _ before after value run
    obtain ⟨same,addressSame⟩ : middle = before ∧ actual = address := by
      cases model with
      | le64 =>
        obtain ⟨same,addressSame,_⟩ := checkedAccess_ok_inv "Load" address allocation size alignment before middle actual accessed
        exact ⟨same,addressSame⟩
      | le32 =>
        obtain ⟨same,addressSame,_⟩ := checkedAccess32_names_live_provenance "Load" address allocation size alignment before middle actual accessed
        exact ⟨same,addressSame⟩
    subst middle
    subst actual
    change Sem.run (match before.memory.readBytes address size with
      | some bytes => match decode before.memory bytes with | .ok v => pure v | .error e => throw e
      | none => if !strict && isPartialLoadTyFor model ty then
          pure (.partial (before.memory.readBytesMaybeUninit address size))
        else Sem.throwUB "Load: reading uninitialized memory") before = .ok (value,after) at run
    have image : ScalarLoadImageAccepted decode ty strict model before.memory address size value ∧ after = before := by
      cases read : before.memory.readBytes address size with
      | some bytes =>
        simp only [read] at run
        cases decoded : decode before.memory bytes with
        | error error => simp only [decoded] at run; cases run
        | ok actual =>
          simp only [decoded] at run
          cases run
          exact ⟨Or.inl ⟨bytes,read,decoded⟩,rfl⟩
      | none =>
        simp only [read] at run
        cases allowed : !strict && isPartialLoadTyFor model ty with
        | false => simp only [allowed,Bool.false_eq_true,ite_false] at run; cases run
        | true =>
          simp only [allowed,ite_true] at run
          cases run
          exact ⟨Or.inr ⟨read,allowed,rfl⟩,rfl⟩
    exact ⟨size,alignment,address,allocation,pointerShape,rfl,aligned,accessed,image⟩

theorem scalarLoadValue_of_checks (decode : Memory → List UInt8 → Except SemError Value)
    (ty : Ty) (strict : Bool) (align : Option Nat) (model : ByteModel) (before : MachineState)
    (value : Value) (size alignment address : Nat) (allocation : AllocId)
    (sized : ty.byteSizeFor model = some size)
    (aligned : Sem.run (Sem.accessAlign "Load" ty align model) before = .ok (alignment,before))
    (accessed : Sem.run (Sem.checkedAccess "Load" address allocation size alignment model) before = .ok (address,before))
    (image : ScalarLoadImageAccepted decode ty strict model before.memory address size value) :
    Sem.run (semLoadValueUsing decode ty (.ptr address (some allocation)) strict align model) before = .ok (value,before) := by
  unfold semLoadValueUsing
  simp only [Sem.rejectPartial,Sem.expectPointer,pure_bind,sized,Sem.run_bind,aligned,accessed,Except.bind]
  change Sem.run (match before.memory.readBytes address size with
    | some bytes => match decode before.memory bytes with | .ok v => pure v | .error e => throw e
    | none => if !strict && isPartialLoadTyFor model ty then
        pure (.partial (before.memory.readBytesMaybeUninit address size))
      else Sem.throwUB "Load: reading uninitialized memory") before = .ok (value,before)
  rcases image with ⟨bytes,read,decoded⟩ | ⟨read,allowed,rfl⟩
  · simp only [read,decoded,Sem.run_pure]
  · simp only [read,allowed,ite_true,Sem.run_pure]

theorem scalarLoadValue_success_iff (decode : Memory → List UInt8 → Except SemError Value)
    (ty : Ty) (pointer : Value) (strict : Bool) (align : Option Nat) (model : ByteModel)
    (before after : MachineState) (value : Value) :
    Sem.run (semLoadValueUsing decode ty pointer strict align model) before = .ok (value,after) ↔
    ∃ size alignment address allocation,
      pointer = .ptr address (some allocation) ∧ ty.byteSizeFor model = some size ∧
      Sem.run (Sem.accessAlign "Load" ty align model) before = .ok (alignment,before) ∧
      Sem.run (Sem.checkedAccess "Load" address allocation size alignment model) before = .ok (address,before) ∧
      ScalarLoadImageAccepted decode ty strict model before.memory address size value ∧ after = before := by
  constructor
  · exact scalarLoadValue_success_steps decode ty pointer strict align model before after value
  · rintro ⟨size,alignment,address,allocation,rfl,sized,aligned,accessed,image,rfl⟩
    exact scalarLoadValue_of_checks decode ty strict align model after value size alignment address allocation sized aligned accessed image

/-- Scalar fallback of the original node authenticates its read and decoder
    to the original SSA operand and memory, with the actual function order. -/
theorem stepLoad_scalar_image (ctx : EvalContext) (ty : Ty) (pointer : ValueId)
    (strict : Bool) (align : Option Nat) (selected : ctx.memoryServiceFor ty = none)
    (before after : MachineState) (result : InstrResult)
    (run : Sem.run (stepInstWithContext ctx (.Load ty pointer strict align)) before = .ok (result,after)) :
    ∃ heldPointer value size alignment address allocation,
      before.lookupValue pointer = some heldPointer ∧ heldPointer = .ptr address (some allocation) ∧
      ty.byteSizeFor ctx.byteModel = some size ∧
      Sem.run (Sem.accessAlign "Load" ty align ctx.byteModel) before = .ok (alignment,before) ∧
      Sem.run (Sem.checkedAccess "Load" address allocation size alignment ctx.byteModel) before = .ok (address,before) ∧
      ScalarLoadImageAccepted
        (fun memory bytes => decodeMemoryWithFunctions ctx.byteModel ctx.functionOrder memory ty bytes)
        ty strict ctx.byteModel before.memory address size value ∧
      result = .value (some ⟨before.nextValueId⟩) ∧ after.memory = before.memory ∧
      after.lookupValue ⟨before.nextValueId⟩ = some value ∧ after.nextValueId = before.nextValueId + 1 := by
  obtain ⟨heldPointer,value,found,loaded,published,next⟩ :=
    stepLoad_published_value ctx ty pointer strict align before after result run
  simp only [selectedLoadAction,selected] at loaded
  obtain ⟨size,alignment,address,allocation,pointerShape,sized,aligned,accessed,image,_⟩ :=
    scalarLoadValue_success_steps _ ty heldPointer strict align ctx.byteModel before before value loaded
  obtain ⟨_,_,_,_,shape,_⟩ := stepLoad_success_publication ctx ty pointer strict align before after result run
  exact ⟨heldPointer,value,size,alignment,address,allocation,found,pointerShape,sized,aligned,accessed,image,
    shape,stepLoad_memory_unchanged ctx ty pointer strict align before after result run,published,next⟩

end TrustIr
