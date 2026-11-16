-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameMemoryDecodeExits
import TrustIr.Proofs.FrameIndirectBodyExits

namespace TrustIr.FrameLifetime

private def Observes {α : Type} (action : Sem α) : Prop := CallCheckReadOnly action ∧ CallCheckNoUnwind action
private theorem observes_pure {α : Type} (value : α) : Observes (pure value : Sem α) := by
  constructor
  · intro state pair run; cases run; rfl
  · intro state exception after run; cases run
private theorem observes_throw {α : Type} (error : SemError) (safe : ExceptNoUnwind (.error error : Except SemError α)) :
    Observes (throw error : Sem α) := by
  constructor
  · intro state pair run; cases run
  · intro state exception after run; cases run; exact safe exception after rfl
private theorem observes_get : Observes Sem.getState := by
  constructor
  · intro state pair run; cases run; rfl
  · intro state exception after run; cases run
private theorem Observes.bind {α β : Type} (action : Sem α) (next : α → Sem β)
    (first : Observes action) (rest : ∀ value, Observes (next value)) : Observes (action >>= next) := by
  constructor
  · intro state pair run
    rw [Sem.run_bind] at run
    cases executed : Sem.run action state with
    | error error => rw [executed] at run; cases run
    | ok middle =>
      have tail : Sem.run (next middle.1) middle.2 = .ok pair := by simpa [executed] using run
      exact (rest middle.1).1 middle.2 pair tail |>.trans (first.1 state middle executed)
  · exact CallCheckNoUnwind.bind _ _ first.2 (fun value => (rest value).2)
private theorem Observes.frame_action {α : Type} (action : Sem α) (observed : Observes action) :
    FrameActionValid (fun _ _ => True) action := by
  apply frame_action_of_success_no_unwind _ _ observed.2
  intro state after value valid run
  have same := observed.1 state (value,after) run
  change after = state at same
  subst after
  exact ⟨valid,True.intro,.refl _⟩

local macro "observe_guards" : tactic => `(tactic|
  repeat' first
    | exact observes_pure _
    | exact observes_get
    | (solve | apply observes_throw; intro exception after same; cases same)
    | (refine Observes.bind _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split
    | (dsimp only; split))

theorem reject_partial_frame_action (value : Value) (operation : String) :
    FrameActionValid (fun _ _ => True) (Sem.rejectPartial value operation) := by
  apply Observes.frame_action
  unfold Sem.rejectPartial
  observe_guards

theorem expect_pointer_frame_action (value : Value) (operation : String) :
    FrameActionValid (fun _ _ => True) (Sem.expectPointer operation value) := by
  apply Observes.frame_action
  unfold Sem.expectPointer
  observe_guards

theorem access_align_frame_action (operation : String) (ty : Ty) (align : Option Nat) (model : ByteModel) :
    FrameActionValid (fun _ _ => True) (Sem.accessAlign operation ty align model) := by
  apply Observes.frame_action
  unfold Sem.accessAlign Sem.declaredOrNaturalAlign
  observe_guards

theorem checked_access_frame_action (operation : String) (address : Addr) (allocation : AllocId)
    (size align : Nat) (model : ByteModel) :
    FrameActionValid (fun _ _ => True) (Sem.checkedAccess operation address allocation size align model) := by
  apply Observes.frame_action
  unfold Sem.checkedAccess Sem.checkTargetRange
  observe_guards

/-- The three access guards neither change the state nor raise: a caller can
carry a fact about the state it ran them in across each of them. -/
theorem reject_partial_observed (value : Value) (operation : String) :
    CallCheckReadOnly (Sem.rejectPartial value operation) ∧
      CallCheckNoUnwind (Sem.rejectPartial value operation) := by
  have observed : Observes (Sem.rejectPartial value operation) := by
    unfold Sem.rejectPartial
    observe_guards
  exact observed

theorem access_align_observed (operation : String) (ty : Ty) (align : Option Nat) (model : ByteModel) :
    CallCheckReadOnly (Sem.accessAlign operation ty align model) ∧
      CallCheckNoUnwind (Sem.accessAlign operation ty align model) := by
  have observed : Observes (Sem.accessAlign operation ty align model) := by
    unfold Sem.accessAlign Sem.declaredOrNaturalAlign
    observe_guards
  exact observed

theorem checked_access_observed (operation : String) (address : Addr) (allocation : AllocId)
    (size align : Nat) (model : ByteModel) :
    CallCheckReadOnly (Sem.checkedAccess operation address allocation size align model) ∧
      CallCheckNoUnwind (Sem.checkedAccess operation address allocation size align model) := by
  have observed : Observes (Sem.checkedAccess operation address allocation size align model) := by
    unfold Sem.checkedAccess Sem.checkTargetRange
    observe_guards
  exact observed

/-- Original held-value load with a proved decoder. All pointer/layout/alignment,
provenance/liveness/bounds and partial-image checks retain their original order.
No memory validity premise is needed: invalid accesses take their actual errors. -/
theorem load_value_using_frame_exit (decode : Memory → List UInt8 → Except SemError Value)
    (decodes : ∀ memory bytes, DecodeFrameExit (MintedValue 0) (decode memory bytes))
    (ty : Ty) (pointer : Value) (strict : Bool) (align : Option Nat) (model : ByteModel) :
    FrameActionValid MintedValue (semLoadValueUsing decode ty pointer strict align model) := by
  intro state valid
  unfold semLoadValueUsing
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ state (reject_partial_frame_action pointer "Load" state valid)
  intro unit before beforeValid _
  cases unit
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ before (expect_pointer_frame_action pointer "Load" before beforeValid)
  intro pair before beforeValid _
  obtain ⟨address,allocation⟩ := pair
  cases ty.byteSizeFor model with
  | none => exact True.intro
  | some width =>
    simp only [pure_bind]
    apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ before (access_align_frame_action "Load" ty align model before beforeValid)
    intro alignment checked checkedValid _
    apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ checked
      (checked_access_frame_action "Load" address allocation width alignment model checked checkedValid)
    intro address loaded loadedValid _
    apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ loaded (Observes.frame_action _ observes_get loaded loadedValid)
    intro snapshot after afterValid _
    cases snapshot.memory.readBytes address width with
    | none =>
      dsimp only
      split
      · exact ⟨afterValid,(mintedValue_iff_shape _ _).2 True.intro,.refl _⟩
      · exact True.intro
    | some bytes =>
      dsimp only
      have decodedValid := decodes snapshot.memory bytes
      cases decoded : decode snapshot.memory bytes with
      | ok value =>
        rw [decoded] at decodedValid
        exact ⟨afterValid,decodedValid.mono (Nat.zero_le _),.refl _⟩
      | error error =>
        rw [decoded] at decodedValid
        cases error <;> first | exact True.intro | exact False.elim decodedValid

/-- Both target widths and actual contextual function-pointer decoding are
qualified for the scalar/vector load core used by SeqMap element cells. -/
theorem scalar_load_value_frame_exit (ctx : EvalContext) (ty : Ty) (pointer : Value)
    (strict : Bool) (align : Option Nat) :
    FrameActionValid MintedValue (semLoadValueUsing
      (fun memory bytes => decodeMemoryWithFunctions ctx.byteModel ctx.functionOrder memory ty bytes)
      ty pointer strict align ctx.byteModel) :=
  load_value_using_frame_exit _ (fun memory bytes => decode_functions_frame_exit ctx.byteModel ctx.functionOrder memory ty bytes)
    ty pointer strict align ctx.byteModel

theorem fresh_minted_frame_exit (value : Value) (state : MachineState) (valid : WellMintedState state)
    (incoming : MintedValue state.nextFrameLineage value) :
    FrameActionExit (fun _ _ => True) state (Sem.run (Sem.bindFresh value) state) := by
  exact ⟨WellMintedState.fresh_success state _ value _ valid incoming rfl,True.intro,⟨Nat.le_refl _,fun _ _ closed => closed⟩⟩

/-- Actual SSA load publication, for any context selecting the scalar core. -/
theorem scalar_load_step_frame_exit (ctx : EvalContext) (ty : Ty) (pointer : ValueId)
    (strict : Bool) (align : Option Nat) (scalar : ctx.memoryServiceFor ty = none) :
    FrameActionValid (fun _ result => BodyValueResult result)
      (stepInstWithContext ctx (.Load ty pointer strict align)) := by
  intro state valid
  simp only [stepInstWithContext,scalar,semLoadUsing,bind_assoc]
  apply FrameActionExit.bind MintedValue (fun _ result => BodyValueResult result) _ _ state
    (lookup_value_frame_action pointer state valid)
  intro pointer before beforeValid _
  apply FrameActionExit.bind MintedValue (fun _ result => BodyValueResult result) _ _ before
    (scalar_load_value_frame_exit ctx ty pointer strict align before beforeValid)
  intro value loaded loadedValid incoming
  apply FrameActionExit.bind (fun _ _ => True) (fun _ result => BodyValueResult result) _ _ loaded
    (fresh_minted_frame_exit value loaded loadedValid incoming)
  intro id after afterValid _
  exact ⟨afterValid,True.intro,.refl _⟩

/-- Canonical scalar/vector leaf types select the proved core in every
context, including contexts carrying arbitrary producer aggregate services. -/
theorem canonical_load_step_frame_exit (ctx : EvalContext) (ty : Ty) (pointer : ValueId)
    (strict : Bool) (align : Option Nat) (canonical : ty.hasCanonicalMemoryLayout = true) :
    FrameActionValid (fun _ result => BodyValueResult result)
      (stepInstWithContext ctx (.Load ty pointer strict align)) :=
  scalar_load_step_frame_exit ctx ty pointer strict align (by simp [EvalContext.memoryServiceFor,canonical])

theorem scalar_load_body_frame_exit (recurse : GenericCoro.Prefix.Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (ty : Ty) (pointer : ValueId) (strict : Bool) (align : Option Nat)
    (dests : List ValueId) (scalar : ctx.memoryServiceFor ty = none) :
    FrameActionValid (fun _ _ => True)
      (GenericCoro.Prefix.evalBodyStep recurse ctx depth strategy (.Load ty pointer strict align,dests)) := by
  intro state valid
  apply FrameActionExit.bind (fun _ result => BodyValueResult result) (fun _ _ => True) _ _ state
    (scalar_load_step_frame_exit ctx ty pointer strict align scalar state valid)
  intro result loaded loadedValid shape
  cases result with
  | terminator step => cases shape
  | value id =>
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ loaded
      (instruction_results_frame_action ctx (.Load ty pointer strict align) (.value id) dests loaded loadedValid)
    intro unit after afterValid _
    cases unit
    exact ⟨afterValid,True.intro,.refl _⟩
  | values ids =>
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ loaded
      (instruction_results_frame_action ctx (.Load ty pointer strict align) (.values ids) dests loaded loadedValid)
    intro unit after afterValid _
    cases unit
    exact ⟨afterValid,True.intro,.refl _⟩

/-- SeqMap's original contextual cell reader uses this same scalar core
for every canonical leaf, irrespective of producer aggregate-service metadata. -/
theorem canonical_context_load_frame_exit (ctx : EvalContext) (ty : Ty) (pointer : Value)
    (strict : Bool) (canonical : ty.hasCanonicalMemoryLayout = true) :
    FrameActionValid MintedValue (ctx.loadMemoryValue ty pointer strict) := by
  simp only [EvalContext.loadMemoryValue,EvalContext.memoryServiceFor,canonical,↓reduceIte]
  exact scalar_load_value_frame_exit ctx ty pointer strict none

end TrustIr.FrameLifetime
