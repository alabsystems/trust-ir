-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameInvokeExits

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix

/-- An action's normal postcondition and actual embedded unwind state. Other
errors expose no final state and propagate without a fabricated state claim. -/
def FrameActionExit {α : Type} (post : Nat → α → Prop) (before : MachineState) :
    Except SemError (α × MachineState) → Prop
  | .ok (value,after) => WellMintedState after ∧ post after.nextFrameLineage value ∧ HistoryExtends before after
  | .error (.unwinding _ after) => WellMintedState after ∧ HistoryExtends before after
  | .error _ => True

def FrameActionValid {α : Type} (post : Nat → α → Prop) (action : Sem α) : Prop :=
  ∀ state, WellMintedState state → FrameActionExit post state (Sem.run action state)

theorem FrameActionExit.history {α : Type} (post : Nat → α → Prop) (before middle : MachineState)
    (result : Except SemError (α × MachineState)) (history : HistoryExtends before middle)
    (valid : FrameActionExit post middle result) : FrameActionExit post before result := by
  cases result with
  | ok pair => exact ⟨valid.1,valid.2.1,history.trans valid.2.2⟩
  | error error =>
    cases error <;> first | exact True.intro | exact ⟨valid.1,history.trans valid.2⟩

theorem FrameActionExit.callee (before : MachineState) (result : Except SemError (List Value × MachineState)) :
    FrameActionExit MintedArgs before result ↔ FrameCalleeExit before result := by
  cases result with
  | ok pair => rfl
  | error error => cases error <;> rfl

/-- State-specific sequencing consumes a current-state result contract;
returned arguments need not satisfy the postcondition in unrelated states. -/
theorem FrameActionExit.bind {α β : Type} (post : Nat → α → Prop) (nextPost : Nat → β → Prop)
    (action : Sem α) (next : α → Sem β) (state : MachineState)
    (executedValid : FrameActionExit post state (Sem.run action state))
    (rest : ∀ value middle, WellMintedState middle → post middle.nextFrameLineage value →
      FrameActionExit nextPost middle (Sem.run (next value) middle)) :
    FrameActionExit nextPost state (Sem.run (action >>= next) state) := by
  rw [Sem.run_bind]
  cases executed : Sem.run action state with
  | error error =>
    rw [executed] at executedValid
    simp only [Except.bind]
    cases error <;> exact executedValid
  | ok pair =>
    obtain ⟨value,middle⟩ := pair
    rw [executed] at executedValid
    simp only [Except.bind]
    exact FrameActionExit.history nextPost state middle _ executedValid.2.2
      (rest value middle executedValid.1 executedValid.2.1)

/-- Compose only the continuation selected by an actual successful first
run. A first-action unwind propagates its original embedded state. -/
theorem FrameActionValid.bind {α β : Type} (post : Nat → α → Prop) (nextPost : Nat → β → Prop)
    (action : Sem α) (next : α → Sem β) (first : FrameActionValid post action)
    (rest : ∀ value state, WellMintedState state → post state.nextFrameLineage value →
      FrameActionExit nextPost state (Sem.run (next value) state)) :
    FrameActionValid nextPost (action >>= next) := by
  intro state valid
  exact FrameActionExit.bind post nextPost action next state (first state valid) rest

theorem frame_action_pure {α : Type} (post : Nat → α → Prop) (value : α)
    (holds : ∀ state, WellMintedState state → post state.nextFrameLineage value) :
    FrameActionValid post (pure value : Sem α) := by
  intro state valid
  exact ⟨valid,holds state valid,.refl _⟩

/-- Reuse successful-state proofs only after ruling out forged unwind errors. -/
theorem frame_action_of_success_no_unwind {α : Type} (post : Nat → α → Prop) (action : Sem α)
    (safe : CallCheckNoUnwind action)
    (success : ∀ state after value, WellMintedState state → Sem.run action state = .ok (value,after) →
      WellMintedState after ∧ post after.nextFrameLineage value ∧ HistoryExtends state after) :
    FrameActionValid post action := by
  intro state valid
  cases executed : Sem.run action state with
  | ok pair => exact success state pair.2 pair.1 valid executed
  | error error =>
    cases error <;> first | exact True.intro | exact False.elim (safe state _ _ executed)

theorem CallCheckNoUnwind.bind {α β : Type} (action : Sem α) (next : α → Sem β)
    (first : CallCheckNoUnwind action) (rest : ∀ value, CallCheckNoUnwind (next value)) :
    CallCheckNoUnwind (action >>= next) := by
  intro state exception after run
  rw [Sem.run_bind] at run
  cases executed : Sem.run action state with
  | error error =>
    simp only [executed,Except.bind] at run
    cases run
    exact first state exception after executed
  | ok pair =>
    simp only [executed,Except.bind] at run
    exact rest pair.1 pair.2 exception after run

/-- Actual exception allocation can be composed before further raising actions. -/
theorem exception_allocation_frame_action (message : String) (site : Option PanicOutcomeSite) (model : ByteModel) :
    FrameActionValid (fun _ _ => True) (semAllocException message site model) := by
  apply frame_action_of_success_no_unwind
  · exact fun state exception after => exception_allocation_no_unwind message site model state after exception
  · intro state after exception valid run
    obtain ⟨afterValid,history⟩ := exception_allocation_frame_success message site model state after exception valid run
    exact ⟨afterValid,True.intro,history⟩

/-- Real raising has no normal return; its actual allocated throw state is
validated rather than accepting arbitrary supplied unwind states. -/
theorem raise_frame_action {α : Type} (post : Nat → α → Prop)
    (message : String) (site : Option PanicOutcomeSite) (model : ByteModel) :
    FrameActionValid post (semRaise message site model) := by
  intro state valid
  cases executed : Sem.run (semRaise (α := α) message site model) state with
  | error error =>
    cases error <;> first
      | exact True.intro
      | exact raise_frame_exit message site model state _ _ valid executed
  | ok pair =>
    unfold semRaise at executed
    rw [Sem.run_bind] at executed
    cases allocated : Sem.run (semAllocException message site model) state with
    | error error => rw [allocated] at executed; cases executed
    | ok allocation =>
      rw [allocated] at executed
      cases executed

/-- Enter-pad success and no-action propagation obey the same action contract. -/
theorem enter_pad_frame_action (cfg : CFG) (exception : Addr) (dest : BlockId) :
    FrameActionValid (fun _ _ => True) (semEnterPad cfg exception dest) := by
  intro state valid
  cases executed : Sem.run (semEnterPad cfg exception dest) state with
  | ok pair =>
    obtain ⟨unit,after⟩ := pair
    cases unit
    obtain ⟨afterValid,history⟩ := enter_pad_frame_success cfg exception dest state after valid executed
    exact ⟨afterValid,True.intro,history⟩
  | error error =>
    cases error
    case unwinding raised after =>
      have same := enter_pad_unwind_state cfg exception dest state after raised executed
      subst after
      exact ⟨valid,.refl _⟩
    all_goals exact True.intro

private theorem pure_no_unwind {α : Type} (value : α) : CallCheckNoUnwind (pure value : Sem α) := by
  intro state exception after run
  cases run

private theorem get_no_unwind : CallCheckNoUnwind Sem.getState := by
  intro state exception after run
  cases run

private theorem set_no_unwind (state : MachineState) : CallCheckNoUnwind (Sem.setState state) := by
  intro before exception after run
  cases run

private theorem fresh_no_unwind (value : Value) : CallCheckNoUnwind (Sem.bindFresh value) := by
  intro state exception after run
  cases run

private theorem type_no_unwind {α : Type} (message : String) : CallCheckNoUnwind (Sem.throwTypeError message : Sem α) := by
  intro state exception after run
  cases run

private theorem ub_no_unwind {α : Type} (message : String) : CallCheckNoUnwind (Sem.throwUB message : Sem α) := by
  intro state exception after run
  cases run

private theorem lookup_no_unwind (id : ValueId) : CallCheckNoUnwind (Sem.lookupValue id) := by
  unfold Sem.lookupValue
  refine CallCheckNoUnwind.bind _ _ get_no_unwind ?_
  intro state
  split <;> first | exact pure_no_unwind _ | exact type_no_unwind _

private theorem partial_no_unwind (value : Value) (message : String) : CallCheckNoUnwind (Sem.rejectPartial value message) := by
  cases value <;> first | exact pure_no_unwind _ | exact ub_no_unwind _

private theorem frame_state_no_unwind (live : List Nat) (counter : Nat) : CallCheckNoUnwind (Sem.setFrameState live counter) := by
  unfold Sem.setFrameState
  exact CallCheckNoUnwind.bind _ _ get_no_unwind (fun _ => set_no_unwind _)

local macro "frame_no_unwind_leaves" : tactic => `(tactic|
  repeat' first
    | exact pure_no_unwind _
    | exact get_no_unwind
    | exact set_no_unwind _
    | exact fresh_no_unwind _
    | exact type_no_unwind _
    | exact ub_no_unwind _
    | exact lookup_no_unwind _
    | exact partial_no_unwind _ _
    | exact frame_state_no_unwind _ _
    | (refine CallCheckNoUnwind.bind _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split)

theorem open_frame_no_unwind (definition : BindingFrameDef) : CallCheckNoUnwind (semOpenFrame definition) := by
  unfold semOpenFrame
  frame_no_unwind_leaves

theorem bind_slot_no_unwind (frame : ValueId) (slot : Nat) (value : ValueId) : CallCheckNoUnwind (semBindSlot frame slot value) := by
  unfold semBindSlot Sem.frameHandle
  frame_no_unwind_leaves

theorem load_slot_no_unwind (frame : ValueId) (slot : Nat) (ty : Ty) : CallCheckNoUnwind (semLoadSlot frame slot ty) := by
  unfold semLoadSlot Sem.frameHandle
  frame_no_unwind_leaves

theorem close_frame_no_unwind (frame : ValueId) : CallCheckNoUnwind (semCloseFrame frame) := by
  unfold semCloseFrame Sem.frameHandle
  frame_no_unwind_leaves

theorem open_frame_action (definition : BindingFrameDef) :
    FrameActionValid (fun _ _ => True) (semOpenFrame definition) := by
  apply frame_action_of_success_no_unwind _ _ (open_frame_no_unwind definition)
  intro state after id valid run
  exact ⟨valid.open_success state after definition id run,True.intro,
    (open_success_history state after definition id run).1⟩

theorem bind_slot_action (frame : ValueId) (slot : Nat) (value : ValueId) :
    FrameActionValid (fun _ _ => True) (semBindSlot frame slot value) := by
  apply frame_action_of_success_no_unwind _ _ (bind_slot_no_unwind frame slot value)
  intro state after id valid run
  exact ⟨valid.bind_success state after frame value id slot run,True.intro,
    (HistoryEffects.semBindSlot_history frame slot value).extends state after id run⟩

theorem load_slot_action (frame : ValueId) (slot : Nat) (ty : Ty) :
    FrameActionValid (fun _ _ => True) (semLoadSlot frame slot ty) := by
  apply frame_action_of_success_no_unwind _ _ (load_slot_no_unwind frame slot ty)
  intro state after id valid run
  exact ⟨valid.load_success state after frame id slot ty run,True.intro,
    (HistoryEffects.semLoadSlot_history frame slot ty).extends state after id run⟩

theorem close_frame_action (frame : ValueId) :
    FrameActionValid (fun _ _ => True) (semCloseFrame frame) := by
  apply frame_action_of_success_no_unwind _ _ (close_frame_no_unwind frame)
  intro state after unit valid run
  cases unit
  refine ⟨valid.close_success state after frame run,True.intro,?_⟩
  obtain ⟨lineage,slots,_,_,rfl⟩ := close_success_state state after frame run
  exact history_close state lineage

/-- Ordered argument transport supplies a useful result postcondition for
composition, rather than discarding the identities of returned values. -/
theorem lookup_arguments_no_unwind (ids : List ValueId) : CallCheckNoUnwind (ids.mapM Sem.lookupValue) := by
  induction ids with
  | nil => exact pure_no_unwind _
  | cons id rest ih =>
    rw [List.mapM_cons]
    exact CallCheckNoUnwind.bind _ _ (lookup_no_unwind id) (fun _ =>
      CallCheckNoUnwind.bind _ _ ih (fun _ => pure_no_unwind _))

theorem lookup_arguments_action (ids : List ValueId) :
    FrameActionValid MintedArgs (ids.mapM Sem.lookupValue) := by
  apply frame_action_of_success_no_unwind _ _ (lookup_arguments_no_unwind ids)
  intro state after values valid run
  obtain ⟨same,incoming⟩ := lookup_args_success ids state after values valid run
  subst after
  exact ⟨valid,incoming,.refl _⟩

end TrustIr.FrameLifetime

