-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameContextSafety

namespace TrustIr.FrameLifetime

/-- Pure validation results may refuse, but cannot invent a runtime throw world. -/
def ExceptNoUnwind {α : Type} (result : Except SemError α) : Prop :=
  ∀ exception after, result ≠ .error (.unwinding exception after)

private theorem except_ok_no_unwind {α : Type} (value : α) : ExceptNoUnwind (.ok value) := by
  intro exception after run
  cases run

private theorem except_type_no_unwind {α : Type} (message : String) : ExceptNoUnwind (.error (.typeError message) : Except SemError α) := by
  intro exception after run
  cases run

private theorem except_ub_no_unwind {α : Type} (message : String) : ExceptNoUnwind (.error (.ub message) : Except SemError α) := by
  intro exception after run
  cases run

private theorem except_unsupported_no_unwind {α : Type} (feature : UnsupportedFeature) (message : String) :
    ExceptNoUnwind (.error (.unsupported feature message) : Except SemError α) := by
  intro exception after run
  cases run

theorem ExceptNoUnwind.bind {α β : Type} (action : Except SemError α) (next : α → Except SemError β)
    (first : ExceptNoUnwind action) (rest : ∀ value, ExceptNoUnwind (next value)) : ExceptNoUnwind (action >>= next) := by
  intro exception after run
  cases action with
  | error error =>
    change Except.error error = Except.error (SemError.unwinding exception after) at run
    cases run
    exact first exception after rfl
  | ok value => exact rest value exception after run

theorem ExceptNoUnwind.mapM {α β : Type} (items : List α) (action : α → Except SemError β)
    (safe : ∀ item, ExceptNoUnwind (action item)) : ExceptNoUnwind (items.mapM action) := by
  induction items with
  | nil => exact except_ok_no_unwind _
  | cons item rest ih =>
    rw [List.mapM_cons]
    exact ExceptNoUnwind.bind _ _ (safe item) (fun _ => ExceptNoUnwind.bind _ _ ih (fun _ => except_ok_no_unwind _))

theorem char_value_no_unwind (ty : Ty) (value : Value) : ExceptNoUnwind (checkSSACharValue ty value) := by
  unfold checkSSACharValue
  repeat' first
    | exact except_ok_no_unwind _
    | exact except_ub_no_unwind _
    | split

theorem char_values_no_unwind (types : List Ty) (values : List Value) : ExceptNoUnwind (checkSSACharValues types values) := by
  induction types generalizing values with
  | nil => cases values <;> first | exact except_ok_no_unwind _ | exact except_type_no_unwind _
  | cons ty types ih =>
    cases values with
    | nil => exact except_type_no_unwind _
    | cons value values =>
      exact ExceptNoUnwind.bind _ _ (char_value_no_unwind ty value) (fun _ => ih values)

theorem result_source_type_no_unwind (original : Option LocalTypeTable) (source : LocalTypeSource) :
    ExceptNoUnwind (ssaResultSourceType original source) := by
  unfold ssaResultSourceType
  repeat' first
    | exact except_ok_no_unwind _
    | exact except_type_no_unwind _
    | exact except_unsupported_no_unwind _ _
    | split

local macro "pure_validation_leaves" : tactic => `(tactic|
  repeat' first
    | exact except_ok_no_unwind _
    | exact except_type_no_unwind _
    | exact except_unsupported_no_unwind _ _
    | exact result_source_type_no_unwind _ _
    | (refine ExceptNoUnwind.mapM _ _ (fun value => ?_))
    | (refine ExceptNoUnwind.bind _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split)

/-- Original declaration association and header-derived classifications retain
all conflicts and absent-metadata refusals without creating unwind states. -/
theorem instruction_types_no_unwind (original : Option LocalTypeTable)
    (direct : FuncId → Option FuncTyDef) (indirect : FuncTyTable)
    (inst : Inst) (dests : List ValueId) (produced : Nat) :
    ExceptNoUnwind (ssaInstructionResultTypes original direct indirect inst dests produced) := by
  unfold ssaInstructionResultTypes
  pure_validation_leaves

theorem lift_validation_no_unwind {α : Type} (result : Except SemError α) (safe : ExceptNoUnwind result) :
    CallCheckNoUnwind (Sem.fromMemoryExcept result) := by
  intro state exception after run
  cases result with
  | ok value => cases run
  | error error =>
    cases run
    exact safe exception after rfl

/-- Actual result checks do not use the potentially arbitrary functionErrors
field: source types and top-level Char validation have their own no-unwind laws. -/
theorem result_checks_no_unwind (ctx : EvalContext) (inst : Inst) (dests : List ValueId) (values : List Value) :
    CallCheckNoUnwind (ctx.checkInstructionResults inst dests values) := by
  have typesSafe : ExceptNoUnwind (ctx.instructionResultTypes inst dests values.length) := instruction_types_no_unwind _ _ _ _ _ _
  cases types : ctx.instructionResultTypes inst dests values.length with
  | error error =>
    intro state exception after run
    simp only [EvalContext.checkInstructionResults,types] at run
    change Except.error error = Except.error (SemError.unwinding exception after) at run
    cases run
    exact typesSafe exception after types
  | ok resolved =>
    cases chars : checkSSACharValues resolved values with
    | error error =>
      intro state exception after run
      simp only [EvalContext.checkInstructionResults,types,chars,pure_bind] at run
      cases run
      exact char_values_no_unwind resolved values exception after chars
    | ok unit =>
      cases unit
      intro state exception after run
      simp only [EvalContext.checkInstructionResults,types,chars,pure_bind] at run
      cases run

private theorem pure_no_unwind {α : Type} (value : α) : CallCheckNoUnwind (pure value : Sem α) := by
  intro state exception after run
  cases run

private theorem get_no_unwind : CallCheckNoUnwind Sem.getState := by
  intro state exception after run
  cases run

private theorem set_no_unwind (state : MachineState) : CallCheckNoUnwind (Sem.setState state) := by
  intro before exception after run
  cases run

private theorem type_no_unwind {α : Type} (message : String) : CallCheckNoUnwind (Sem.throwTypeError message : Sem α) := by
  intro state exception after run
  cases run

private theorem lookup_no_unwind (id : ValueId) : CallCheckNoUnwind (Sem.lookupValue id) := by
  unfold Sem.lookupValue
  refine CallCheckNoUnwind.bind _ _ get_no_unwind ?_
  intro state
  split <;> first | exact pure_no_unwind _ | exact type_no_unwind _

local macro "publication_leaves" : tactic => `(tactic|
  first
    | exact pure_no_unwind _
    | exact get_no_unwind
    | exact set_no_unwind _
    | exact type_no_unwind _
    | exact lookup_no_unwind _
    | exact lookup_arguments_no_unwind _
    | exact result_checks_no_unwind _ _ _ _
    | (refine CallCheckNoUnwind.bind _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split)

theorem result_dests_no_unwind (dests : List ValueId) (values : List Value) : CallCheckNoUnwind (bindResultDests dests values) := by
  unfold bindResultDests
  repeat' publication_leaves

theorem instruction_dests_no_unwind (result : InstrResult) (dests : List ValueId) :
    CallCheckNoUnwind (bindInstrResultDests result dests) := by
  unfold bindInstrResultDests
  repeat' first
    | exact result_dests_no_unwind _ _
    | publication_leaves
    | split

theorem call_results_no_unwind (ctx : EvalContext) (inst : Inst) (dests : List ValueId) (values : List Value) :
    CallCheckNoUnwind (ctx.bindCallResults inst dests values) := by
  unfold EvalContext.bindCallResults
  split
  · exact result_dests_no_unwind _ _
  · exact CallCheckNoUnwind.bind _ _ (result_checks_no_unwind _ _ _ _) (fun _ => result_dests_no_unwind _ _)

theorem instruction_results_no_unwind (ctx : EvalContext) (inst : Inst) (result : InstrResult) (dests : List ValueId) :
    CallCheckNoUnwind (ctx.bindInstructionResults inst result dests) := by
  unfold EvalContext.bindInstructionResults
  repeat' first
    | exact instruction_dests_no_unwind _ _
    | publication_leaves
    | split

private theorem exit_at_no_unwind {α : Type} (post : Nat → α → Prop) (action : Sem α) (state : MachineState)
    (safe : CallCheckNoUnwind action)
    (success : ∀ after value, Sem.run action state = .ok (value,after) →
      WellMintedState after ∧ post after.nextFrameLineage value ∧ HistoryExtends state after) :
    FrameActionExit post state (Sem.run action state) := by
  cases executed : Sem.run action state with
  | ok pair => exact success pair.2 pair.1 executed
  | error error =>
    cases error <;> first | exact True.intro | exact False.elim (safe state _ _ executed)

theorem result_checks_frame_action (ctx : EvalContext) (inst : Inst) (dests : List ValueId) (values : List Value) :
    FrameActionValid (fun _ _ => True) (ctx.checkInstructionResults inst dests values) := by
  apply frame_action_of_success_no_unwind _ _ (result_checks_no_unwind ctx inst dests values)
  intro state after unit valid run
  cases unit
  have same := result_checks_success_state ctx inst dests values state after run
  subst after
  exact ⟨valid,True.intro,.refl _⟩

theorem result_dests_frame_exit (dests : List ValueId) (values : List Value) (state : MachineState)
    (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage values) :
    FrameActionExit (fun _ _ => True) state (Sem.run (bindResultDests dests values) state) := by
  apply exit_at_no_unwind _ _ _ (result_dests_no_unwind dests values)
  intro after unit run
  cases unit
  exact ⟨valid.bind_result_dests_success dests values state after incoming run,True.intro,
    (result_dests_history dests values).extends state after () run⟩

/-- Full call/Invoke normal-edge publication, consuming original guards. -/
theorem call_results_frame_exit (ctx : EvalContext) (inst : Inst) (dests : List ValueId) (values : List Value)
    (state : MachineState) (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage values) :
    FrameActionExit (fun _ _ => True) state (Sem.run (ctx.bindCallResults inst dests values) state) := by
  apply exit_at_no_unwind _ _ _ (call_results_no_unwind ctx inst dests values)
  intro after unit run
  cases unit
  exact ⟨valid.call_results_success ctx inst dests values state after incoming run,True.intro,
    (call_results_history ctx inst dests values).extends state after () run⟩

/-- Arbitrary original instruction result shapes/destination collisions and
private-SSA retirement preserve state/history through all exits. -/
theorem instruction_results_frame_action (ctx : EvalContext) (inst : Inst) (result : InstrResult) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (ctx.bindInstructionResults inst result dests) := by
  apply frame_action_of_success_no_unwind _ _ (instruction_results_no_unwind ctx inst result dests)
  intro state after unit valid run
  cases unit
  exact ⟨valid.bind_instruction_success ctx inst result dests state after run,True.intro,
    (instruction_results_history ctx inst result dests).extends state after () run⟩

theorem block_params_no_unwind (params : List (ValueId × Ty)) (args : List Value) :
    CallCheckNoUnwind (bindBlockParams params args) := by
  unfold bindBlockParams
  repeat' publication_leaves

theorem checked_params_no_unwind (params : List (ValueId × Ty)) (args : List Value) :
    CallCheckNoUnwind (bindBlockParamsChecked params args) := by
  unfold bindBlockParamsChecked
  split
  · exact block_params_no_unwind _ _
  · cases checked : checkSSACharValues (params.map Prod.snd) args with
    | ok unit => cases unit; exact block_params_no_unwind _ _
    | error error =>
      intro state exception after run
      cases run
      exact char_values_no_unwind _ _ exception after checked

theorem checked_params_frame_exit (params : List (ValueId × Ty)) (args : List Value) (state : MachineState)
    (valid : WellMintedState state) (incoming : MintedArgs state.nextFrameLineage args) :
    FrameActionExit (fun _ _ => True) state (Sem.run (bindBlockParamsChecked params args) state) := by
  apply exit_at_no_unwind _ _ _ (checked_params_no_unwind params args)
  intro after unit run
  cases unit
  exact ⟨valid.checked_params_success params args state after incoming run,True.intro,
    (checked_params_history params args).extends state after () run⟩

end TrustIr.FrameLifetime
