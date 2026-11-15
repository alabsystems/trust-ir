-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameValueValidity
import TrustIr.Semantics.Eval

namespace TrustIr.FrameLifetime

private theorem run_bind {α β : Type} (action : Sem α) (next : α → Sem β) (state : MachineState) :
    Sem.run (action >>= next) state =
      (Sem.run action state >>= fun pair => Sem.run (next pair.1) pair.2) := rfl

private theorem split_bind_success {α β : Type} (action : Sem α) (next : α → Sem β)
    (s final : MachineState) (result : β)
    (run : Sem.run (action >>= next) s = .ok (result, final)) :
    ∃ value middle, Sem.run action s = .ok (value, middle) ∧
      Sem.run (next value) middle = .ok (result, final) := by
  rw [run_bind] at run
  cases step : Sem.run action s with
  | error error => simp [step, bind, Except.bind] at run
  | ok pair => exact ⟨pair.1, pair.2, rfl, by simpa [step] using run⟩

private theorem lookup_success (s final : MachineState) (id : ValueId) (value : Value)
    (run : Sem.run (Sem.lookupValue id) s = .ok (value, final)) :
    s.lookupValue id = some value ∧ final = s := by
  cases lookup : s.lookupValue id with
  | none =>
    simp [Sem.lookupValue, Sem.run, Sem.getState, Sem.throwTypeError, lookup,
      StateT.run, StateT.bind, StateT.get, StateT.pure, StateT.lift, bind, pure,
      Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at run
  | some held =>
    simp [Sem.lookupValue, Sem.run, Sem.getState, lookup, StateT.run,
      StateT.bind, StateT.get, StateT.pure, bind, pure, Except.bind, Except.pure] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- SSA retirement removes a binding without weakening recursive validity of
any remaining value. Runtime frame history is unchanged. -/
theorem WellMintedState.retire (s : MachineState) (id : ValueId) (valid : WellMintedState s) :
    WellMintedState { s with locals := fun key => if key == id then none else s.locals key } := by
  constructor
  · exact valid.table
  · intro key value lookup
    by_cases same : key = id
    · simp [ValueMap.get, same] at lookup
    · simp [ValueMap.get, same] at lookup
      exact valid.values key value lookup

/-- Exact single-result publication state, including retirement of a distinct
private result and the original destination's allocation cursor. -/
def afterSinglePublication (s : MachineState) (result dest : ValueId) (value : Value) : MachineState :=
  let bound := { s with locals := s.locals.set dest value, nextValueId := max s.nextValueId (dest.index + 1) }
  if result != dest then
    { bound with locals := fun id => if id == result then none else bound.locals id }
  else bound

theorem single_publication_run (s : MachineState) (result dest : ValueId) (value : Value)
    (lookup : s.lookupValue result = some value) :
    Sem.run (bindInstrResultDests (.value (some result)) [dest]) s =
      .ok ((), afterSinglePublication s result dest value) := by
  by_cases same : result = dest
  · subst result
    simp [bindInstrResultDests, bindResultDests, afterSinglePublication,
      Sem.lookupValue, Sem.run, Sem.getState, Sem.setState, lookup,
      StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure, StateT.lift,
      bind, pure, Except.bind, Except.pure]
  · simp [bindInstrResultDests, bindResultDests, afterSinglePublication,
      Sem.lookupValue, Sem.run, Sem.getState, Sem.setState, lookup, same,
      StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure, StateT.lift,
      bind, pure, Except.bind, Except.pure]

theorem WellMintedState.single_publication (s : MachineState) (result dest : ValueId) (value : Value)
    (valid : WellMintedState s) (lookup : s.lookupValue result = some value) :
    WellMintedState (afterSinglePublication s result dest value) := by
  have bound : WellMintedState { s with locals := s.locals.set dest value, nextValueId := max s.nextValueId (dest.index + 1) } :=
    ⟨valid.table, values_set valid.values dest value (valid.values result value lookup)⟩
  unfold afterSinglePublication
  split
  · exact bound.retire _ _
  · exact bound

/-- Production destination/type/Char checks cannot mutate state on success. -/
theorem result_checks_success_state (ctx : EvalContext) (inst : Inst)
    (dests : List ValueId) (values : List Value) (s final : MachineState)
    (run : Sem.run (ctx.checkInstructionResults inst dests values) s = .ok ((), final)) :
    final = s := by
  cases typesEq : ctx.instructionResultTypes inst dests values.length with
  | error error =>
    simp [EvalContext.checkInstructionResults, typesEq, Sem.run,
      StateT.run, StateT.bind, StateT.pure, StateT.lift, bind, pure,
      Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at run
  | ok types =>
    cases chars : checkSSACharValues types values with
    | error error =>
      simp [EvalContext.checkInstructionResults, typesEq, chars, Sem.run,
        StateT.run, StateT.bind, StateT.pure, StateT.lift, bind, pure,
        Except.bind, Except.pure, throw, throwThe, MonadExceptOf.throw] at run
    | ok unit =>
      cases unit
      simpa [EvalContext.checkInstructionResults, typesEq, chars, Sem.run,
        StateT.run, StateT.bind, StateT.pure, StateT.lift, bind, pure,
        Except.bind, Except.pure] using run.symm

private theorem checked_noop_success_state (ctx : EvalContext) (inst : Inst)
    (dests : List ValueId) (values : List Value) (s final : MachineState)
    (run : Sem.run (ctx.checkInstructionResults inst dests values >>= fun _ => pure ()) s =
      .ok ((), final)) : final = s := by
  obtain ⟨unit, middle, checked, tail⟩ := split_bind_success _ _ s final () run
  cases unit
  have same := result_checks_success_state ctx inst dests values s middle checked
  subst middle
  change Except.ok ((), s) = Except.ok ((), final) at tail
  cases tail
  rfl

/-- The actual single/no-result context binder preserves recursive identity
validity on success, including type checks, Char guards and SSA retirement.
No successful destination check is assumed independently of execution. -/
theorem WellMintedState.bind_value_success (ctx : EvalContext) (inst : Inst)
    (result : Option ValueId) (dests : List ValueId) (s final : MachineState)
    (valid : WellMintedState s)
    (run : Sem.run (ctx.bindInstructionResults inst (.value result) dests) s = .ok ((), final)) :
    WellMintedState final := by
  cases result with
  | none =>
    cases dests with
    | nil =>
      have same := checked_noop_success_state ctx inst [] [] s final run
      subst final
      exact valid
    | cons dest rest =>
      simp [EvalContext.bindInstructionResults, bindInstrResultDests,
        Sem.throwTypeError, Sem.run, throw, throwThe, MonadExceptOf.throw,
        StateT.run, StateT.lift, bind, pure, Except.bind, Except.pure] at run
  | some result =>
    cases dests with
    | nil =>
      obtain ⟨value, middle, lookupRun, tail⟩ := split_bind_success (Sem.lookupValue result) _ s final () run
      obtain ⟨_, sameLookup⟩ := lookup_success s middle result value lookupRun
      subst middle
      have same := checked_noop_success_state ctx inst [] [value] s final tail
      subst final
      exact valid
    | cons dest rest =>
      cases rest with
      | nil =>
        obtain ⟨value, middle, lookupRun, tail⟩ := split_bind_success (Sem.lookupValue result) _ s final () run
        obtain ⟨lookup, sameLookup⟩ := lookup_success s middle result value lookupRun
        subst middle
        obtain ⟨unit, checkedState, checked, published⟩ := split_bind_success _ _ s final () tail
        cases unit
        have same := result_checks_success_state ctx inst [dest] [value] s checkedState checked
        subst checkedState
        rw [single_publication_run s result dest value lookup] at published
        cases published
        exact valid.single_publication s result dest value lookup
      | cons next rest =>
        simp [EvalContext.bindInstructionResults, bindInstrResultDests,
          Sem.throwTypeError, Sem.run, throw, throwThe, MonadExceptOf.throw,
          StateT.run, StateT.lift, bind, pure, Except.bind, Except.pure] at run

/-- Incoming/returned values may contain closed handles, but every nested
identity must have already been minted at the current runtime counter. -/
def MintedArgs (bound : Nat) (args : List Value) : Prop :=
  ∀ value ∈ args, MintedValue bound value

/-- A successful ordered lookup list retains state exactly and transports
recursive validity from the actual source SSA values. -/
theorem lookup_args_success (ids : List ValueId) (s final : MachineState) (args : List Value)
    (valid : WellMintedState s)
    (run : Sem.run (ids.mapM Sem.lookupValue) s = .ok (args, final)) :
    final = s ∧ MintedArgs s.nextFrameLineage args := by
  induction ids generalizing s final args with
  | nil =>
    change Except.ok ([], s) = Except.ok (args, final) at run
    cases run
    exact ⟨rfl, fun _ member => nomatch member⟩
  | cons id rest ih =>
    rw [List.mapM_cons] at run
    obtain ⟨head, middle, first, tail⟩ := split_bind_success _ _ s final args run
    obtain ⟨lookup, same⟩ := lookup_success s middle id head first
    subst middle
    obtain ⟨values, after, remaining, finished⟩ := split_bind_success _ _ s final args tail
    obtain ⟨same, minted⟩ := ih s after values valid remaining
    subst after
    change Except.ok (head :: values, s) = Except.ok (args, final) at finished
    have equal := Except.ok.inj finished
    have listEq : head :: values = args := congrArg Prod.fst equal
    have stateEq := congrArg Prod.snd equal
    refine ⟨stateEq.symm, ?_⟩
    rw [← listEq]
    intro value member
    cases member with
    | head => exact valid.values id head lookup
    | tail _ member => exact minted value member


private theorem destination_fold_valid (dests : List ValueId) (args : List Value)
    (bound : Nat) (locals : ValueMap) (valid : MintedValues bound locals)
    (incoming : MintedArgs bound args) :
    MintedValues bound ((dests.zip args).foldl
      (fun locals binding => locals.set binding.1 binding.2) locals) := by
  induction dests generalizing args locals with
  | nil => exact valid
  | cons dest rest ih =>
    cases args with
    | nil => exact valid
    | cons arg args =>
      exact ih args (locals.set dest arg)
        (values_set valid dest arg (incoming arg (.head args)))
        (fun value member => incoming value (.tail arg member))

/-- Actual positional publication preserves recursive frame identities for
arbitrary arity, including repeated and colliding destination ids. -/
theorem WellMintedState.bind_result_dests_success (dests : List ValueId) (args : List Value)
    (s final : MachineState) (valid : WellMintedState s)
    (incoming : MintedArgs s.nextFrameLineage args)
    (run : Sem.run (bindResultDests dests args) s = .ok ((), final)) :
    WellMintedState final := by
  by_cases arity : dests.length = args.length
  · have exactRun : Sem.run (bindResultDests dests args) s = .ok ((),
        { s with
          locals := (dests.zip args).foldl (fun locals binding => locals.set binding.1 binding.2) s.locals
          nextValueId := dests.foldl (fun next dest => max next (dest.index + 1)) s.nextValueId }) := by
      simp [bindResultDests, arity, Sem.run, Sem.getState, Sem.setState,
        StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure, bind, pure, Except.bind, Except.pure]
    rw [exactRun] at run
    cases run
    exact ⟨valid.table, destination_fold_valid dests args _ s.locals valid.values incoming⟩
  · simp [bindResultDests, arity, Sem.throwTypeError, Sem.run,
      StateT.run, StateT.lift, bind, pure, Except.bind, Except.pure,
      throw, throwThe, MonadExceptOf.throw] at run

private theorem retirement_fold_valid (results dests : List ValueId) (bound : Nat)
    (locals : ValueMap) (valid : MintedValues bound locals) :
    MintedValues bound (results.foldl (fun locals tmp =>
      if dests.contains tmp then locals else fun id => if id == tmp then none else locals id) locals) := by
  induction results generalizing locals with
  | nil => exact valid
  | cons tmp rest ih =>
    apply ih
    dsimp only
    split
    · exact valid
    · intro id value lookup
      by_cases same : id = tmp
      · simp [ValueMap.get, same] at lookup
      · simp [ValueMap.get, same] at lookup
        exact valid id value lookup

/-- Multi-result publication looks up every source before writing any destination,
then retires all private sources except those retained as destinations. -/
theorem WellMintedState.bind_values_core_success (results dests : List ValueId)
    (s final : MachineState) (valid : WellMintedState s)
    (run : Sem.run (bindInstrResultDests (.values results) dests) s = .ok ((), final)) :
    WellMintedState final := by
  by_cases arity : dests.length = results.length
  · simp only [bindInstrResultDests, arity, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at run
    obtain ⟨args, middle, looked, tail⟩ := split_bind_success _ _ s final () run
    obtain ⟨same, incoming⟩ := lookup_args_success results s middle args valid looked
    subst middle
    obtain ⟨unit, published, bound, tail⟩ := split_bind_success _ _ s final () tail
    cases unit
    have publishedValid := valid.bind_result_dests_success dests args s published incoming bound
    change Except.ok ((), { published with locals := results.foldl (fun locals tmp =>
      if dests.contains tmp then locals else fun id => if id == tmp then none else locals id) published.locals }) = Except.ok ((), final) at tail
    cases tail
    exact ⟨publishedValid.table, retirement_fold_valid results dests _ _ publishedValid.values⟩
  · simp [bindInstrResultDests, arity, Sem.throwTypeError, Sem.run,
      StateT.run, StateT.lift, bind, pure, Except.bind, Except.pure,
      throw, throwThe, MonadExceptOf.throw] at run

/-- Production metadata and Char checks remain on the original successful path;
no independent check-success or source freshness assumption is required. -/
theorem WellMintedState.bind_values_success (ctx : EvalContext) (inst : Inst)
    (results dests : List ValueId) (s final : MachineState) (valid : WellMintedState s)
    (run : Sem.run (ctx.bindInstructionResults inst (.values results) dests) s = .ok ((), final)) :
    WellMintedState final := by
  by_cases arity : dests.length = results.length
  · simp only [EvalContext.bindInstructionResults, arity, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at run
    obtain ⟨args, middle, looked, tail⟩ := split_bind_success _ _ s final () run
    obtain ⟨same, _⟩ := lookup_args_success results s middle args valid looked
    subst middle
    obtain ⟨unit, checkedState, checked, published⟩ := split_bind_success _ _ s final () tail
    cases unit
    have same := result_checks_success_state ctx inst dests args s checkedState checked
    subst checkedState
    exact valid.bind_values_core_success results dests s final published
  · apply valid.bind_values_core_success results dests s final
    simpa [EvalContext.bindInstructionResults, arity] using run

/-- Every successful body-result publication preserves the identity component
of machine validity. Terminator results are rejected by the production binder. -/
theorem WellMintedState.bind_instruction_success (ctx : EvalContext) (inst : Inst)
    (result : InstrResult) (dests : List ValueId) (s final : MachineState)
    (valid : WellMintedState s)
    (run : Sem.run (ctx.bindInstructionResults inst result dests) s = .ok ((), final)) :
    WellMintedState final := by
  cases result with
  | value result => exact valid.bind_value_success ctx inst result dests s final run
  | values results => exact valid.bind_values_success ctx inst results dests s final run
  | terminator result =>
    simp [EvalContext.bindInstructionResults, bindInstrResultDests, Sem.throwTypeError,
      Sem.run, StateT.run, StateT.lift, throw, throwThe, MonadExceptOf.throw,
      bind, pure, Except.bind, Except.pure] at run

end TrustIr.FrameLifetime
