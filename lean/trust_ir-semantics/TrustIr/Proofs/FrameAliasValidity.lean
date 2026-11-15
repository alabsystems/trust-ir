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

/-- Fresh SSA binding transports a recursively valid value unchanged. -/
theorem WellMintedState.fresh_success (s final : MachineState) (value : Value) (id : ValueId)
    (valid : WellMintedState s) (operand : MintedValue s.nextFrameLineage value)
    (run : Sem.run (Sem.bindFresh value) s = .ok (id, final)) : WellMintedState final := by
  have exactRun : Sem.run (Sem.bindFresh value) s = .ok (s.bindValue value) := rfl
  rw [exactRun] at run
  cases run
  exact ⟨valid.table, values_set valid.values _ value operand⟩

private theorem fresh_publication_success (s final : MachineState) (value : Value) (result : InstrResult)
    (valid : WellMintedState s) (operand : MintedValue s.nextFrameLineage value)
    (run : Sem.run (Sem.bindFresh value >>= fun id => pure (.value (some id))) s = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  obtain ⟨id, middle, fresh, tail⟩ := split_bind_success _ _ s final result run
  change Except.ok (.value (some id), middle) = Except.ok (result, final) at tail
  cases tail
  exact ⟨id, rfl, WellMintedState.fresh_success s final value id valid operand fresh⟩

private theorem lookup_publication_success (operand : ValueId) (s final : MachineState)
    (result : InstrResult) (valid : WellMintedState s)
    (run : Sem.run (do
      let value ← Sem.lookupValue operand
      let id ← Sem.bindFresh value
      pure (.value (some id))) s = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  obtain ⟨value, middle, looked, tail⟩ := split_bind_success _ _ s final result run
  obtain ⟨lookup, same⟩ := lookup_success s middle operand value looked
  subst middle
  exact fresh_publication_success s final value result valid (valid.values operand value lookup) tail

/-- Copy preserves all nested snapshot identities, including closed handles
and poison transports; its nominal type does not inspect the copied value. -/
theorem WellMintedState.copy_step_success (ctx : EvalContext) (ty : Ty) (operand : ValueId)
    (s final : MachineState) (result : InstrResult) (valid : WellMintedState s)
    (run : Sem.run (stepInstWithContext ctx (.Copy ty operand)) s = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final :=
  lookup_publication_success operand s final result valid run

/-- Lane selection preserves recursive validity without assuming a scalar
lane type: every successful lane is transported from one of the two arms. -/
theorem select_lanes_minted (bound : Nat) (mask left right output : List Value)
    (leftValid : ∀ value ∈ left, MintedValue bound value)
    (rightValid : ∀ value ∈ right, MintedValue bound value)
    (run : semVectorSelectLanes mask left right = .ok output) :
    ∀ value ∈ output, MintedValue bound value := by
  induction mask generalizing left right output with
  | nil =>
    cases left <;> cases right <;> simp [semVectorSelectLanes] at run
    cases run
    intro value member
    cases member
  | cons condition rest ih =>
    cases left with
    | nil => simp [semVectorSelectLanes] at run
    | cons first left =>
      cases right with
      | nil => simp [semVectorSelectLanes] at run
      | cons second right =>
        cases condition with
        | bool bit =>
          cases bit
          · cases computed : semVectorSelectLanes rest left right with
            | error error => simp [semVectorSelectLanes, computed, bind, Except.bind] at run
            | ok remaining =>
              simp [semVectorSelectLanes, computed, bind, pure, Except.bind, Except.pure] at run
              cases run
              intro value member
              cases member with
              | head => exact rightValid second (.head right)
              | tail _ member =>
                exact ih left right remaining
                  (fun value member => leftValid value (.tail first member))
                  (fun value member => rightValid value (.tail second member)) computed value member
          · cases computed : semVectorSelectLanes rest left right with
            | error error => simp [semVectorSelectLanes, computed, bind, Except.bind] at run
            | ok remaining =>
              simp [semVectorSelectLanes, computed, bind, pure, Except.bind, Except.pure] at run
              cases run
              intro value member
              cases member with
              | head => exact leftValid first (.head left)
              | tail _ member =>
                exact ih left right remaining
                  (fun value member => leftValid value (.tail first member))
                  (fun value member => rightValid value (.tail second member)) computed value member
        | int _ _ => simp [semVectorSelectLanes] at run
        | float _ => simp [semVectorSelectLanes] at run
        | ptr _ _ => simp [semVectorSelectLanes] at run
        | array _ => simp [semVectorSelectLanes] at run
        | aggregate _ => simp [semVectorSelectLanes] at run
        | vector _ => simp [semVectorSelectLanes] at run
        | frame _ _ => simp [semVectorSelectLanes] at run
        | set _ => simp [semVectorSelectLanes] at run
        | sequence _ => simp [semVectorSelectLanes] at run
        | record _ => simp [semVectorSelectLanes] at run
        | closure _ _ => simp [semVectorSelectLanes] at run
        | fnDef _ _ => simp [semVectorSelectLanes] at run
        | typedClosure _ _ _ => simp [semVectorSelectLanes] at run
        | fatPtr _ _ _ => simp [semVectorSelectLanes] at run
        | «partial» _ => simp [semVectorSelectLanes] at run
        | undef _ => simp [semVectorSelectLanes] at run
        | nullPtr  => simp [semVectorSelectLanes] at run
        | uninit  => simp [semVectorSelectLanes] at run

private theorem except_success {α β : Type} (action : Except SemError α)
    (next : α → Except SemError β) (result : β)
    (run : (action >>= next) = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases step : action with
  | error error => simp [step, bind, Except.bind] at run
  | ok value => exact ⟨value, rfl, by simpa [step] using run⟩

/-- Successful vector selection inherits recursive validity from its actual
arms while retaining all original shape, poison and lane checks. -/
theorem vector_select_minted (bound : Nat) (ty : Ty) (mask : List Value)
    (left right result : Value) (leftValid : MintedValue bound left)
    (rightValid : MintedValue bound right)
    (run : semVectorSelectValues ty mask left right = .ok result) : MintedValue bound result := by
  unfold semVectorSelectValues at run
  cases ty <;> try { simp [throw, throwThe, MonadExceptOf.throw] at run }
  case Vector count elemTy =>
    obtain ⟨unit, _, tail⟩ := except_success (checkVectorShape count .Bool mask) _ result run
    cases unit
    cases poison : left.isPoison || left.isUninit || right.isPoison || right.isUninit with
    | true => simp [poison, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at tail
    | false =>
      simp only [poison, Bool.false_eq_true, if_false] at tail
      cases left <;> try { simp [throw, throwThe, MonadExceptOf.throw] at tail }
      case vector left =>
        cases right <;> try { simp [throw, throwThe, MonadExceptOf.throw] at tail }
        case vector right =>
          obtain ⟨unit, _, tail⟩ := except_success (checkVectorShape count elemTy left) _ result tail
          cases unit
          obtain ⟨unit, _, tail⟩ := except_success (checkVectorShape count elemTy right) _ result tail
          cases unit
          obtain ⟨unit, _, tail⟩ := except_success (checkVectorLanes elemTy true left) _ result tail
          cases unit
          obtain ⟨unit, _, tail⟩ := except_success (checkVectorLanes elemTy true right) _ result tail
          cases unit
          obtain ⟨output, selected, finished⟩ := except_success (semVectorSelectLanes mask left right) _ result tail
          change Except.ok (.vector output) = Except.ok result at finished
          cases finished
          apply (mintedValue_iff_shape bound (.vector output)).2
          exact select_lanes_minted bound mask left right output
            ((mintedValue_iff_shape bound (.vector left)).1 leftValid)
            ((mintedValue_iff_shape bound (.vector right)).1 rightValid) selected

/-- The original Select arm transport, factored only for its preservation
proof. The enclosing step equality retains the original condition guard. -/
def selectTransport (ty : Ty) (condition : Value) (yes no : ValueId) : Sem Value :=
  match condition with
  | .bool true => Sem.lookupValue yes
  | .bool false => Sem.lookupValue no
  | .vector mask => do
    let left ← Sem.lookupValue yes
    let right ← Sem.lookupValue no
    match semVectorSelectValues ty mask left right with
    | .ok result => pure result
    | .error error => throw error
  | _ => Sem.throwTypeError "Select: condition is not bool"

theorem select_step_eq (ctx : EvalContext) (ty : Ty) (condition yes no : ValueId) :
    stepInstWithContext ctx (.Select ty condition yes no) = (do
      let value ← Sem.lookupValue condition
      Sem.rejectPartial value "Select"
      let chosen ← selectTransport ty value yes no
      let id ← Sem.bindFresh chosen
      pure (.value (some id))) := by
  change (do
    let value ← Sem.lookupValue condition
    Sem.rejectPartial value "Select"
    let chosen ← match value with
      | .bool true => Sem.lookupValue yes
      | .bool false => Sem.lookupValue no
      | .vector mask => do
        let left ← Sem.lookupValue yes
        let right ← Sem.lookupValue no
        match semVectorSelectValues ty mask left right with
        | .ok result => pure result
        | .error error => throw error
      | _ => Sem.throwTypeError "Select: condition is not bool"
    let id ← Sem.bindFresh chosen
    pure (InstrResult.value (some id))) = _
  apply congrArg (fun next : Value → Sem InstrResult => Sem.lookupValue condition >>= next)
  funext value
  apply congrArg (fun next : Unit → Sem InstrResult => Sem.rejectPartial value "Select" >>= next)
  funext unit
  cases value <;> try rfl
  case bool bit => cases bit <;> rfl
  case vector mask =>
    simp only [selectTransport, bind_assoc]
    apply congrArg (fun next : Value → Sem InstrResult => Sem.lookupValue yes >>= next)
    funext left
    apply congrArg (fun next : Value → Sem InstrResult => Sem.lookupValue no >>= next)
    funext right
    cases semVectorSelectValues ty mask left right <;> rfl

theorem select_transport_success (ty : Ty) (condition : Value) (yes no : ValueId)
    (s final : MachineState) (result : Value) (valid : WellMintedState s)
    (run : Sem.run (selectTransport ty condition yes no) s = .ok (result, final)) :
    final = s ∧ MintedValue s.nextFrameLineage result := by
  cases condition with
  | bool bit =>
    cases bit
    · obtain ⟨lookup, same⟩ := lookup_success s final no result run
      exact ⟨same, valid.values no result lookup⟩
    · obtain ⟨lookup, same⟩ := lookup_success s final yes result run
      exact ⟨same, valid.values yes result lookup⟩
  | vector mask =>
    obtain ⟨left, middle, lookedLeft, tail1⟩ := split_bind_success (Sem.lookupValue yes) _ s final result run
    obtain ⟨leftLookup, same⟩ := lookup_success s middle yes left lookedLeft
    subst middle
    obtain ⟨right, middle, lookedRight, tail2⟩ := split_bind_success (Sem.lookupValue no) _ s final result tail1
    obtain ⟨rightLookup, same⟩ := lookup_success s middle no right lookedRight
    subst middle
    cases computed : semVectorSelectValues ty mask left right with
    | error error =>
      simp [computed, Sem.run, StateT.run, StateT.lift,
        throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at tail2
    | ok chosen =>
      have finished : (Except.ok (chosen, s) : Except SemError (Value × MachineState)) = Except.ok (result, final) := by
        simpa [computed, Sem.run_pure] using tail2
      have equal := Except.ok.inj finished
      have resultEq : chosen = result := congrArg Prod.fst equal
      have stateEq : s = final := congrArg Prod.snd equal
      exact ⟨stateEq.symm, resultEq ▸ vector_select_minted s.nextFrameLineage ty mask left right chosen
        (valid.values yes left leftLookup) (valid.values no right rightLookup) computed⟩
  | int _ _ =>
    simp [selectTransport, Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run
  | float _ =>
    simp [selectTransport, Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run
  | ptr _ _ =>
    simp [selectTransport, Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run
  | array _ =>
    simp [selectTransport, Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run
  | aggregate _ =>
    simp [selectTransport, Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run
  | frame _ _ =>
    simp [selectTransport, Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run
  | set _ =>
    simp [selectTransport, Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run
  | sequence _ =>
    simp [selectTransport, Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run
  | record _ =>
    simp [selectTransport, Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run
  | closure _ _ =>
    simp [selectTransport, Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run
  | fnDef _ _ =>
    simp [selectTransport, Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run
  | typedClosure _ _ _ =>
    simp [selectTransport, Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run
  | fatPtr _ _ _ =>
    simp [selectTransport, Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run
  | «partial» _ =>
    simp [selectTransport, Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run
  | undef _ =>
    simp [selectTransport, Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run
  | nullPtr  =>
    simp [selectTransport, Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run
  | uninit  =>
    simp [selectTransport, Sem.throwTypeError, Sem.run, StateT.run, StateT.lift,
      throw, throwThe, MonadExceptOf.throw, bind, pure, Except.bind, Except.pure] at run

private theorem reject_success_state (value : Value) (s final : MachineState)
    (run : Sem.run (Sem.rejectPartial value "Select") s = .ok ((), final)) : final = s := by
  cases value <;>
    simp [Sem.rejectPartial, Sem.run, Sem.throwUB, StateT.run, StateT.pure,
      StateT.lift, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      bind, Except.bind] at run <;> exact run.symm

/-- The complete scalar AND vector Select step preserves recursive identities,
retaining poison/shape checks and scalar selected-arm laziness. -/
theorem WellMintedState.select_step_success (ctx : EvalContext) (ty : Ty) (condition yes no : ValueId)
    (s final : MachineState) (result : InstrResult) (valid : WellMintedState s)
    (run : Sem.run (stepInstWithContext ctx (.Select ty condition yes no)) s = .ok (result, final)) :
    ∃ id, result = .value (some id) ∧ WellMintedState final := by
  rw [select_step_eq] at run
  obtain ⟨value, middle, looked, tail1⟩ := split_bind_success _ _ s final result run
  obtain ⟨_, same⟩ := lookup_success s middle condition value looked
  subst middle
  obtain ⟨unit, middle, guarded, tail2⟩ := split_bind_success _ _ s final result tail1
  cases unit
  have same := reject_success_state value s middle guarded
  subst middle
  obtain ⟨chosen, middle, selected, tail3⟩ := split_bind_success _ _ s final result tail2
  obtain ⟨same, minted⟩ := select_transport_success ty value yes no s middle chosen valid selected
  subst middle
  exact fresh_publication_success s final chosen result valid minted tail3

end TrustIr.FrameLifetime

