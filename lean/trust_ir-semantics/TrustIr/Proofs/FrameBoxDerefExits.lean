-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameMemoryLoads

namespace TrustIr.FrameLifetime

/-- A guard that neither changes the state nor raises keeps the mintedness of
a value the caller already holds. -/
private theorem guard_keeps_minted {α : Type} (action : Sem α)
    (observed : CallCheckReadOnly action ∧ CallCheckNoUnwind action)
    (held : Value) (state : MachineState) (valid : WellMintedState state)
    (minted : MintedValue state.nextFrameLineage held) :
    FrameActionExit (fun bound _ => MintedValue bound held) state (Sem.run action state) := by
  cases executed : Sem.run action state with
  | ok pair =>
    obtain ⟨result,after⟩ := pair
    have same := observed.1 state (result,after) executed
    change after = state at same
    subst after
    exact ⟨valid,minted,.refl _⟩
  | error error =>
    cases error <;> first | exact True.intro | exact False.elim (observed.2 state _ _ executed)

/-- Publishing an already minted value as a fresh SSA result. -/
private theorem publish_minted_frame_exit (value : Value) (state : MachineState)
    (valid : WellMintedState state) (minted : MintedValue state.nextFrameLineage value) :
    FrameActionExit (fun _ result => BodyValueResult result) state
      (Sem.run (Sem.bindFresh value >>= fun id => pure (InstrResult.value (some id))) state) := by
  apply FrameActionExit.bind (fun _ _ => True) (fun _ result => BodyValueResult result) _ _ state
    (fresh_minted_frame_exit value state valid minted)
  intro id after afterValid _
  exact ⟨afterValid,True.intro,.refl _⟩

/-- The Box-deref rule on a held operand. Every guard keeps its original
order and its original error; a defined step publishes the operand pointer
itself, so the result is exactly as minted as the operand was. No memory
validity premise is needed: an invalid Box pointer takes its actual error. -/
theorem box_deref_value_frame_exit (pointee : BoxPointee) (value : Value) (model : ByteModel)
    (state : MachineState) (valid : WellMintedState state)
    (minted : MintedValue state.nextFrameLineage value) :
    FrameActionExit (fun _ result => BodyValueResult result) state
      (Sem.run (semBoxDeref pointee value model) state) := by
  cases pointee with
  | sized ty =>
    unfold semBoxDeref
    dsimp only
    cases ty.byteSizeFor model with
    | none => exact True.intro
    | some size =>
      dsimp only
      apply FrameActionExit.bind (fun bound _ => MintedValue bound value)
        (fun _ result => BodyValueResult result) _ _ state
        (guard_keeps_minted _ (access_align_observed "BoxDeref" ty none model) value state valid minted)
      intro align aligned alignedValid kept
      apply FrameActionExit.bind (fun bound _ => MintedValue bound value)
        (fun _ result => BodyValueResult result) _ _ aligned
        (guard_keeps_minted _ (reject_partial_observed value "BoxDeref") value aligned alignedValid kept)
      intro unit guarded guardedValid kept
      cases unit
      cases value with
      | ptr addr prov =>
        dsimp only
        split
        · exact True.intro
        · split
          · exact True.intro
          · split
            · exact publish_minted_frame_exit _ guarded guardedValid kept
            · cases prov with
              | none => exact True.intro
              | some id =>
                dsimp only
                apply FrameActionExit.bind (fun bound _ => MintedValue bound (.ptr addr (some id)))
                  (fun _ result => BodyValueResult result) _ _ guarded
                  (guard_keeps_minted _
                    (checked_access_observed "BoxDeref: Dereferenceable is false" addr id size align model)
                    _ guarded guardedValid kept)
                intro _ accessed accessedValid kept
                exact publish_minted_frame_exit _ accessed accessedValid kept
      | _ => exact True.intro

/-- Actual SSA publication of a Box deref in every context: the carried
validity fact is not an input of the step. -/
theorem box_deref_step_frame_exit (ctx : EvalContext) (ptrTy : Ty) (pointee : BoxPointee)
    (operand : ValueId) (fact : BoxValidityFact) :
    FrameActionValid (fun _ result => BodyValueResult result)
      (stepInstWithContext ctx (.BoxDeref ptrTy pointee operand fact)) := by
  intro state valid
  simp only [stepInstWithContext,stepInst]
  apply FrameActionExit.bind MintedValue (fun _ result => BodyValueResult result) _ _ state
    (lookup_value_frame_action operand state valid)
  intro value before beforeValid minted
  exact box_deref_value_frame_exit pointee value ctx.byteModel before beforeValid minted

theorem box_deref_body_frame_exit (recurse : GenericCoro.Prefix.Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (ptrTy : Ty) (pointee : BoxPointee) (operand : ValueId)
    (fact : BoxValidityFact) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True)
      (GenericCoro.Prefix.evalBodyStep recurse ctx depth strategy (.BoxDeref ptrTy pointee operand fact,dests)) := by
  intro state valid
  apply FrameActionExit.bind (fun _ result => BodyValueResult result) (fun _ _ => True) _ _ state
    (box_deref_step_frame_exit ctx ptrTy pointee operand fact state valid)
  intro result stepped steppedValid shape
  cases result with
  | terminator step => cases shape
  | value id =>
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ stepped
      (instruction_results_frame_action ctx (.BoxDeref ptrTy pointee operand fact) (.value id) dests stepped steppedValid)
    intro unit after afterValid _
    cases unit
    exact ⟨afterValid,True.intro,.refl _⟩
  | values ids =>
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ stepped
      (instruction_results_frame_action ctx (.BoxDeref ptrTy pointee operand fact) (.values ids) dests stepped steppedValid)
    intro unit after afterValid _
    cases unit
    exact ⟨afterValid,True.intro,.refl _⟩

end TrustIr.FrameLifetime
