-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.ConstantFrameValues
import TrustIr.Proofs.FrameMemoryLoads

namespace TrustIr.FrameLifetime

theorem checked_constant_decode_exit (ty : Ty) (constant : Constant) (model : ByteModel) (allow : Bool) :
    DecodeFrameExit (MintedValue 0) (constValueAtChecked ty constant model allow) :=
  DecodeFrameExit.of_no_unwind _ _ (checked_constant_no_unwind ty constant model allow)
    (checked_constant_minted ty constant model allow)

theorem context_constant_decode_exit (ctx : ConstantEvalContext) (ty : Ty) (constant : Constant) (allow : Bool) :
    DecodeFrameExit (MintedValue 0) (constValueAtWithDefsIn ctx ty constant allow) :=
  DecodeFrameExit.of_no_unwind _ _ (context_constant_no_unwind ctx ty constant allow)
    (context_constant_minted ctx ty constant allow)

private theorem publish_constant_exit (value : Value) (minted : MintedValue 0 value) :
    FrameActionValid (fun _ result => BodyValueResult result) (do
      let id ← Sem.bindFresh value
      pure (.value (some id))) := by
  intro state valid
  apply FrameActionExit.bind (fun _ _ => True) (fun _ result => BodyValueResult result) _ _ state
    (fresh_minted_frame_exit value state valid (minted.mono (Nat.zero_le _)))
  intro id state valid _
  exact ⟨valid,True.intro,.refl _⟩

/-- Original scalar/inline Const, retaining recursive symbol refusal and the
checked converter's actual result before fresh SSA publication. -/
theorem checked_constant_step_exit (ty : Ty) (constant : Constant) (model : ByteModel) :
    FrameActionValid (fun _ result => BodyValueResult result) (stepInst (.Const ty constant) model) := by
  simp only [stepInst]
  by_cases symbol : constant.hasSymbolAddr = true
  · simp only [symbol,↓reduceIte]; intro state valid; exact True.intro
  · simp only [symbol,↓reduceIte]
    cases converted : constValueAtChecked ty constant model true with
    | error error =>
      intro state valid
      cases error <;> first
        | exact True.intro
        | exact False.elim (checked_constant_no_unwind _ _ _ _ _ _ converted)
    | ok value => exact publish_constant_exit value (checked_constant_minted _ _ _ _ _ converted)

private theorem contextual_constant_action_exit (ctx : EvalContext) (ty : Ty) (constant : Constant) :
    FrameActionValid (fun _ result => BodyValueResult result) (if constant.hasSymbolAddr then
      Sem.throwUnsupported .linkTimeAddress "Const: a link-time symbol address has no compile-time value"
    else match constValueAtWithDefs ctx ty constant with
      | .ok value => do let id ← Sem.bindFresh value; pure (.value (some id))
      | .error error => throw error) := by
  by_cases symbol : constant.hasSymbolAddr = true
  · simp only [symbol,↓reduceIte]; intro state valid; exact True.intro
  · simp only [symbol,↓reduceIte]
    cases converted : constValueAtWithDefsIn ctx.constantContext ty constant true with
    | error error =>
      intro state valid
      simp only [constValueAtWithDefs,converted]
      cases error <;> first
        | exact True.intro
        | exact False.elim (context_constant_no_unwind _ _ _ _ _ _ converted)
    | ok value =>
      simp only [constValueAtWithDefs,converted]
      exact publish_constant_exit value (context_constant_minted _ _ _ _ _ converted)

/-- Every original contextual Const arm, including named aggregates, byte
arrays, compact splats and the checked scalar fallback. -/
theorem context_constant_step_exit (ctx : EvalContext) (ty : Ty) (constant : Constant) :
    FrameActionValid (fun _ result => BodyValueResult result) (stepInstWithContext ctx (.Const ty constant)) := by
  cases constant <;> simp only [stepInstWithContext] <;> first
    | exact contextual_constant_action_exit ctx ty _
    | exact checked_constant_step_exit ty _ ctx.byteModel

theorem context_constant_body_exit (recurse : GenericCoro.Prefix.Recurse) (ctx : EvalContext)
    (depth : Nat) (strategy : PanicStrategy) (ty : Ty) (constant : Constant) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True)
      (GenericCoro.Prefix.evalBodyStep recurse ctx depth strategy (.Const ty constant,dests)) := by
  intro state valid
  apply FrameActionExit.bind (fun _ result => BodyValueResult result) (fun _ _ => True) _ _ state
    (context_constant_step_exit ctx ty constant state valid)
  intro result state valid shape
  cases result with
  | terminator step => cases shape
  | value id =>
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
      (instruction_results_frame_action ctx _ (.value id) dests state valid)
    intro unit state valid _
    cases unit
    exact ⟨valid,True.intro,.refl _⟩
  | values ids =>
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
      (instruction_results_frame_action ctx _ (.values ids) dests state valid)
    intro unit state valid _
    cases unit
    exact ⟨valid,True.intro,.refl _⟩

end TrustIr.FrameLifetime
