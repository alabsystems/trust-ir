-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameCastExits

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix NoUnwindEffects

/-- Upgrade the original successful instruction law only after establishing
that its actual contextual primitive cannot manufacture an unwind state. -/
theorem frame_step_exit_of_no_unwind (ctx : EvalContext) (inst : Inst) (site : FrameInstruction inst)
    (safe : CallCheckNoUnwind (stepInstWithContext ctx inst)) :
    FrameActionValid (fun _ result => BodyValueResult result) (stepInstWithContext ctx inst) := by
  apply frame_action_of_success_no_unwind _ _ safe
  intro state after result valid run
  obtain ⟨shape,preserved⟩ := valid.frame_step_success ctx inst site state after result run
  exact ⟨preserved,shape,frame_step_history ctx inst site state after result run⟩

/-- Full exits through original body stepping and actual SSA publication.
The no-unwind obligation applies to the contextual primitive, not to an
independently assumed successful check or a fabricated intermediate state. -/
theorem frame_body_exit_of_no_unwind (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (inst : Inst) (site : FrameInstruction inst) (dests : List ValueId)
    (safe : CallCheckNoUnwind (stepInstWithContext ctx inst)) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (inst,dests)) := by
  intro state valid
  cases stepped : Sem.run (stepInstWithContext ctx inst) state with
  | error error =>
    rw [frame_body_error recurse ctx depth strategy inst site dests state error stepped]
    cases error <;> first
      | exact True.intro
      | exact False.elim (safe state _ _ stepped)
  | ok pair =>
    obtain ⟨result,after⟩ := pair
    obtain ⟨shape,preserved⟩ := valid.frame_step_success ctx inst site state after result stepped
    rw [frame_body_computed recurse ctx depth strategy inst site dests state after result shape stepped]
    apply FrameActionExit.history (fun _ _ => True) state after _ (frame_step_history ctx inst site state after result stepped)
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ after
      (instruction_results_frame_action ctx inst result dests after preserved)
    intro unit published publishedValid _
    cases unit
    exact ⟨publishedValid,True.intro,.refl _⟩

/-- Full exits compose through actual forIn traversal, including an early done
or an embedded unwind from the selected body action. Only list members need
contracts, and each action is checked at its actual predecessor state. -/
theorem FrameActionValid.forIn {α β : Type} (items : List α) (initial : β)
    (action : α → β → Sem (ForInStep β))
    (exits : ∀ item ∈ items, ∀ value, FrameActionValid (fun _ _ => True) (action item value)) :
    FrameActionValid (fun _ _ => True) (forIn items initial action) := by
  induction items generalizing initial with
  | nil => intro state valid; exact ⟨valid,True.intro,.refl _⟩
  | cons item rest ih =>
    rw [List.forIn_cons]
    intro state valid
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
      (exits item ((trustIrListMemConsSelf _ _)) initial state valid)
    intro step before beforeValid _
    cases step with
    | done value => exact ⟨beforeValid,True.intro,.refl _⟩
    | yield value =>
      exact ih value (fun item member => exits item (List.mem_cons_of_mem _ member)) before beforeValid

theorem frame_body_list_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (rows : List (Inst × List ValueId))
    (exits : ∀ row ∈ rows, FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy row)) :
    FrameActionValid (fun _ _ => True) (evalBody recurse ctx depth strategy rows) :=
  FrameActionValid.forIn rows () _ (fun row member _ => exits row member)

theorem unary_body_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (op : UnOp) (ty : Ty) (operand : ValueId) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (.UnOp op ty operand,dests)) := by
  apply frame_body_exit_of_no_unwind recurse ctx depth strategy _ (.unary op ty operand) dests
  exact CallCheckNoUnwind.bind _ _ (unary_action_no_unwind op ty operand) (fun _ => pure_safe _)

theorem binary_body_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (op : BinOp) (ty : Ty) (left right : ValueId) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (.BinOp op ty left right,dests)) := by
  apply frame_body_exit_of_no_unwind recurse ctx depth strategy _ (.binary op ty left right) dests
  rw [binary_step_eq]
  apply CallCheckNoUnwind.bind
  · unfold binaryAction
    split
    · exact boolean_action_no_unwind op left right
    · exact binary_action_no_unwind op ty left right
  · intro _
    exact pure_safe _

theorem overflow_body_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (op : OverflowOp) (ty : Ty) (left right : ValueId) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (.Overflow op ty left right,dests)) := by
  apply frame_body_exit_of_no_unwind recurse ctx depth strategy _ (.overflow op ty left right) dests
  exact CallCheckNoUnwind.bind _ _ (overflow_action_no_unwind op ty left right) (fun _ => pure_safe _)

theorem integer_compare_body_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (op : ICmpOp) (ty : Ty) (left right : ValueId) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (.ICmp op ty left right,dests)) := by
  apply frame_body_exit_of_no_unwind recurse ctx depth strategy _ (.icmp op ty left right) dests
  exact CallCheckNoUnwind.bind _ _ (integer_compare_action_no_unwind op ty left right ctx.byteModel) (fun _ => pure_safe _)

theorem float_compare_body_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (op : FCmpOp) (ty : Ty) (left right : ValueId) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (.FCmp op ty left right,dests)) := by
  apply frame_body_exit_of_no_unwind recurse ctx depth strategy _ (.fcmp op ty left right) dests
  exact CallCheckNoUnwind.bind _ _ (float_compare_action_no_unwind op ty left right) (fun _ => pure_safe _)

theorem cast_body_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (op : CastOp) (srcTy dstTy : Ty) (operand : ValueId) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (.Cast op srcTy dstTy operand,dests)) := by
  apply frame_body_exit_of_no_unwind recurse ctx depth strategy _ (.cast op srcTy dstTy operand) dests
  exact CallCheckNoUnwind.bind _ _ (semCast_no_unwind op srcTy dstTy operand ctx.byteModel) (fun _ => pure_safe _)

theorem copy_body_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (ty : Ty) (operand : ValueId) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (.Copy ty operand,dests)) := by
  apply frame_body_exit_of_no_unwind recurse ctx depth strategy _ (.copy ty operand) dests
  exact CallCheckNoUnwind.bind _ _ (lookup_safe operand) (fun value =>
    CallCheckNoUnwind.bind _ _ (fresh_safe value) (fun _ => pure_safe _))

theorem null_body_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (.NullPtr,dests)) := by
  apply frame_body_exit_of_no_unwind recurse ctx depth strategy _ .null dests
  exact CallCheckNoUnwind.bind _ _ (fresh_safe .nullPtr) (fun _ => pure_safe _)

theorem undef_body_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (ty : Ty) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (.Undef ty,dests)) := by
  apply frame_body_exit_of_no_unwind recurse ctx depth strategy _ (.undef ty) dests
  change CallCheckNoUnwind (if isPartialLoadTy ty then (do
    let id ← Sem.bindFresh (.undef ty)
    pure (InstrResult.value (some id))) else Sem.throwUB (nonpartialUndefMessage ty))
  split
  · exact CallCheckNoUnwind.bind _ _ (fresh_safe _) (fun _ => pure_safe _)
  · exact ub_safe _


theorem open_body_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (definition : BindingFrameDef) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (.OpenFrame definition,dests)) := by
  apply frame_body_exit_of_no_unwind recurse ctx depth strategy _ (.open definition) dests
  exact CallCheckNoUnwind.bind _ _ (open_frame_no_unwind definition) (fun _ => pure_safe _)

theorem bind_body_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (frame : ValueId) (slot : Nat) (value : ValueId) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (.BindSlot frame slot value,dests)) := by
  apply frame_body_exit_of_no_unwind recurse ctx depth strategy _ (.bind frame slot value) dests
  exact CallCheckNoUnwind.bind _ _ (bind_slot_no_unwind frame slot value) (fun _ => pure_safe _)

theorem load_body_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (frame : ValueId) (slot : Nat) (ty : Ty) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (.LoadSlot frame slot ty,dests)) := by
  apply frame_body_exit_of_no_unwind recurse ctx depth strategy _ (.load frame slot ty) dests
  exact CallCheckNoUnwind.bind _ _ (load_slot_no_unwind frame slot ty) (fun _ => pure_safe _)

theorem close_body_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (frame : ValueId) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (.CloseFrame frame,dests)) := by
  apply frame_body_exit_of_no_unwind recurse ctx depth strategy _ (.close frame) dests
  exact CallCheckNoUnwind.bind _ _ (close_frame_no_unwind frame) (fun _ => pure_safe _)

end TrustIr.FrameLifetime
