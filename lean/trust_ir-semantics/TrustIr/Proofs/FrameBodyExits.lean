-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameCastExits

namespace TrustIr.FrameLifetime
open GenericCoro GenericCoro.Prefix NoUnwindEffects

private theorem contextual_frame_state_safe (live : List Nat) (counter : Nat) :
    CallCheckNoUnwind (Sem.setFrameState live counter) := by
  intro state exception after run
  cases run

private theorem contextual_handle_safe (frame : ValueId) (op : String) :
    CallCheckNoUnwind (Sem.frameHandle frame op) := by
  unfold Sem.frameHandle
  refine CallCheckNoUnwind.bind _ _ (lookup_safe frame) (fun value => ?_)
  refine CallCheckNoUnwind.bind _ _ (reject_safe value _) (fun _ => ?_)
  cases value <;> first | exact pure_safe _ | exact type_safe _

local macro "contextual_frame_safety" : tactic => `(tactic|
  repeat' first
    | exact lift_validation_no_unwind _ (binding_frame_types_no_unwind _ _)
    | exact lift_validation_no_unwind _ (function_item_lanes_no_unwind _ _ _ _)
    | exact contextual_handle_safe _ _
    | exact contextual_frame_state_safe _ _
    | exact close_frame_no_unwind _
    | exact lookup_safe _
    | exact reject_safe _ _
    | exact get_safe
    | exact fresh_safe _
    | exact pure_safe _
    | exact type_safe _
    | exact ub_safe _
    | (refine CallCheckNoUnwind.bind _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split)

private theorem checked_fresh_safe (ctx : EvalContext) (ty : Ty) (value : Value) :
    CallCheckNoUnwind (α := InstrResult) (do
      Sem.fromMemoryExcept (checkFunctionItemLanes ctx (value.depth + 1) ty value)
      pure (.value (some (← Sem.bindFresh value)))) :=
  CallCheckNoUnwind.bind _ _
    (lift_validation_no_unwind _ (function_item_lanes_no_unwind ctx _ ty value))
    (fun _ => CallCheckNoUnwind.bind _ _ (fresh_safe value) (fun _ => pure_safe _))

private theorem snapshot_bind_safe (held : Value) (slot : Nat) (value : Value) (message : String) :
    CallCheckNoUnwind (α := InstrResult) (do
      let result ← match bindSlot held slot value with
        | some result => pure result
        | none => Sem.throwUB message
      pure (.value (some (← Sem.bindFresh result)))) := by
  cases found : bindSlot held slot value with
  | none => simp only [found]; exact ub_safe _
  | some result =>
    simp only [found, pure_bind]
    exact CallCheckNoUnwind.bind _ _ (fresh_safe result) (fun _ => pure_safe _)

private theorem checked_bind_safe (ctx : EvalContext) (held : Value) (slot : Nat)
    (ty : Ty) (value : Value) (message : String) :
    CallCheckNoUnwind (α := InstrResult) (do
      Sem.fromMemoryExcept (checkFunctionItemLanes ctx (value.depth + 1) ty value)
      let result ← match bindSlot held slot value with
        | some result => pure result
        | none => Sem.throwUB message
      pure (.value (some (← Sem.bindFresh result)))) :=
  CallCheckNoUnwind.bind _ _
    (lift_validation_no_unwind _ (function_item_lanes_no_unwind ctx _ ty value))
    (fun _ => snapshot_bind_safe held slot value message)

private theorem ordinary_bind_safe (ctx : EvalContext) (held : Value) (slots : List Value)
    (slot : Nat) (rhs : ValueId) :
    CallCheckNoUnwind (α := InstrResult) (do
      let value ← Sem.lookupValue rhs
      if slot < slots.length then
        Sem.fromMemoryExcept (checkFunctionItemLanes ctx (value.depth + 1) .Error value)
        let result ← match bindSlot held slot value with
          | some result => pure result
          | none => Sem.throwUB s!"BindSlot: slot {slot} out of range for frame of {slots.length} slots"
        pure (.value (some (← Sem.bindFresh result)))
      else Sem.throwUB s!"BindSlot: slot {slot} out of range for frame of {slots.length} slots") := by
  refine CallCheckNoUnwind.bind _ _ (lookup_safe rhs) (fun value => ?_)
  split
  · exact checked_bind_safe ctx held slot .Error value _
  · exact ub_safe _

private theorem source_bind_safe (ctx : EvalContext) (held : Value) (slot : Nat) (rhs : ValueId) :
    CallCheckNoUnwind (α := InstrResult) (do
      let types ← Sem.fromMemoryExcept (bindingFrameTypes ctx held)
      let value ← Sem.lookupValue rhs
      let ty ← match trustIrListGet? types slot with
        | some ty => pure ty
        | none => Sem.throwUB "BindSlot: slot out of bounds"
      Sem.fromMemoryExcept (checkFunctionItemLanes ctx (value.depth + 1) ty value)
      let result ← match bindSlot held slot value with
        | some result => pure result
        | none => Sem.throwUB "BindSlot: slot out of bounds"
      pure (.value (some (← Sem.bindFresh result)))) := by
  refine CallCheckNoUnwind.bind _ _
    (lift_validation_no_unwind _ (binding_frame_types_no_unwind ctx held)) (fun types => ?_)
  refine CallCheckNoUnwind.bind _ _ (lookup_safe rhs) (fun value => ?_)
  cases found : trustIrListGet? types slot with
  | none => simp only [found]; exact ub_safe _
  | some ty => simp only [found, pure_bind]; exact checked_bind_safe ctx held slot ty value _

private theorem ordinary_load_safe (ctx : EvalContext) (slots : List Value) (slot : Nat) :
    CallCheckNoUnwind (α := InstrResult) (match trustIrListGet? slots slot with
      | none => Sem.throwUB s!"LoadSlot: slot {slot} out of range for frame of {slots.length} slots"
      | some value => do
        Sem.fromMemoryExcept (checkFunctionItemLanes ctx (value.depth + 1) .Error value)
        pure (.value (some (← Sem.bindFresh value)))) := by
  cases found : trustIrListGet? slots slot with
  | none => exact ub_safe _
  | some value => exact checked_fresh_safe ctx .Error value

private theorem source_load_safe (ctx : EvalContext) (held : Value) (slot : Nat) (ty : Ty) :
    CallCheckNoUnwind (α := InstrResult) (do
      let types ← Sem.fromMemoryExcept (bindingFrameTypes ctx held)
      let declared ← match trustIrListGet? types slot with
        | some declared => pure declared
        | none => Sem.throwUB "LoadSlot: slot out of bounds"
      if !(closureTyEq declared ty) then
        Sem.throwTypeError "LoadSlot: requested type differs from original slot declaration"
      let value ← match loadSlot held slot with
        | some value => pure value
        | none => Sem.throwUB "LoadSlot: slot out of bounds"
      if value.isUninit then
        if isPartialLoadTy ty then
          pure (.value (some (← Sem.bindFresh (.undef ty))))
        else Sem.throwUB (nonpartialUndefMessage ty)
      else
        Sem.fromMemoryExcept (checkFunctionItemLanes ctx (value.depth + 1) ty value)
        pure (.value (some (← Sem.bindFresh value)))) := by
  refine CallCheckNoUnwind.bind _ _
    (lift_validation_no_unwind _ (binding_frame_types_no_unwind ctx held)) (fun types => ?_)
  cases found : trustIrListGet? types slot with
  | none => simp only [found]; exact ub_safe _
  | some declared =>
    simp only [found, pure_bind]
    cases typeEq : closureTyEq declared ty with
    | false =>
      simp only [typeEq, Bool.not_false, ↓reduceIte]
      exact type_safe _
    | true =>
      simp only [typeEq, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
      cases loaded : loadSlot held slot with
      | none => simp only [loaded]; exact ub_safe _
      | some value =>
        simp only [loaded, pure_bind]
        cases unwritten : value.isUninit with
        | false =>
          trustIrCompilerProof { simp only [unwritten, ↓reduceIte] } { skip }
          exact checked_fresh_safe ctx ty value
        | true =>
          simp only [unwritten, ↓reduceIte]
          cases partialTy : isPartialLoadTy ty with
          | false =>
            trustIrCompilerProof { simp only [partialTy, ↓reduceIte] } { skip }
            exact ub_safe _
          | true =>
            simp only [partialTy, ↓reduceIte]
            exact CallCheckNoUnwind.bind _ _ (fresh_safe _) (fun _ => pure_safe _)

set_option smartUnfolding false in
theorem contextual_open_no_unwind (ctx : EvalContext) (definition : BindingFrameDef) :
    CallCheckNoUnwind (stepInstWithContext ctx (.OpenFrame definition)) := by
  cases origin : ctx.currentFunction with
  | none =>
    simp only [stepInstWithContext, origin]
    exact CallCheckNoUnwind.bind _ _ (open_frame_no_unwind definition) (fun _ => pure_safe _)
  | some function =>
    cases found : ctx.valueSource.bindingFrame function definition.id with
    | none =>
      simp only [stepInstWithContext, origin, found]
      exact type_safe _
    | some original =>
      simp only [stepInstWithContext, origin, found, pure_bind]
      split
      · exact type_safe _
      · try simp only [pure_bind]
        refine CallCheckNoUnwind.bind _ _ get_safe (fun state => ?_)
        split
        · refine CallCheckNoUnwind.bind _ _ (contextual_frame_state_safe _ _) (fun _ => ?_)
          exact CallCheckNoUnwind.bind _ _ (fresh_safe _) (fun _ => pure_safe _)
        · exact ub_safe _

set_option smartUnfolding false in
theorem contextual_bind_no_unwind (ctx : EvalContext) (frame : ValueId) (slot : Nat) (value : ValueId) :
    CallCheckNoUnwind (stepInstWithContext ctx (.BindSlot frame slot value)) := by
  unfold stepInstWithContext
  refine CallCheckNoUnwind.bind _ _ (contextual_handle_safe _ _) (fun pair => ?_)
  rcases pair with ⟨lineage, slots⟩
  refine CallCheckNoUnwind.bind _ _ get_safe (fun state => ?_)
  cases live : state.openFrameLineages.contains lineage with
  | false =>
    simp only [live, Bool.not_false, ↓reduceIte]
    exact ub_safe _
  | true =>
    simp only [live, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
    refine CallCheckNoUnwind.bind _ _ (lookup_safe frame) (fun held => ?_)
    cases held
    case frame identity stored => exact ordinary_bind_safe ctx _ slots slot value
    all_goals exact source_bind_safe ctx _ slot value

set_option smartUnfolding false in
theorem contextual_load_no_unwind (ctx : EvalContext) (frame : ValueId) (slot : Nat) (ty : Ty) :
    CallCheckNoUnwind (stepInstWithContext ctx (.LoadSlot frame slot ty)) := by
  unfold stepInstWithContext
  refine CallCheckNoUnwind.bind _ _ (contextual_handle_safe _ _) (fun pair => ?_)
  rcases pair with ⟨lineage, slots⟩
  refine CallCheckNoUnwind.bind _ _ get_safe (fun state => ?_)
  cases live : state.openFrameLineages.contains lineage with
  | false =>
    simp only [live, Bool.not_false, ↓reduceIte]
    exact ub_safe _
  | true =>
    simp only [live, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
    refine CallCheckNoUnwind.bind _ _ (lookup_safe frame) (fun held => ?_)
    cases held
    case frame identity stored => exact ordinary_load_safe ctx slots slot
    all_goals exact source_load_safe ctx _ slot ty

theorem contextual_close_no_unwind (ctx : EvalContext) (frame : ValueId) :
    CallCheckNoUnwind (stepInstWithContext ctx (.CloseFrame frame)) := by
  unfold stepInstWithContext
  contextual_frame_safety

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
  exact contextual_cast_no_unwind ctx op srcTy dstTy operand

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
  exact contextual_open_no_unwind ctx definition

theorem bind_body_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (frame : ValueId) (slot : Nat) (value : ValueId) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (.BindSlot frame slot value,dests)) := by
  apply frame_body_exit_of_no_unwind recurse ctx depth strategy _ (.bind frame slot value) dests
  exact contextual_bind_no_unwind ctx frame slot value

theorem load_body_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (frame : ValueId) (slot : Nat) (ty : Ty) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (.LoadSlot frame slot ty,dests)) := by
  apply frame_body_exit_of_no_unwind recurse ctx depth strategy _ (.load frame slot ty) dests
  exact contextual_load_no_unwind ctx frame slot ty

theorem close_body_exit (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (strategy : PanicStrategy)
    (frame : ValueId) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (evalBodyStep recurse ctx depth strategy (.CloseFrame frame,dests)) := by
  apply frame_body_exit_of_no_unwind recurse ctx depth strategy _ (.close frame) dests
  exact contextual_close_no_unwind ctx frame

end TrustIr.FrameLifetime
