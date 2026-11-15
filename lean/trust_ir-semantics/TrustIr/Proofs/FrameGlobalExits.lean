-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameConstantExits
import TrustIr.Proofs.FrameAllocationExits
import TrustIr.Proofs.FrameWorldUpdates

namespace TrustIr.FrameLifetime

private def Observes {α : Type} (action : Sem α) : Prop :=
  CallCheckReadOnly action ∧ CallCheckNoUnwind action

private theorem pure_observes {α : Type} (value : α) : Observes (pure value : Sem α) := by
  constructor
  · intro state pair run; cases run; rfl
  · intro state exception after run; cases run

private theorem throw_observes {α : Type} (error : SemError)
    (safe : ExceptNoUnwind (.error error : Except SemError α)) : Observes (throw error : Sem α) := by
  constructor
  · intro state pair run; cases run
  · intro state exception after run; cases run; exact safe _ _ rfl

private theorem check_observes {α : Type} (result : Except SemError α) (safe : ExceptNoUnwind result) :
    Observes (Sem.fromMemoryExcept result) := by
  cases result with
  | ok value => exact pure_observes value
  | error error => exact throw_observes error safe

private theorem target_observes (model : ByteModel) (address : Nat) :
    Observes (Sem.targetAddress model "GlobalAddr" address) := by
  cases model with
  | le64 => exact pure_observes _
  | le32 =>
    by_cases fits : address < ByteModel.le32.addressLimit
    · simp only [Sem.targetAddress,if_pos fits]; exact pure_observes _
    · simp only [Sem.targetAddress,if_neg fits]
      apply throw_observes; intro exception after same; cases same

private theorem capacity_observes (model : ByteModel) (memory : Memory) (size alignment : Nat) :
    Observes (Sem.checkTargetAllocation model memory size alignment 0) :=
  check_observes _ (word_allocation_no_unwind model memory size alignment 0)


private theorem publish_global_exit (state : MachineState) (valid : WellMintedState state)
    (memory : Memory) (address : Nat) (allocation : AllocId) (global : GlobalId) :
    FrameActionExit (fun _ _ => True) state (Sem.run (do
      Sem.setState {state with
        memory, permissions := state.permissions.set allocation .owned,
        globals := (global,address,allocation) :: state.globals}
      Sem.bindFresh (.ptr address (some allocation))) state) := by
  refine FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state ?_ ?_
  · exact ⟨⟨valid.table,valid.values⟩,True.intro,⟨Nat.le_refl _,fun _ _ closed => closed⟩⟩
  · intro unit state valid _
    cases unit
    exact fresh_minted_frame_exit _ state valid ((mintedValue_iff_shape _ _).2 True.intro)

/-- Scalar materialization preserves all exits, including initializer error
remapping, and retains the allocation snapshot through read-only checks. -/
theorem global_using_frame_exit (encode : Ty → Value → Except SemError (List UInt8))
    (codec : ∀ ty value, ExceptNoUnwind (encode ty value)) (table : GlobalsTable)
    (global : GlobalId) (model : ByteModel) :
    FrameActionValid (fun _ _ => True) (semGlobalAddrUsing encode table global model) := by
  intro state valid
  unfold semGlobalAddrUsing
  apply frame_get_bind_exit
  cases cached : state.lookupGlobal global with
  | some pair =>
    obtain ⟨address, allocation⟩ := pair
    simp only [cached]
    apply frame_readonly_bind_exit _ _ _ state (target_observes model address).1 (target_observes model address).2
    intro address
    exact fresh_minted_frame_exit _ state valid ((mintedValue_iff_shape _ _).2 True.intro)
  | none =>
    simp only [cached]
    cases defined : table global with
    | none => exact True.intro
    | some definition =>
      simp only [defined,pure_bind]
      cases sized : definition.ty.byteSizeFor model with
      | none => exact True.intro
      | some size =>
        simp only [sized,pure_bind]
        apply frame_readonly_bind_exit _ _ _ state (capacity_observes _ _ _ _).1 (capacity_observes _ _ _ _).2
        intro unit
        cases unit
        cases allocated : state.memory.alloc size _ 0 .rustHeap with
        | mk address memory =>
          dsimp only
          cases initialized : definition.initializer with
          | none =>
            simp only [initialized,pure_bind]
            exact publish_global_exit state valid _ _ _ global
          | some constant =>
            simp only [initialized]
            by_cases symbol : constant.hasSymbolAddr = true
            · simp only [symbol,↓reduceIte]; exact True.intro
            · simp only [symbol,↓reduceIte]
              cases converted : constValueAtChecked definition.ty constant model false with
              | error error =>
                simp only [converted]
                cases error <;> first
                  | exact True.intro
                  | exact False.elim (checked_constant_no_unwind _ _ _ _ _ _ converted)
              | ok value =>
                simp only [converted,pure_bind]
                cases encoded : encode definition.ty value with
                | ok bytes =>
                  simp only [encoded]
                  by_cases wrong : (bytes.length != size) = true
                  · simp only [wrong,↓reduceIte]; exact True.intro
                  · simp only [wrong,↓reduceIte,pure_bind]
                    exact publish_global_exit state valid _ _ _ global
                | error error =>
                  try simp only [encoded]
                  cases error <;> repeat' first
                    | contradiction
                    | (solve | exact True.intro)
                    | (solve | simp_all only [Except.error.injEq]; subst_vars; exact True.intro)
                    | (solve | exact False.elim (codec _ _ _ _ encoded))
                    | split
                    | (dsimp only; split)

private theorem global_image_exit (state : MachineState) (valid : WellMintedState state)
    (memory : Memory) (address size : Nat) (allocation : AllocId) (global : GlobalId) (image : ByteImage) :
    FrameActionExit (fun _ _ => True) state (Sem.run (do
      if image.size != size then
        Sem.throwTypeError "GlobalAddr: initializer byte count does not match source layout"
      Sem.setState {state with
        memory := memory.writeImage address image,
        permissions := state.permissions.set allocation .owned,
        globals := (global,address,allocation) :: state.globals}
      Sem.bindFresh (.ptr address (some allocation))) state) := by
  by_cases wrong : (image.size != size) = true
  · simp only [wrong,↓reduceIte]; exact True.intro
  · simp only [wrong,↓reduceIte,pure_bind]
    exact publish_global_exit state valid _ address allocation global

/-- Actual contextual materialization, with the selected service's cache
policy checked and the original cache-hit and initializer orders retained. -/
theorem context_global_frame_exit (ctx : EvalContext) (safe : MemoryContextErrors ctx) (global : GlobalId) :
    FrameActionValid (fun _ _ => True) (semGlobalAddrInContext ctx global) := by
  unfold semGlobalAddrInContext
  cases defined : ctx.globalsTable global with
  | none =>
    simp only [defined]
    cases selected : ctx.memoryService with
    | none =>
      exact global_using_frame_exit _ (encode_functions_no_unwind ctx.byteModel ctx.functionOrder) _ global _
    | some service =>
      intro state valid
      apply frame_get_bind_exit
      cases cached : state.lookupGlobal global with
      | none => simp only [cached,defined]; exact True.intro
      | some pair =>
        obtain ⟨address, allocation⟩ := pair
        simp only [cached]
        apply frame_readonly_bind_exit _ _ _ state (target_observes ctx.byteModel address).1 (target_observes ctx.byteModel address).2
        intro address
        exact fresh_minted_frame_exit _ state valid ((mintedValue_iff_shape _ _).2 True.intro)
  | some definition =>
    simp only [defined]
    cases selected : ctx.memoryServiceFor definition.ty with
    | none => exact global_using_frame_exit _ (encode_functions_no_unwind ctx.byteModel ctx.functionOrder) _ global _
    | some service =>
      have serviceSafe := safe definition.ty service selected
      intro state valid
      apply frame_get_bind_exit
      cases cached : state.lookupGlobal global with
      | some pair =>
        obtain ⟨address, allocation⟩ := pair
        simp only [cached]
        apply frame_readonly_bind_exit _ _ _ state (target_observes ctx.byteModel address).1 (target_observes ctx.byteModel address).2
        intro address
        exact fresh_minted_frame_exit _ state valid ((mintedValue_iff_shape _ _).2 True.intro)
      | none =>
        simp only [cached,defined,pure_bind]
        by_cases mismatch : (service.model != ctx.byteModel) = true
        · simp only [mismatch,↓reduceIte]; exact True.intro
        · simp only [mismatch,↓reduceIte,pure_bind]
          have layoutSafe := DecodeFrameExit.no_unwind _ _ ((block_result_frame_iff _ _).1 (serviceSafe definition.ty).2)
          apply frame_readonly_bind_exit _ _ _ state (check_observes _ layoutSafe).1 (check_observes _ layoutSafe).2
          intro layout
          apply frame_readonly_bind_exit _ _ _ state (capacity_observes _ _ _ _).1 (capacity_observes _ _ _ _).2
          intro unit
          cases unit
          cases allocated : state.memory.alloc layout.size _ 0 .rustHeap with
          | mk address memory =>
            dsimp only
            cases initialized : definition.initializer with
            | none =>
              simp only [initialized,pure_bind]
              exact global_image_exit state valid memory address layout.size _ global _
            | some constant =>
              simp only [initialized]
              by_cases symbol : constant.hasSymbolAddr = true
              · simp only [symbol,↓reduceIte]; exact True.intro
              · simp only [symbol,↓reduceIte]
                have constSafe := context_constant_no_unwind ctx.constantContext definition.ty constant false
                apply frame_readonly_bind_exit _ _ _ state (check_observes _ constSafe).1 (check_observes _ constSafe).2
                intro value
                have planSafe := DecodeFrameExit.no_unwind _ _ ((block_result_frame_iff _ _).1 (serviceSafe definition.ty).1)
                apply frame_readonly_bind_exit _ _ _ state (check_observes _ planSafe).1 (check_observes _ planSafe).2
                intro plan
                have encodedSafe := aggregate_encode_no_unwind ctx.byteModel ctx.functionOrder plan value false
                apply frame_readonly_bind_exit _ _ _ state (check_observes _ encodedSafe).1 (check_observes _ encodedSafe).2
                intro image
                exact global_image_exit state valid memory address layout.size _ global image.zeroUninit

theorem context_global_step_frame_exit (ctx : EvalContext) (safe : MemoryContextErrors ctx) (global : GlobalId) :
    FrameActionValid (fun _ result => BodyValueResult result) (stepInstWithContext ctx (.GlobalAddr global)) := by
  intro state valid
  apply FrameActionExit.bind (fun _ _ => True) (fun _ result => BodyValueResult result) _ _ state
    (context_global_frame_exit ctx safe global state valid)
  intro id state valid _
  exact ⟨valid,True.intro,.refl _⟩

theorem context_global_body_frame_exit (recurse : GenericCoro.Prefix.Recurse) (ctx : EvalContext)
    (safe : MemoryContextErrors ctx) (depth : Nat) (strategy : PanicStrategy) (global : GlobalId) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True)
      (GenericCoro.Prefix.evalBodyStep recurse ctx depth strategy (.GlobalAddr global,dests)) := by
  intro state valid
  apply FrameActionExit.bind (fun _ result => BodyValueResult result) (fun _ _ => True) _ _ state
    (context_global_step_frame_exit ctx safe global state valid)
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
