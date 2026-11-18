-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameAggregateDecoding
import TrustIr.Proofs.FrameMemoryLoads

namespace TrustIr.FrameLifetime

/-- Actual prepared services cannot inject an embedded unwind world through
either positive or negative caches, or through a later uncached request. -/
theorem prepared_memory_error_policy (source : SourceLayout.Environment) (roots : List Ty) :
    AggregateMemory.ServiceErrorPolicy BlockDecodeError (AggregateMemory.prepare source roots) :=
  AggregateMemory.prepare_error_policy BlockDecodeError (fun _ => True.intro) (fun _ => True.intro) source roots

private theorem memory_check_frame_action {α : Type} (result : Except SemError α)
    (safe : ExceptNoUnwind result) :
    FrameActionValid (fun _ _ => True) (Sem.fromMemoryExcept result) := by
  intro state valid
  cases result with
  | ok value => exact ⟨valid,True.intro,.refl _⟩
  | error error =>
    cases error <;> first | exact True.intro | exact False.elim (safe _ _ rfl)

private theorem memory_decode_frame_action (result : Except SemError Value)
    (safe : DecodeFrameExit (MintedValue 0) result) :
    FrameActionValid MintedValue (Sem.fromMemoryExcept result) := by
  intro state valid
  cases result with
  | ok value => exact ⟨valid,safe.mono (Nat.zero_le _),.refl _⟩
  | error error => cases error <;> first | exact True.intro | exact False.elim safe

private theorem checked_alignment_no_unwind (natural : Nat) (align : Option Nat) :
    ExceptNoUnwind (checkedMemoryAlign "Load" natural align) := by
  unfold checkedMemoryAlign
  dsimp only
  split <;> intro exception after same <;> cases same

/-- Full held aggregate load, including target mismatch, layout refusals,
pointer checks, partial loads and the actual allocation-specific unwritten
explanation fold. No successful plan or valid-memory premise is assumed. -/
theorem aggregate_load_value_frame_exit (service : AggregateMemory.Service)
    (safe : AggregateMemory.ServiceErrorPolicy BlockDecodeError service)
    (order : FunctionAddressOrder) (ty : Ty) (pointer : Value)
    (strict : Bool) (align : Option Nat) (model : ByteModel) :
    FrameActionValid MintedValue (AggregateMemory.loadValue service order ty pointer strict align model) := by
  intro state valid
  unfold AggregateMemory.loadValue
  have planSafe := AggregateMemory.checkedPlan_errors BlockDecodeError (fun _ => True.intro) service safe model ty
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ state
    (memory_check_frame_action _ (DecodeFrameExit.no_unwind _ _ ((block_result_frame_iff _ _).1 planSafe)) state valid)
  intro plan before beforeValid _
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ before
    (memory_check_frame_action _ (checked_alignment_no_unwind plan.layout.alignment align) before beforeValid)
  intro alignment before beforeValid _
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ before
    (reject_partial_frame_action pointer "Load" before beforeValid)
  intro unit before beforeValid _
  cases unit
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ before
    (expect_pointer_frame_action pointer "Load" before beforeValid)
  intro pair before beforeValid _
  obtain ⟨address,allocation⟩ := pair
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ before
    (checked_access_frame_action "Load" address allocation plan.layout.size alignment model before beforeValid)
  intro address before beforeValid _
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ before
    (show FrameActionExit (fun _ _ => True) before (Sem.run Sem.getState before) from
      ⟨beforeValid,True.intro,.refl _⟩)
  intro snapshot after afterValid _
  dsimp only
  repeat' first
    | (solve | exact memory_decode_frame_action _ (aggregate_decode_frame_exit _ _ _ _ _) after afterValid)
    | (solve | exact memory_decode_frame_action _ (aggregate_unwritten_decode_frame_exit _ _ _ _ _) after afterValid)
    | (solve | exact ⟨afterValid,(mintedValue_iff_shape _ _).2 True.intro,.refl _⟩)
    | (solve | exact True.intro)
    | (refine FrameActionExit.bind (fun _ _ => True) MintedValue _ _ after
        (memory_check_frame_action _ (aggregate_covered_no_unwind _ _) after afterValid) ?_
       intro covered after afterValid _)
    | split
    | (dsimp only; split)

private theorem capture_decode_frame_action (result : Except SemError (List Value))
    (safe : DecodeFrameExit (fun values => ∀ value ∈ values, MintedValue 0 value) result) :
    FrameActionValid (fun bound values => ∀ value ∈ values, MintedValue bound value)
      (Sem.fromMemoryExcept result) := by
  intro state valid
  cases result with
  | ok values =>
    exact ⟨valid, fun value member => (safe value member).mono (Nat.zero_le _), .refl _⟩
  | error error => cases error <;> first | exact True.intro | exact False.elim safe

private theorem original_check_frame_action {α : Type} (result : Except SemError α)
    (safe : ByteImage.BlockResult (fun _ => True) BlockDecodeError result) :
    FrameActionValid (fun _ _ => True) (Sem.fromMemoryExcept result) :=
  memory_check_frame_action result
    (DecodeFrameExit.no_unwind _ _ ((block_result_frame_iff _ _).1 safe))

/-- The new original-source route preserves frame identities through its actual
binding, geometry, capture plans, allocation checks and canonical field decode.
This proves no allocation embedding, callee rely or machine/SP placement. -/
theorem original_closure_load_value_frame_exit (service : OriginalClosureMemory.Service)
    (order : FunctionAddressOrder) (closure : ClosureTyId) (pointer : Value)
    (strict : Bool) (align : Option Nat) (model : ByteModel) :
    FrameActionValid MintedValue
      (OriginalClosureMemory.loadValue service order closure pointer strict align model) := by
  intro state valid
  unfold OriginalClosureMemory.loadValue
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ state
    (original_check_frame_action _
      (OriginalClosureMemory.binding_errors BlockDecodeError (fun _ => True.intro)
        (fun _ => True.intro) service model closure) state valid)
  intro held before beforeValid _
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ before
    (original_check_frame_action _
      (OriginalClosureMemory.layout_errors BlockDecodeError (fun _ => True.intro) _) before beforeValid)
  intro storage before beforeValid _
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ before
    (original_check_frame_action _
      (OriginalClosureMemory.capturePlans_errors BlockDecodeError (fun _ => True.intro)
        (fun _ => True.intro) service _ _ _ _) before beforeValid)
  intro fields before beforeValid _
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ before
    (memory_check_frame_action _ (checked_alignment_no_unwind storage.alignment align) before beforeValid)
  intro alignment before beforeValid _
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ before
    (reject_partial_frame_action pointer "Load" before beforeValid)
  intro unit before beforeValid _
  cases unit
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ before
    (expect_pointer_frame_action pointer "Load" before beforeValid)
  intro pair before beforeValid _
  obtain ⟨address,allocation⟩ := pair
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ before
    (checked_access_frame_action "Load" address allocation storage.size alignment model before beforeValid)
  intro address before beforeValid _
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ before
    (show FrameActionExit (fun _ _ => True) before (Sem.run Sem.getState before) from
      ⟨beforeValid,True.intro,.refl _⟩)
  intro snapshot after afterValid _
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ after
    (memory_check_frame_action _ (closure_capture_covered_no_unwind _ _) after afterValid)
  intro missing after afterValid _
  dsimp only
  split
  · exact True.intro
  · simp only [pure_bind]
    apply FrameActionExit.bind
      (fun bound values => ∀ value ∈ values, MintedValue bound value) MintedValue _ _ after
      (capture_decode_frame_action _ (closure_capture_decode_frame_exit _ _ _ _ _) after afterValid)
    intro captures final finalValid incoming
    exact ⟨finalValid, (mintedValue_iff_shape _ _).2 incoming, .refl _⟩

/-- Every aggregate service selected by this context has a proved static
error policy. Scalar fallback remains covered without a service premise. -/
def MemoryContextErrors (ctx : EvalContext) : Prop :=
  ∀ ty service, ctx.memoryServiceFor ty = some service →
    AggregateMemory.ServiceErrorPolicy BlockDecodeError service

theorem prepared_memory_context_errors (ctx : EvalContext) (source : SourceLayout.Environment)
    (roots : List Ty) (prepared : ctx.memoryService = some (AggregateMemory.prepare source roots)) :
    MemoryContextErrors ctx := by
  intro ty service selected
  unfold EvalContext.memoryServiceFor at selected
  split at selected
  · cases selected
  · rw [prepared] at selected
    cases selected
    exact prepared_memory_error_policy source roots

theorem context_load_aligned_frame_exit (ctx : EvalContext) (safe : MemoryContextErrors ctx)
    (ty : Ty) (pointer : Value) (strict : Bool) (align : Option Nat) :
    FrameActionValid MintedValue (ctx.loadMemoryValueAligned ty pointer strict align) := by
  unfold EvalContext.loadMemoryValueAligned
  cases selected : ctx.memoryRoute ty with
  | scalar => exact scalar_load_value_frame_exit ctx ty pointer strict align
  | descriptor service =>
    exact aggregate_load_value_frame_exit service
      (safe ty service (ctx.memoryRoute_descriptor_source ty service selected)) _ _ _ _ _ _
  | original closure service =>
    exact original_closure_load_value_frame_exit service _ _ _ _ _ _

theorem context_load_value_frame_exit (ctx : EvalContext) (safe : MemoryContextErrors ctx)
    (ty : Ty) (pointer : Value) (strict : Bool) :
    FrameActionValid MintedValue (ctx.loadMemoryValue ty pointer strict) :=
  context_load_aligned_frame_exit ctx safe ty pointer strict none

/-- All actual contextual routes preserve frame identities through the single
fresh SSA publication. No successful lookup or native-memory premise is assumed. -/
theorem context_load_step_frame_exit (ctx : EvalContext) (safe : MemoryContextErrors ctx)
    (ty : Ty) (pointer : ValueId) (strict : Bool) (align : Option Nat) :
    FrameActionValid (fun _ result => BodyValueResult result)
      (stepInstWithContext ctx (.Load ty pointer strict align)) := by
  intro state valid
  simp only [stepInstWithContext,bind_assoc]
  apply FrameActionExit.bind MintedValue (fun _ result => BodyValueResult result) _ _ state
    (lookup_value_frame_action pointer state valid)
  intro pointer before beforeValid _
  apply FrameActionExit.bind MintedValue (fun _ result => BodyValueResult result) _ _ before
    (context_load_aligned_frame_exit ctx safe ty pointer strict align before beforeValid)
  intro value loaded loadedValid incoming
  apply FrameActionExit.bind (fun _ _ => True) (fun _ result => BodyValueResult result) _ _ loaded
    (fresh_minted_frame_exit value loaded loadedValid incoming)
  intro id after afterValid _
  exact ⟨afterValid,True.intro,.refl _⟩

theorem context_load_body_frame_exit (recurse : GenericCoro.Prefix.Recurse) (ctx : EvalContext)
    (safe : MemoryContextErrors ctx) (depth : Nat) (strategy : PanicStrategy)
    (ty : Ty) (pointer : ValueId) (strict : Bool) (align : Option Nat) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True)
      (GenericCoro.Prefix.evalBodyStep recurse ctx depth strategy (.Load ty pointer strict align,dests)) := by
  intro state valid
  apply FrameActionExit.bind (fun _ result => BodyValueResult result) (fun _ _ => True) _ _ state
    (context_load_step_frame_exit ctx safe ty pointer strict align state valid)
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

end TrustIr.FrameLifetime
