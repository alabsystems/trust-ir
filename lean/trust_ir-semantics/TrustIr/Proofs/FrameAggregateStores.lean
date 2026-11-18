-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameMemoryEncoding
import TrustIr.Proofs.FrameAggregateLoads

namespace TrustIr.FrameLifetime

private theorem check_action {α : Type} (result : Except SemError α) (safe : ExceptNoUnwind result) :
    FrameActionValid (fun _ _ => True) (Sem.fromMemoryExcept result) := by
  intro state valid
  cases result with
  | ok value => exact ⟨valid,True.intro,.refl _⟩
  | error error => cases error <;> first | exact True.intro | exact False.elim (safe _ _ rfl)

private theorem alignment_no_unwind (natural : Nat) (align : Option Nat) :
    ExceptNoUnwind (checkedMemoryAlign "Store" natural align) := by
  unfold checkedMemoryAlign
  dsimp only
  split <;> intro exception after same <;> cases same

/-- The original store changes only memory, through strict/poison checks,
source-plan failures, access checks, encoding and unwritten-record clipping.
Input values need no frame-identity premise because no SSA value is published. -/
theorem aggregate_store_value_frame_exit (service : AggregateMemory.Service)
    (safe : AggregateMemory.ServiceErrorPolicy BlockDecodeError service)
    (order : FunctionAddressOrder) (ty : Ty) (pointer value : Value)
    (strict : Bool) (align : Option Nat) (model : ByteModel) :
    FrameActionValid (fun _ _ => True) (AggregateMemory.storeValue service order ty pointer value strict align model) := by
  intro state valid
  unfold AggregateMemory.storeValue
  by_cases rejected : (strict && (value.isPoison || AggregateMemory.carriesUnwritten value)) = true
  · simp only [rejected,↓reduceIte]
    exact True.intro
  · simp only [rejected,↓reduceIte,pure_bind]
    have planSafe := AggregateMemory.checkedPlan_errors BlockDecodeError (fun _ => True.intro) service safe model ty
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
      (check_action _ (DecodeFrameExit.no_unwind _ _ ((block_result_frame_iff _ _).1 planSafe)) state valid)
    intro plan state valid _
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
      (check_action _ (alignment_no_unwind plan.layout.alignment align) state valid)
    intro alignment state valid _
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
      (reject_partial_frame_action pointer "Store" state valid)
    intro unit state valid _
    cases unit
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
      (expect_pointer_frame_action pointer "Store" state valid)
    intro pair state valid _
    obtain ⟨address,allocation⟩ := pair
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
      (checked_access_frame_action "Store" address allocation plan.layout.size alignment model state valid)
    intro address state valid _
    repeat' first
      | (solve | exact True.intro)
      | (solve | exact ⟨⟨valid.table,valid.values⟩,True.intro,⟨Nat.le_refl _,fun _ _ closed => closed⟩⟩)
      | (simp only [pure_bind])
      | (refine FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
          (check_action _ (aggregate_encode_no_unwind _ _ _ _ _) state valid) ?_; intro image state valid _)
      | split
      | (dsimp only; split)

theorem scalar_layout_no_unwind (model : ByteModel) (ty : Ty) :
    ExceptNoUnwind (scalarMemoryLayout model ty) := by
  unfold scalarMemoryLayout
  repeat' first
    | (solve | intro exception after same; cases same)
    | split
    | (dsimp only; split)

/-- Original scalar store, including poison transport and the actual
contextual encoder; invalid values retain their original refusals. -/
theorem scalar_store_value_frame_exit (ctx : EvalContext) (ty : Ty) (pointer value : Value)
    (strict : Bool) (align : Option Nat) :
    FrameActionValid (fun _ _ => True) (semStoreValueUsing (scalarMemoryLayout ctx.byteModel)
      (encodeMemoryWithFunctions ctx.byteModel ctx.functionOrder ty) ty pointer value strict align ctx.byteModel) := by
  intro state valid
  unfold semStoreValueUsing
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
    (reject_partial_frame_action pointer "Store" state valid)
  intro unit state valid _
  cases unit
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
    (expect_pointer_frame_action pointer "Store" state valid)
  intro pair state valid _
  obtain ⟨address,allocation⟩ := pair
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
    (check_action _ (scalar_layout_no_unwind ctx.byteModel ty) state valid)
  intro layout state valid _
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
    (check_action _ (alignment_no_unwind layout.alignment align) state valid)
  intro alignment state valid _
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
    (checked_access_frame_action "Store" address allocation layout.size alignment ctx.byteModel state valid)
  intro address state valid _
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
    (show FrameActionExit (fun _ _ => True) state (Sem.run Sem.getState state) from ⟨valid,True.intro,.refl _⟩)
  intro snapshot state valid _
  repeat' first
    | (solve | exact True.intro)
    | (solve | exact ⟨⟨valid.table,valid.values⟩,True.intro,⟨Nat.le_refl _,fun _ _ closed => closed⟩⟩)
    | (simp only [pure_bind])
    | (refine FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
        (check_action _ (encode_functions_no_unwind _ _ _ _) state valid) ?_; intro bytes state valid _)
    | split
    | (dsimp only; split)
  rename_i result failure encoded
  cases failure <;> first
    | exact True.intro
    | exact False.elim (encode_functions_no_unwind ctx.byteModel ctx.functionOrder ty value _ _ encoded)

private theorem original_check_action {α : Type} (result : Except SemError α)
    (safe : ByteImage.BlockResult (fun _ => True) BlockDecodeError result) :
    FrameActionValid (fun _ _ => True) (Sem.fromMemoryExcept result) :=
  check_action result (DecodeFrameExit.no_unwind _ _ ((block_result_frame_iff _ _).1 safe))

/-- Actual original-source nominal storage changes only memory. Source checks,
canonical child encoding and all failure exits remain in this proved action. -/
theorem original_closure_store_value_frame_exit (service : OriginalClosureMemory.Service)
    (order : FunctionAddressOrder) (closure : ClosureTyId) (pointer value : Value)
    (strict : Bool) (align : Option Nat) (model : ByteModel) :
    FrameActionValid (fun _ _ => True)
      (OriginalClosureMemory.storeValue service order closure pointer value strict align model) := by
  intro state valid
  unfold OriginalClosureMemory.storeValue
  by_cases rejected : (strict && (value.isPoison || AggregateMemory.carriesUnwritten value)) = true
  · simp only [rejected,↓reduceIte]
    exact True.intro
  · simp only [rejected,↓reduceIte,pure_bind]
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
      (original_check_action _
        (OriginalClosureMemory.binding_errors BlockDecodeError (fun _ => True.intro)
          (fun _ => True.intro) service model closure) state valid)
    intro held state valid _
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
      (original_check_action _
        (OriginalClosureMemory.layout_errors BlockDecodeError (fun _ => True.intro) _) state valid)
    intro storage state valid _
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
      (original_check_action _
        (OriginalClosureMemory.capturePlans_errors BlockDecodeError (fun _ => True.intro)
          (fun _ => True.intro) service _ _ _ _) state valid)
    intro fields state valid _
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
      (check_action _ (alignment_no_unwind storage.alignment align) state valid)
    intro alignment state valid _
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
      (reject_partial_frame_action pointer "Store" state valid)
    intro unit state valid _
    cases unit
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
      (expect_pointer_frame_action pointer "Store" state valid)
    intro pair state valid _
    obtain ⟨address,allocation⟩ := pair
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
      (checked_access_frame_action "Store" address allocation storage.size alignment model state valid)
    intro address state valid _
    repeat' first
      | (solve | exact True.intro)
      | (solve | exact ⟨⟨valid.table,valid.values⟩,True.intro,⟨Nat.le_refl _,fun _ _ closed => closed⟩⟩)
      | (simp only [pure_bind])
      | (refine FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state
          (check_action _ (closure_capture_encode_no_unwind _ _ _ _ _) state valid) ?_; intro image state valid _)
      | split
      | (dsimp only; split)

theorem context_store_aligned_frame_exit (ctx : EvalContext) (safe : MemoryContextErrors ctx)
    (ty : Ty) (pointer value : Value) (strict : Bool) (align : Option Nat) :
    FrameActionValid (fun _ _ => True) (ctx.storeMemoryValueAligned ty pointer value strict align) := by
  unfold EvalContext.storeMemoryValueAligned
  cases selected : ctx.memoryRoute ty with
  | scalar => exact scalar_store_value_frame_exit ctx ty pointer value strict align
  | descriptor service =>
    exact aggregate_store_value_frame_exit service
      (safe ty service (ctx.memoryRoute_descriptor_source ty service selected)) _ _ _ _ _ _ _
  | original closure service => exact original_closure_store_value_frame_exit service _ _ _ _ _ _ _

theorem context_store_value_frame_exit (ctx : EvalContext) (safe : MemoryContextErrors ctx)
    (ty : Ty) (pointer value : Value) (strict : Bool) :
    FrameActionValid (fun _ _ => True) (ctx.storeMemoryValue ty pointer value strict) :=
  context_store_aligned_frame_exit ctx safe ty pointer value strict none

/-- The actual common operand/route selector publishes no SSA result across
all three routes, including the original-source nominal branch. -/
theorem context_store_step_frame_exit (ctx : EvalContext) (safe : MemoryContextErrors ctx)
    (ty : Ty) (pointer value : ValueId) (strict : Bool) (align : Option Nat) :
    FrameActionValid (fun _ result => BodyValueResult result)
      (stepInstWithContext ctx (.Store ty pointer value strict align)) := by
  intro state valid
  unfold stepInstWithContext
  apply FrameActionExit.bind MintedValue (fun _ result => BodyValueResult result) _ _ state
    (lookup_value_frame_action pointer state valid)
  intro pointer state valid _
  apply FrameActionExit.bind MintedValue (fun _ result => BodyValueResult result) _ _ state
    (lookup_value_frame_action value state valid)
  intro value state valid _
  apply FrameActionExit.bind (fun _ _ => True) (fun _ result => BodyValueResult result) _ _ state
    (context_store_aligned_frame_exit ctx safe ty pointer value strict align state valid)
  intro unit state valid _
  cases unit
  exact ⟨valid,True.intro,.refl _⟩

theorem context_store_body_frame_exit (recurse : GenericCoro.Prefix.Recurse) (ctx : EvalContext)
    (safe : MemoryContextErrors ctx) (depth : Nat) (strategy : PanicStrategy)
    (ty : Ty) (pointer value : ValueId) (strict : Bool) (align : Option Nat) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True)
      (GenericCoro.Prefix.evalBodyStep recurse ctx depth strategy (.Store ty pointer value strict align,dests)) := by
  intro state valid
  apply FrameActionExit.bind (fun _ result => BodyValueResult result) (fun _ _ => True) _ _ state
    (context_store_step_frame_exit ctx safe ty pointer value strict align state valid)
  intro result loaded loadedValid shape
  cases result with
  | terminator step => cases shape
  | value id =>
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ loaded
      (instruction_results_frame_action ctx (.Store ty pointer value strict align) (.value id) dests loaded loadedValid)
    intro unit after afterValid _
    cases unit
    exact ⟨afterValid,True.intro,.refl _⟩
  | values ids =>
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ loaded
      (instruction_results_frame_action ctx (.Store ty pointer value strict align) (.values ids) dests loaded loadedValid)
    intro unit after afterValid _
    cases unit
    exact ⟨afterValid,True.intro,.refl _⟩

end TrustIr.FrameLifetime
