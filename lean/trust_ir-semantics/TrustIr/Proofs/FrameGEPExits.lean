-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameAllocationExits

namespace TrustIr.FrameLifetime

private theorem check_action {α : Type} (result : Except SemError α) (safe : ExceptNoUnwind result) :
    FrameActionValid (fun _ _ => True) (Sem.fromMemoryExcept result) := by
  intro state valid
  cases result with
  | ok value => exact ⟨valid,True.intro,.refl _⟩
  | error error => cases error <;> first | exact True.intro | exact False.elim (safe _ _ rfl)

private theorem get_action : FrameActionValid (fun _ _ => True) Sem.getState := by
  intro state valid
  exact ⟨valid,True.intro,.refl _⟩

theorem gep_offset_no_unwind {key : Type} (layoutOf : MemoryLayoutQuery)
    (reader : key → Value → Except SemError Int) (layouts : ∀ ty, ExceptNoUnwind (layoutOf ty))
    (integers : ∀ id value, ExceptNoUnwind (reader id value)) (ty : Ty) (indices : List (key × Value)) :
    ExceptNoUnwind (gepOffsetUsing layoutOf reader ty indices) := by
  unfold gepOffsetUsing
  apply ExceptNoUnwind.bind _ _ (layouts ty)
  intro layout
  apply ExceptNoUnwind.forIn
  intro input delta
  apply ExceptNoUnwind.bind _ _ (integers input.1 input.2)
  intro integer
  apply ExceptNoUnwind.bind _ _ (word_operand_no_unwind "GEP" false integer)
  intro magnitude
  apply ExceptNoUnwind.bind _ _ (word_mul_no_unwind "GEP" layout.size magnitude)
  intro offset
  apply ExceptNoUnwind.bind _ _ (word_add_no_unwind "GEP" delta offset)
  intro result exception after same
  cases same

/-- Actual provenance-aware address arithmetic creates only frame-free
pointers. Its u64/target checks and absent-origin refusals remain explicit. -/
theorem gep_address_frame_exit (base : Value) (delta : Nat) (model : ByteModel) :
    FrameActionValid MintedValue (semGEPAddress base delta model) := by
  intro state valid
  unfold semGEPAddress
  apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ state (reject_partial_frame_action base "GEP" state valid)
  intro unit state valid _
  cases unit
  split
  · exact True.intro
  · apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ state (check_action _ (word_add_no_unwind _ _ _) state valid)
    intro result state valid _
    split
    · exact True.intro
    · exact ⟨valid,(mintedValue_iff_shape _ _).2 True.intro,.refl _⟩
  · apply FrameActionExit.bind (fun _ _ => True) MintedValue _ _ state (get_action state valid)
    intro snapshot state valid _
    repeat' first
      | (solve | exact True.intro)
      | (solve | exact ⟨valid,(mintedValue_iff_shape _ _).2 True.intro,.refl _⟩)
      | (simp only [pure_bind])
      | (refine FrameActionExit.bind (fun _ _ => True) MintedValue _ _ state (check_action _ (word_add_no_unwind _ _ _) state valid) ?_; intro result state valid _)
      | split
      | (dsimp only; split)
  · exact True.intro

theorem gep_values_frame_exit {key : Type} (layoutOf : MemoryLayoutQuery)
    (reader : key → Value → Except SemError Int) (layouts : ∀ ty, ExceptNoUnwind (layoutOf ty))
    (integers : ∀ id value, ExceptNoUnwind (reader id value)) (ty : Ty) (base : Value)
    (indices : List (key × Value)) (model : ByteModel) :
    FrameActionValid MintedValue (semGEPValuesUsing layoutOf reader ty base indices model) := by
  unfold semGEPValuesUsing
  apply FrameActionValid.bind (fun _ _ => True) MintedValue _ _
    (check_action _ (gep_offset_no_unwind layoutOf reader layouts integers ty indices))
  intro delta state valid _
  exact gep_address_frame_exit base delta model state valid

private theorem index_lookup_action (indices : List ValueId) :
    FrameActionValid (fun _ _ => True) (indices.mapM fun id => do pure (id, ← Sem.lookupValue id)) := by
  induction indices with
  | nil => intro state valid; exact ⟨valid,True.intro,.refl _⟩
  | cons id rest ih =>
    intro state valid
    simp only [List.mapM_cons,bind_assoc,pure_bind]
    apply FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state (lookup_value_frame_action id state valid)
    intro value state valid _
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (ih state valid)
    intro inputs state valid _
    exact ⟨valid,True.intro,.refl _⟩

/-- Full contextual GEP, including original operand retrieval order and
source-declared integer interpretation, then actual fresh SSA publication. -/
theorem gep_step_frame_exit (ctx : EvalContext) (safe : MemoryContextErrors ctx)
    (ty : Ty) (base : ValueId) (indices : List ValueId) (inbounds : Bool) :
    FrameActionValid (fun _ result => BodyValueResult result)
      (stepInstWithContext ctx (.GEP ty base indices inbounds)) := by
  intro state valid
  simp only [stepInstWithContext,semGEPUsing,bind_assoc]
  apply FrameActionExit.bind MintedValue (fun _ result => BodyValueResult result) _ _ state (lookup_value_frame_action base state valid)
  intro base state valid _
  apply FrameActionExit.bind (fun _ _ => True) (fun _ result => BodyValueResult result) _ _ state (index_lookup_action indices state valid)
  intro inputs state valid _
  apply FrameActionExit.bind MintedValue (fun _ result => BodyValueResult result) _ _ state
    (gep_values_frame_exit _ _ (context_memory_layout_no_unwind ctx safe) (carrier_integer_no_unwind ctx) ty base inputs ctx.byteModel state valid)
  intro value state valid incoming
  apply FrameActionExit.bind (fun _ _ => True) (fun _ result => BodyValueResult result) _ _ state (fresh_minted_frame_exit value state valid incoming)
  intro id state valid _
  exact ⟨valid,True.intro,.refl _⟩

theorem gep_body_frame_exit (recurse : GenericCoro.Prefix.Recurse) (ctx : EvalContext)
    (safe : MemoryContextErrors ctx) (depth : Nat) (strategy : PanicStrategy) (ty : Ty)
    (base : ValueId) (indices : List ValueId) (inbounds : Bool) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True)
      (GenericCoro.Prefix.evalBodyStep recurse ctx depth strategy (.GEP ty base indices inbounds,dests)) := by
  intro state valid
  apply FrameActionExit.bind (fun _ result => BodyValueResult result) (fun _ _ => True) _ _ state
    (gep_step_frame_exit ctx safe ty base indices inbounds state valid)
  intro result state valid shape
  cases result with
  | terminator step => cases shape
  | value id =>
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (instruction_results_frame_action ctx _ (.value id) dests state valid)
    intro unit state valid _
    cases unit
    exact ⟨valid,True.intro,.refl _⟩
  | values ids =>
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (instruction_results_frame_action ctx _ (.values ids) dests state valid)
    intro unit state valid _
    cases unit
    exact ⟨valid,True.intro,.refl _⟩

end TrustIr.FrameLifetime
