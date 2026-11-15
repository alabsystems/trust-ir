-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameGEPExits
import TrustIr.Proofs.FrameWorldUpdates

namespace TrustIr.FrameLifetime

private theorem get_action : FrameActionValid (fun _ _ => True) Sem.getState := by
  intro state valid
  exact ⟨valid,True.intro,.refl _⟩

theorem bulk_count_frame_exit (operation : String) (count : ValueId) :
    FrameActionValid (fun _ _ => True) (bulkByteCount operation count) := by
  intro state valid
  unfold bulkByteCount
  apply FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state (lookup_value_frame_action count state valid)
  intro count state valid _
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (reject_partial_frame_action count operation state valid)
  intro unit state valid _
  cases unit
  repeat' first
    | (solve | exact True.intro)
    | (solve | exact ⟨valid,True.intro,.refl _⟩)
    | split
    | (dsimp only; split)

theorem bulk_pointer_frame_exit (operation : String) (pointer : ValueId) (count : Nat) (model : ByteModel) :
    FrameActionValid (fun _ _ => True) (bulkPointer operation pointer count model) := by
  intro state valid
  unfold bulkPointer Sem.accessAddr
  apply FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state (lookup_value_frame_action pointer state valid)
  intro pointer state valid _
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (reject_partial_frame_action pointer operation state valid)
  intro unit state valid _
  cases unit
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (expect_pointer_frame_action pointer operation state valid)
  intro pair state valid _
  exact checked_access_frame_action operation pair.1 pair.2 count 1 model state valid

/-- Original copy/move, including the zero-count shortcut, both access
checks, overlap refusal and actual captured image written to memory. -/
theorem memcopy_frame_exit (dst src count : ValueId) (overlap : Bool) (model : ByteModel) :
    FrameActionValid (fun _ _ => True) (semMemCopy dst src count overlap model) := by
  intro state valid
  unfold semMemCopy
  dsimp only
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (bulk_count_frame_exit _ count state valid)
  intro count state valid _
  split
  · exact ⟨valid,True.intro,.refl _⟩
  · apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (bulk_pointer_frame_exit _ dst count model state valid)
    intro dst state valid _
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (bulk_pointer_frame_exit _ src count model state valid)
    intro src state valid _
    apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (get_action state valid)
    intro snapshot state valid _
    split
    · exact True.intro
    · simp only [pure_bind]
      exact ⟨⟨valid.table,valid.values⟩,True.intro,⟨Nat.le_refl _,fun _ _ closed => closed⟩⟩

/-- Original fill, including fill lookup/inspection before zero count and
initialization of the actual destination byte range. -/
theorem memset_frame_exit (dst byte count : ValueId) (model : ByteModel) :
    FrameActionValid (fun _ _ => True) (semMemSet dst byte count model) := by
  intro state valid
  unfold semMemSet
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (bulk_count_frame_exit "MemSet" count state valid)
  intro count state valid _
  apply FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state (lookup_value_frame_action byte state valid)
  intro byte state valid _
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (reject_partial_frame_action byte "MemSet fill byte" state valid)
  intro unit state valid _
  cases unit
  repeat' first
    | (solve | exact True.intro)
    | (solve | exact ⟨valid,True.intro,.refl _⟩)
    | (solve | exact ⟨⟨valid.table,valid.values⟩,True.intro,⟨Nat.le_refl _,fun _ _ closed => closed⟩⟩)
    | (simp only [pure_bind])
    | (refine FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (bulk_pointer_frame_exit _ _ _ _ state valid) ?_; intro dst state valid _)
    | split
    | (dsimp only; split)

inductive BulkFrameInst : Inst → Prop where
  | copy (dst src count overlap) : BulkFrameInst (.MemCopy dst src count overlap)
  | fill (dst byte count) : BulkFrameInst (.MemSet dst byte count)

theorem bulk_step_frame_exit (ctx : EvalContext) (inst : Inst) (grammar : BulkFrameInst inst) :
    FrameActionValid (fun _ result => BodyValueResult result) (stepInstWithContext ctx inst) := by
  intro state valid
  cases grammar with
  | copy dst src count overlap =>
    apply FrameActionExit.bind (fun _ _ => True) (fun _ result => BodyValueResult result) _ _ state (memcopy_frame_exit dst src count overlap ctx.byteModel state valid)
    intro unit state valid _
    cases unit
    exact ⟨valid,True.intro,.refl _⟩
  | fill dst byte count =>
    apply FrameActionExit.bind (fun _ _ => True) (fun _ result => BodyValueResult result) _ _ state (memset_frame_exit dst byte count ctx.byteModel state valid)
    intro unit state valid _
    cases unit
    exact ⟨valid,True.intro,.refl _⟩

theorem bulk_body_frame_exit (recurse : GenericCoro.Prefix.Recurse) (ctx : EvalContext)
    (depth : Nat) (strategy : PanicStrategy) (inst : Inst) (grammar : BulkFrameInst inst) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (GenericCoro.Prefix.evalBodyStep recurse ctx depth strategy (inst,dests)) := by
  intro state valid
  have stepSafe := bulk_step_frame_exit ctx inst grammar state valid
  cases grammar <;> apply FrameActionExit.bind (fun _ result => BodyValueResult result) (fun _ _ => True) _ _ state stepSafe
  all_goals
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
