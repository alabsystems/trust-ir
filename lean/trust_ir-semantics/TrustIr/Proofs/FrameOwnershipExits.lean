-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameBulkMemoryExits

namespace TrustIr.FrameLifetime

private theorem get_action : FrameActionValid (fun _ _ => True) Sem.getState := by
  intro state valid
  exact ⟨valid,True.intro,.refl _⟩

local macro "readonly_guards" vf:ident : tactic => `(tactic|
  repeat' first
    | (solve | exact True.intro)
    | (solve | exact ⟨$vf,True.intro,.refl _⟩)
    | (simp only [pure_bind])
    | split
    | (dsimp only; split))

theorem borrow_operand_frame_exit (operation : String) (value : Value) :
    FrameActionValid (fun _ _ => True) (borrowOperand operation value) := by
  intro state valid
  unfold borrowOperand
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (get_action state valid)
  intro snapshot state valid _
  readonly_guards valid

theorem permission_get_frame_exit (id : AllocId) :
    FrameActionValid (fun _ _ => True) (getPermission id) := by
  intro state valid
  unfold getPermission
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (get_action state valid)
  intro snapshot state valid _
  readonly_guards valid

theorem permission_set_frame_exit (id : AllocId) (permission : Permission) :
    FrameActionValid (fun _ _ => True) (setPermission id permission) := by
  intro state valid
  exact ⟨⟨valid.table,valid.values⟩,True.intro,⟨Nat.le_refl _,fun _ _ closed => closed⟩⟩

private theorem fresh_after_action (action : Sem Unit) (safe : FrameActionValid (fun _ _ => True) action)
    (value : Value) (state : MachineState) (valid : WellMintedState state)
    (incoming : MintedValue state.nextFrameLineage value) :
    FrameActionExit (fun _ _ => True) state (Sem.run (do action; Sem.bindFresh value) state) := by
  apply FrameActionExit.bind (fun bound _ => MintedValue bound value) (fun _ _ => True) _ _ state
    (frame_carry_value_exit state _ value incoming (safe state valid))
  intro unit state valid incoming
  cases unit
  exact fresh_minted_frame_exit value state valid incoming

local macro "borrow_exits" st:ident vf:ident inc:ident : tactic => `(tactic|
  repeat' first
    | (solve | exact True.intro)
    | (solve | exact fresh_minted_frame_exit _ ($st) ($vf) (by assumption))
    | (solve | exact fresh_after_action _ (permission_set_frame_exit _ _) _ ($st) ($vf) (by assumption))
    | (simp only [pure_bind])
    | (refine FrameActionExit.bind (fun bound _ => MintedValue bound _) (fun _ _ => True) _ _ $st
        (frame_carry_value_exit $st _ _ (by assumption) (borrow_operand_frame_exit _ _ ($st) ($vf))) ?_; intro target $st $vf $inc)
    | (refine FrameActionExit.bind (fun bound _ => MintedValue bound _) (fun _ _ => True) _ _ $st
        (frame_carry_value_exit $st _ _ (by assumption) (permission_get_frame_exit _ ($st) ($vf))) ?_; intro permission $st $vf $inc)
    | split
    | (dsimp only; split))

/-- Actual shared borrow, including fat-pointer pass-through and recursive
identity bounds retained through permission updates and alias publication. -/
theorem borrow_frame_exit (pointer : ValueId) :
    FrameActionValid (fun _ _ => True) (semBorrow pointer) := by
  intro state valid
  unfold semBorrow
  apply FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state (lookup_value_frame_action pointer state valid)
  intro value state valid incoming
  borrow_exits state valid incoming

theorem borrow_mut_frame_exit (pointer : ValueId) :
    FrameActionValid (fun _ _ => True) (semBorrowMut pointer) := by
  intro state valid
  unfold semBorrowMut
  apply FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state (lookup_value_frame_action pointer state valid)
  intro value state valid incoming
  borrow_exits state valid incoming

theorem end_borrow_frame_exit (pointer : ValueId) :
    FrameActionValid (fun _ _ => True) (semEndBorrow pointer) := by
  intro state valid
  unfold semEndBorrow
  apply FrameActionExit.bind MintedValue (fun _ _ => True) _ _ state (lookup_value_frame_action pointer state valid)
  intro value state valid _
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (get_action state valid)
  intro snapshot state valid _
  repeat' first
    | (solve | exact True.intro)
    | (solve | exact ⟨valid,True.intro,.refl _⟩)
    | (solve | exact permission_set_frame_exit _ _ state valid)
    | (simp only [pure_bind])
    | (refine FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (permission_get_frame_exit _ state valid) ?_; intro permission state valid _)
    | split
    | (dsimp only; split)

theorem arc_pointer_frame_exit (value : Value) :
    FrameActionValid (fun _ _ => True) (getAllocIdFromPtrARC value) := by
  intro state valid
  unfold getAllocIdFromPtrARC
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (get_action state valid)
  intro snapshot state valid _
  readonly_guards valid

theorem arc_permission_frame_exit (id : AllocId) :
    FrameActionValid (fun _ _ => True) (requireArcRef id) := by
  intro state valid
  unfold requireArcRef
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (get_action state valid)
  intro snapshot state valid _
  readonly_guards valid

theorem arc_object_base_frame_exit (operation : String) (value : Value) (id : AllocId) :
    FrameActionValid (fun _ _ => True) (requireObjectBase operation value id) := by
  intro state valid
  unfold requireObjectBase
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (get_action state valid)
  intro snapshot state valid _
  readonly_guards valid

/-- ARC deallocation retains the exact snapshot while marking matching
allocations dead and clearing permission/setting refcount zero. -/
theorem arc_dealloc_frame_exit (id : AllocId) :
    FrameActionValid (fun _ _ => True) (deallocARC id) := by
  intro state valid
  unfold deallocARC
  apply frame_get_bind_exit
  dsimp only
  split
  · exact True.intro
  · exact ⟨⟨valid.table,valid.values⟩,True.intro,⟨Nat.le_refl _,fun _ _ closed => closed⟩⟩

local macro "arc_prefix" st:ident vf:ident : tactic => `(tactic| (
  refine (FrameActionExit.bind MintedValue (fun _ _ => True) _ _ $st (lookup_value_frame_action _ ($st) ($vf)) ?_)
  intro value $st $vf _
  refine (FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ $st (arc_pointer_frame_exit value ($st) ($vf)) ?_)
  intro id $st $vf _
  refine (FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ $st (arc_permission_frame_exit id ($st) ($vf)) ?_)
  intro unit $st $vf _
  cases unit
  refine (FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ $st (arc_object_base_frame_exit _ value id ($st) ($vf)) ?_)
  intro unit $st $vf _
  cases unit))


theorem retain_frame_exit (pointer : ValueId) :
    FrameActionValid (fun _ _ => True) (semRetain pointer) := by
  intro state valid
  unfold semRetain
  arc_prefix state valid
  apply frame_get_bind_exit
  exact ⟨⟨valid.table,valid.values⟩,True.intro,⟨Nat.le_refl _,fun _ _ closed => closed⟩⟩

theorem release_frame_exit (pointer : ValueId) :
    FrameActionValid (fun _ _ => True) (semRelease pointer) := by
  intro state valid
  unfold semRelease
  arc_prefix state valid
  apply frame_get_bind_exit
  dsimp only
  split
  · exact True.intro
  · exact arc_dealloc_frame_exit _ state valid
  · exact ⟨⟨valid.table,valid.values⟩,True.intro,⟨Nat.le_refl _,fun _ _ closed => closed⟩⟩

theorem is_unique_frame_exit (pointer : ValueId) :
    FrameActionValid (fun _ _ => True) (semIsUnique pointer) := by
  intro state valid
  unfold semIsUnique
  arc_prefix state valid
  apply FrameActionExit.bind (fun _ _ => True) (fun _ _ => True) _ _ state (get_action state valid)
  intro snapshot state valid _
  exact fresh_minted_frame_exit _ state valid ((mintedValue_iff_shape _ _).2 True.intro)

inductive OwnershipFrameInst : Inst → Prop where
  | shared (pointer) : OwnershipFrameInst (.Borrow pointer)
  | mutable (pointer) : OwnershipFrameInst (.BorrowMut pointer)
  | endBorrow (pointer) : OwnershipFrameInst (.EndBorrow pointer)
  | retain (pointer) : OwnershipFrameInst (.Retain pointer)
  | release (pointer) : OwnershipFrameInst (.Release pointer)
  | unique (pointer) : OwnershipFrameInst (.IsUnique pointer)

private theorem one_result (action : Sem ValueId) (safe : FrameActionValid (fun _ _ => True) action) :
    FrameActionValid (fun _ result => BodyValueResult result) (do
      let id ← action
      pure (.value (some id))) := by
  intro state valid
  apply FrameActionExit.bind (fun _ _ => True) (fun _ result => BodyValueResult result) _ _ state (safe state valid)
  intro id state valid _
  exact ⟨valid,True.intro,.refl _⟩

private theorem no_result (action : Sem Unit) (safe : FrameActionValid (fun _ _ => True) action) :
    FrameActionValid (fun _ result => BodyValueResult result) (do
      action
      pure (.value none)) := by
  intro state valid
  apply FrameActionExit.bind (fun _ _ => True) (fun _ result => BodyValueResult result) _ _ state (safe state valid)
  intro unit state valid _
  cases unit
  exact ⟨valid,True.intro,.refl _⟩

theorem ownership_step_frame_exit (ctx : EvalContext) (inst : Inst) (grammar : OwnershipFrameInst inst) :
    FrameActionValid (fun _ result => BodyValueResult result) (stepInstWithContext ctx inst) := by
  cases grammar
  · exact one_result _ (borrow_frame_exit _)
  · exact one_result _ (borrow_mut_frame_exit _)
  · exact no_result _ (end_borrow_frame_exit _)
  · exact no_result _ (retain_frame_exit _)
  · exact no_result _ (release_frame_exit _)
  · exact one_result _ (is_unique_frame_exit _)

theorem ownership_body_frame_exit (recurse : GenericCoro.Prefix.Recurse) (ctx : EvalContext)
    (depth : Nat) (strategy : PanicStrategy) (inst : Inst) (grammar : OwnershipFrameInst inst) (dests : List ValueId) :
    FrameActionValid (fun _ _ => True) (GenericCoro.Prefix.evalBodyStep recurse ctx depth strategy (inst,dests)) := by
  intro state valid
  have stepSafe := ownership_step_frame_exit ctx inst grammar state valid
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
