-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SSAFreshMemory

namespace TrustIr.SSAFreshOwnership
open SSAFreshFrames SSAFreshStep SSAFreshInstructions SSAFreshMemory

local macro "read_leaves" : tactic =>
  `(tactic| repeat (first
    | exact pure_fresh _
    | exact throw_fresh _
    | exact bindFresh_fresh _
    | exact get_fresh
    | exact lookup_fresh _
    | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split))

theorem getPermission_fresh (allocation : AllocId) : KeepsFresh (getPermission allocation) := by
  unfold getPermission
  read_leaves

theorem setPermission_fresh (allocation : AllocId) (permission : Permission) :
    KeepsFresh (setPermission allocation permission) := by
  unfold setPermission
  exact modify_fresh _ (fun state fresh => sameSSA_fresh state _ fresh rfl rfl)

theorem borrowOperand_fresh (op : String) (value : Value) : KeepsFresh (borrowOperand op value) := by
  unfold borrowOperand
  read_leaves

theorem getAllocIdFromPtrARC_fresh (value : Value) : KeepsFresh (getAllocIdFromPtrARC value) := by
  unfold getAllocIdFromPtrARC
  read_leaves

theorem requireArcRef_fresh (allocation : AllocId) : KeepsFresh (requireArcRef allocation) := by
  unfold requireArcRef
  read_leaves

theorem requireObjectBase_fresh (op : String) (value : Value) (allocation : AllocId) :
    KeepsFresh (requireObjectBase op value allocation) := by
  unfold requireObjectBase
  read_leaves

theorem deallocARC_fresh (allocation : AllocId) : KeepsFresh (deallocARC allocation) := by
  unfold deallocARC
  refine getState_bind_fresh _ (fun state fresh => ?_)
  dsimp only
  split
  · exact throw_fresh _
  · exact setState_fresh _ (sameSSA_fresh state _ fresh rfl rfl)

local macro "ownership_leaves" : tactic =>
  `(tactic| repeat (first
    | exact pure_fresh _
    | exact throw_fresh _
    | exact bindFresh_fresh _
    | exact get_fresh
    | exact lookup_fresh _
    | exact getPermission_fresh _
    | exact setPermission_fresh _ _
    | exact borrowOperand_fresh _ _
    | exact getAllocIdFromPtrARC_fresh _
    | exact requireArcRef_fresh _
    | exact requireObjectBase_fresh _ _ _
    | exact deallocARC_fresh _
    | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split))

theorem semBorrow_fresh (pointer : ValueId) : KeepsFresh (semBorrow pointer) := by
  unfold semBorrow
  ownership_leaves

theorem semBorrowMut_fresh (pointer : ValueId) : KeepsFresh (semBorrowMut pointer) := by
  unfold semBorrowMut
  ownership_leaves

theorem semEndBorrow_fresh (pointer : ValueId) : KeepsFresh (semEndBorrow pointer) := by
  unfold semEndBorrow
  ownership_leaves

theorem semIsUnique_fresh (pointer : ValueId) : KeepsFresh (semIsUnique pointer) := by
  unfold semIsUnique
  ownership_leaves

theorem semRetain_fresh (pointer : ValueId) : KeepsFresh (semRetain pointer) := by
  unfold semRetain
  refine bind_fresh _ _ (lookup_fresh pointer) (fun value => ?_)
  refine bind_fresh _ _ (getAllocIdFromPtrARC_fresh value) (fun allocation => ?_)
  refine bind_fresh _ _ (requireArcRef_fresh allocation) (fun _ => ?_)
  refine bind_fresh _ _ (requireObjectBase_fresh "Retain" value allocation) (fun _ => ?_)
  refine getState_bind_fresh _ (fun state fresh => ?_)
  exact setState_fresh _ (sameSSA_fresh state _ fresh rfl rfl)

theorem semRelease_fresh (pointer : ValueId) : KeepsFresh (semRelease pointer) := by
  unfold semRelease
  refine bind_fresh _ _ (lookup_fresh pointer) (fun value => ?_)
  refine bind_fresh _ _ (getAllocIdFromPtrARC_fresh value) (fun allocation => ?_)
  refine bind_fresh _ _ (requireArcRef_fresh allocation) (fun _ => ?_)
  refine bind_fresh _ _ (requireObjectBase_fresh "Release" value allocation) (fun _ => ?_)
  refine getState_bind_fresh _ (fun state fresh => ?_)
  dsimp only
  split
  · exact throw_fresh _
  · exact deallocARC_fresh allocation
  · exact setState_fresh _ (sameSSA_fresh state _ fresh rfl rfl)

end TrustIr.SSAFreshOwnership
