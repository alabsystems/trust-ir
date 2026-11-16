-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SSAFreshMemoryExtra
import TrustIr.Proofs.TransformCorrectness

namespace TrustIr.SSAFreshDispatch
open SSAFreshFrames SSAFreshStep SSAFreshInstructions SSAFreshMemory SSAFreshOwnership
  SSAFreshAtomic SSAFreshMemoryExtra

theorem semAssertFail_fresh {α : Type} (kind : AssertKind) (site : Option PanicSite) :
    KeepsFresh (semAssertFail kind site : Sem α) := by
  intro state result _ run
  exact False.elim (semAssertFail_run_not_ok kind site state result run)

theorem semCoroSuspend_fresh (frame : ValueId) (slot : Nat) (next : Int)
    (value : ValueId) (model : ByteModel) :
    KeepsFresh (semCoroSuspend frame slot next value model) := by
  unfold semCoroSuspend
  refine bind_fresh _ _ (lookup_fresh frame) (fun heldFrame => ?_)
  refine bind_fresh _ _
    (equivariant_fresh _ (HeldMemoryFrames.semGEPValuesUsing_eqv _ _ _ _ _ _)) (fun heldSlot => ?_)
  exact bind_fresh _ _
    (equivariant_fresh _ (HeldMemoryFrames.semStoreValueUsing_eqv _ _ _ _ _ _ _ _))
    (fun _ => semReturn_fresh [value])

theorem throwUB_fresh {α : Type} (message : String) :
    KeepsFresh (Sem.throwUB message : Sem α) := throw_fresh _

theorem throwTypeError_fresh {α : Type} (message : String) :
    KeepsFresh (Sem.throwTypeError message : Sem α) := throw_fresh _

theorem throwUnsupported_fresh {α : Type} (feature : UnsupportedFeature) (message : String) :
    KeepsFresh (Sem.throwUnsupported feature message : Sem α) := throw_fresh _

theorem semBoxDeref_fresh (pointee : BoxPointee) (value : Value) (model : ByteModel) :
    KeepsFresh (semBoxDeref pointee value model) := by
  unfold semBoxDeref
  repeat (first
    | exact accessAlign_fresh _ _ _ _
    | exact checkedAccess_fresh _ _ _ _ _ _
    | exact rejectPartial_fresh _ _
    | exact pure_fresh _
    | exact throwUB_fresh _
    | exact throwTypeError_fresh _
    | exact throwUnsupported_fresh _ _
    | exact bindFresh_fresh _
    | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split)

local macro "step_leaves" : tactic =>
  `(tactic| with_reducible (repeat (first
    | apply semBinOp_fresh
    | apply semBoolBinOpInst_fresh
    | apply semUnOp_fresh
    | apply semOverflow_fresh
    | apply semICmpInst_fresh
    | apply semFCmpInst_fresh
    | apply semCast_fresh
    | apply semBr_fresh
    | apply semCondBr_fresh
    | apply semReturn_fresh
    | apply semAssertFail_fresh
    | apply semLoadUsing_fresh
    | apply semStoreUsing_fresh
    | apply semAllocaUsing_fresh
    | apply semHeapAllocUsing_fresh
    | apply semGEPUsing_fresh
    | apply semGlobalAddr_fresh
    | apply semGlobalAddrUsing_fresh
    | apply semPtrData_fresh
    | apply semPtrMetadata_fresh
    | apply semPtrFromParts_fresh
    | apply semAtomicLoadUsing_fresh
    | apply semAtomicStoreUsing_fresh
    | apply semAtomicRMWUsing_fresh
    | apply semCmpXchg_fresh
    | apply semCmpXchgExchangeUsing_fresh
    | apply semFence_fresh
    | apply semExtractField_fresh
    | apply semInsertField_fresh
    | apply semMakeAggregate_fresh
    | apply semArraySplat_fresh
    | apply semExtractElement_fresh
    | apply semInsertElement_fresh
    | apply semSeqMapAddK_fresh
    | apply semSeqMapNot_fresh
    | apply semBorrow_fresh
    | apply semBorrowMut_fresh
    | apply semEndBorrow_fresh
    | apply semRetain_fresh
    | apply semRelease_fresh
    | apply semIsUnique_fresh
    | apply semOpenFrame_fresh
    | apply semBindSlot_fresh
    | apply semLoadSlot_fresh
    | apply semCloseFrame_fresh
    | apply semDealloc_fresh
    | apply semMemCopy_fresh
    | apply semMemSet_fresh
    | apply semCoroSuspend_fresh
    | apply semBoxDeref_fresh
    | apply lookupLanes_fresh
    | exact pure_fresh _
    | apply throwUB_fresh
    | apply throwTypeError_fresh
    | apply throwUnsupported_fresh
    | exact throw_fresh _
    | exact bindFresh_fresh _
    | exact bindFreshPair_fresh _ _
    | exact get_fresh
    | exact lookup_fresh _
    | exact rejectPartial_fresh _ _
    | exact mapM_fresh Sem.lookupValue _ lookup_fresh
    | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split)))

theorem semSwitch_fresh (value : ValueId) (default_ : BlockId)
    (defaultArgs : List ValueId) (cases : List SwitchCase) :
    KeepsFresh (semSwitch value default_ defaultArgs cases) := by
  unfold semSwitch
  step_leaves

/-- Every successful bare instruction preserves the SSA high-water invariant,
    including its real state effects and error ordering. -/
theorem stepInst_fresh (inst : Inst) (model : ByteModel) :
    KeepsFresh (stepInst inst model) := by
  cases inst <;>
    simp only [stepInst, semLoad, semStore, semAlloca, semHeapAlloc, semGEP,
      semAtomicLoad, semAtomicStore, semAtomicRMW] <;>
    first | apply semSwitch_fresh | step_leaves
  all_goals first | apply semSwitch_fresh | step_leaves

end TrustIr.SSAFreshDispatch
