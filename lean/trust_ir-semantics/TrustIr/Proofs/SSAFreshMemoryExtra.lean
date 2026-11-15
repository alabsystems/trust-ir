-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SSAFreshAtomic

namespace TrustIr.SSAFreshMemoryExtra
open SSAFreshFrames SSAFreshStep SSAFreshInstructions SSAFreshMemory

local macro "memory_leaves" : tactic =>
  `(tactic| repeat (first
    | exact expectPointer_fresh _ _
    | exact targetAddress_fresh _ _ _
    | exact checkedAccess_fresh _ _ _ _ _ _
    | exact pure_fresh _
    | exact throw_fresh _
    | exact bindFresh_fresh _
    | exact get_fresh
    | exact lookup_fresh _
    | exact rejectPartial_fresh _ _
    | exact fromMemoryExcept_fresh _
    | (exact modify_fresh _ (fun state fresh => sameSSA_fresh state _ fresh rfl rfl))
    | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split))

theorem accessAddr_fresh (op : String) (value : Value) (size align : Nat) (model : ByteModel) :
    KeepsFresh (Sem.accessAddr op value size align model) := by
  unfold Sem.accessAddr
  memory_leaves

theorem bulkByteCount_fresh (op : String) (count : ValueId) :
    KeepsFresh (bulkByteCount op count) := by
  unfold bulkByteCount
  memory_leaves

theorem bulkPointer_fresh (op : String) (pointer : ValueId) (count : Nat) (model : ByteModel) :
    KeepsFresh (bulkPointer op pointer count model) := by
  unfold bulkPointer
  exact bind_fresh _ _ (lookup_fresh pointer) (fun value =>
    bind_fresh _ _ (rejectPartial_fresh value op) (fun _ => accessAddr_fresh op value count 1 model))

local macro "bulk_leaves" : tactic =>
  `(tactic| repeat (first
    | exact bulkByteCount_fresh _ _
    | exact bulkPointer_fresh _ _ _ _
    | exact pure_fresh _
    | exact throw_fresh _
    | exact get_fresh
    | exact lookup_fresh _
    | exact rejectPartial_fresh _ _
    | (exact modify_fresh _ (fun state fresh => sameSSA_fresh state _ fresh rfl rfl))
    | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split))

theorem semMemCopy_fresh (dst src bytes : ValueId) (overlap : Bool) (model : ByteModel) :
    KeepsFresh (semMemCopy dst src bytes overlap model) := by
  unfold semMemCopy
  dsimp only
  bulk_leaves

theorem semMemSet_fresh (dst byte bytes : ValueId) (model : ByteModel) :
    KeepsFresh (semMemSet dst byte bytes model) := by
  unfold semMemSet
  bulk_leaves

theorem semDealloc_fresh (pointer : ValueId) : KeepsFresh (semDealloc pointer) := by
  unfold semDealloc
  refine bind_fresh _ _ (lookup_fresh pointer) (fun value => ?_)
  split <;> try (memory_leaves; done)
  all_goals
    refine bind_fresh _ _ (pure_fresh _) (fun pair => ?_)
    refine getState_bind_fresh _ (fun before fresh => ?_)
    repeat (first
      | exact setState_fresh _ (sameSSA_fresh before _ fresh rfl rfl)
      | exact pure_fresh _
      | exact throw_fresh _
      | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
      | split)

theorem semGlobalAddr_fresh (global : GlobalId) (model : ByteModel) :
    KeepsFresh (semGlobalAddr global model) := by
  unfold semGlobalAddr
  refine getState_bind_fresh _ (fun before fresh => ?_)
  repeat (first
    | exact targetAddress_fresh _ _ _
    | exact fromMemoryExcept_fresh _
    | exact setState_fresh _ (sameSSA_fresh before _ fresh rfl rfl)
    | exact bindFresh_fresh _
    | exact pure_fresh _
    | exact throw_fresh _
    | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split)

theorem semGlobalAddrUsing_fresh (encode : Ty → Value → Except SemError (List UInt8))
    (globals : GlobalsTable) (global : GlobalId) (model : ByteModel) :
    KeepsFresh (semGlobalAddrUsing encode globals global model) := by
  unfold semGlobalAddrUsing
  refine getState_bind_fresh _ (fun before fresh => ?_)
  repeat (first
    | exact targetAddress_fresh _ _ _
    | exact fromMemoryExcept_fresh _
    | exact setState_fresh _ (sameSSA_fresh before _ fresh rfl rfl)
    | exact bindFresh_fresh _
    | exact pure_fresh _
    | exact throw_fresh _
    | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split)

theorem semPtrData_fresh (ty : Ty) (pointer : ValueId) (model : ByteModel) :
    KeepsFresh (semPtrData ty pointer model) := by
  unfold semPtrData
  memory_leaves

theorem semPtrMetadata_fresh (ty metadataTy : Ty) (pointer : ValueId) (model : ByteModel) :
    KeepsFresh (semPtrMetadata ty metadataTy pointer model) := by
  unfold semPtrMetadata
  memory_leaves

theorem semPtrFromParts_fresh (ty metadataTy : Ty) (data metadata : ValueId) (model : ByteModel) :
    KeepsFresh (semPtrFromParts ty metadataTy data metadata model) := by
  unfold semPtrFromParts
  memory_leaves

end TrustIr.SSAFreshMemoryExtra
