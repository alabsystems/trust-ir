-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SSAFreshDispatch

namespace TrustIr.SSAFreshAggregate
open SSAFreshFrames SSAFreshStep SSAFreshInstructions SSAFreshMemory SSAFreshMemoryExtra SSAFreshDispatch

theorem loadValue_fresh (service : AggregateMemory.Service) (order : FunctionAddressOrder)
    (ty : Ty) (pointer : Value) (strict : Bool) (align : Option Nat) (model : ByteModel) :
    KeepsFresh (AggregateMemory.loadValue service order ty pointer strict align model) :=
  equivariant_fresh _ (HeldMemoryFrames.aggregateLoadValue_eqv service order ty pointer strict align model)

theorem storeValue_fresh (service : AggregateMemory.Service) (order : FunctionAddressOrder)
    (ty : Ty) (pointer value : Value) (strict : Bool) (align : Option Nat) (model : ByteModel) :
    KeepsFresh (AggregateMemory.storeValue service order ty pointer value strict align model) :=
  equivariant_fresh _ (HeldMemoryFrames.aggregateStoreValue_eqv service order ty pointer value strict align model)

theorem load_fresh (service : AggregateMemory.Service) (order : FunctionAddressOrder)
    (ty : Ty) (pointer : ValueId) (strict : Bool) (align : Option Nat) (model : ByteModel) :
    KeepsFresh (AggregateMemory.load service order ty pointer strict align model) := by
  unfold AggregateMemory.load
  exact bind_fresh _ _ (lookup_fresh pointer) (fun held =>
    bind_fresh _ _ (loadValue_fresh service order ty held strict align model) bindFresh_fresh)

theorem store_fresh (service : AggregateMemory.Service) (order : FunctionAddressOrder)
    (ty : Ty) (pointer value : ValueId) (strict : Bool) (align : Option Nat) (model : ByteModel) :
    KeepsFresh (AggregateMemory.store service order ty pointer value strict align model) := by
  unfold AggregateMemory.store
  exact bind_fresh _ _ (lookup_fresh pointer) (fun held =>
    bind_fresh _ _ (lookup_fresh value) (fun input =>
      storeValue_fresh service order ty held input strict align model))

local macro "aggregate_leaves" : tactic =>
  `(tactic| with_reducible (repeat' (first
    | apply loadValue_fresh
    | apply storeValue_fresh
    | apply load_fresh
    | apply store_fresh
    | apply throwUB_fresh
    | apply throwTypeError_fresh
    | apply throwUnsupported_fresh
    | exact throw_fresh _
    | exact pure_fresh _
    | exact bindFresh_fresh _
    | exact lookup_fresh _
    | exact rejectPartial_fresh _ _
    | exact fromMemoryExcept_fresh _
    | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
    | (split <;> try dsimp only))))

theorem atomicLoad_fresh (service : AggregateMemory.Service) (order : FunctionAddressOrder)
    (ty : Ty) (pointer : ValueId) (ordering : MemOrdering) (model : ByteModel) :
    KeepsFresh (AggregateMemory.atomicLoad service order ty pointer ordering model) := by
  unfold AggregateMemory.atomicLoad
  aggregate_leaves

theorem atomicStore_fresh (service : AggregateMemory.Service) (order : FunctionAddressOrder)
    (ty : Ty) (pointer value : ValueId) (ordering : MemOrdering) (model : ByteModel) :
    KeepsFresh (AggregateMemory.atomicStore service order ty pointer value ordering model) := by
  unfold AggregateMemory.atomicStore
  aggregate_leaves

theorem atomicRMW_fresh (service : AggregateMemory.Service) (order : FunctionAddressOrder)
    (op : AtomicRMWOp) (ty : Ty) (pointer value : ValueId) (ordering : MemOrdering) (model : ByteModel) :
    KeepsFresh (AggregateMemory.atomicRMW service order op ty pointer value ordering model) := by
  unfold AggregateMemory.atomicRMW
  aggregate_leaves

theorem cmpXchgExchange_fresh (service : AggregateMemory.Service) (order : FunctionAddressOrder)
    (ty : Ty) (pointer expected desired : ValueId) (model : ByteModel) :
    KeepsFresh (AggregateMemory.cmpXchgExchange service order ty pointer expected desired model) := by
  unfold AggregateMemory.cmpXchgExchange
  aggregate_leaves

theorem semGlobalAddrInContext_fresh (ctx : EvalContext) (global : GlobalId) :
    KeepsFresh (semGlobalAddrInContext ctx global) := by
  unfold semGlobalAddrInContext
  dsimp only
  split
  · exact semGlobalAddrUsing_fresh _ _ _ _
  · refine getState_bind_fresh _ (fun before fresh => ?_)
    repeat' (first
      | exact targetAddress_fresh _ _ _
      | exact fromMemoryExcept_fresh _
      | exact setState_fresh _ (sameSSA_fresh before _ fresh rfl rfl)
      | exact bindFresh_fresh _
      | exact pure_fresh _
      | exact throw_fresh _
      | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
      | (split <;> try dsimp only))

end TrustIr.SSAFreshAggregate
