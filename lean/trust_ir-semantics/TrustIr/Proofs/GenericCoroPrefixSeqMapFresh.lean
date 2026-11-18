-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixSeqMap
import TrustIr.Proofs.GenericCoroPrefixFresh
import TrustIr.Proofs.GenericCoroCell
import TrustIr.Proofs.AggregateMemoryFrames

namespace TrustIr.GenericCoro.Prefix
open SSAFreshStep

private theorem loadMemoryValue_equivariant (ctx : EvalContext) (ty : Ty) (pointer : Value) :
    HeldMemoryFrames.Equivariant (ctx.loadMemoryValue ty pointer) := by
  unfold EvalContext.loadMemoryValue EvalContext.loadMemoryValueAligned
  cases ctx.memoryRoute ty with
  | original closure service => exact HeldMemoryFrames.originalClosureLoadValue_eqv _ _ _ _ _ _ _
  | descriptor service => exact HeldMemoryFrames.aggregateLoadValue_eqv _ _ _ _ _ _ _
  | scalar => exact HeldMemoryFrames.semLoadValueUsing_eqv _ _ _ _ _ _

private theorem storeMemoryValue_equivariant (ctx : EvalContext) (ty : Ty) (pointer value : Value) :
    HeldMemoryFrames.Equivariant (ctx.storeMemoryValue ty pointer value) := by
  unfold EvalContext.storeMemoryValue EvalContext.storeMemoryValueAligned
  cases ctx.memoryRoute ty with
  | original closure service => exact HeldMemoryFrames.originalClosureStoreValue_eqv _ _ _ _ _ _ _ _
  | descriptor service => exact HeldMemoryFrames.aggregateStoreValue_eqv _ _ _ _ _ _ _ _
  | scalar => exact HeldMemoryFrames.semStoreValueUsing_eqv _ _ _ _ _ _ _ _

/-- The allocator's identity writer leaves initialization to the actual
    typed store. No SSA alias or synthetic byte image is introduced. -/
private theorem seqMapElement_allocate (ctx : EvalContext) (elemTy : Ty)
    (invoke : Value → Sem (List Value)) (elem : Value) :
    seqMapElement ctx elemTy invoke elem = (do
      let layout ← Sem.fromMemoryExcept (ctx.memoryLayout elemTy)
      let pointer ← allocateCell ctx.byteModel layout.size layout.alignment (fun memory _ => memory)
      ctx.storeMemoryValue elemTy pointer elem
      let _ ← invoke pointer
      ctx.loadMemoryValue elemTy pointer) := by
  simp only [seqMapElement, allocateCell, bind_assoc, pure_bind]

/-- The exact source-derived cell operations commute with every caller SSA
    replacement, including arbitrary layout/codec failures and world effects. -/
theorem seqMapElement_equivariant (ctx : EvalContext) (elemTy : Ty)
    (invoke : Value → Sem (List Value))
    (equivariant : ∀ pointer, HeldMemoryFrames.Equivariant (invoke pointer)) (elem : Value) :
    HeldMemoryFrames.Equivariant (seqMapElement ctx elemTy invoke elem) := by
  rw [seqMapElement_allocate]
  refine HeldMemoryFrames.bind_eqv _ _ (HeldMemoryFrames.memoryExcept_eqv _) ?_; intro layout
  refine HeldMemoryFrames.bind_eqv _ _ (allocateCell_equivariant _ _ _ _) ?_; intro pointer
  refine HeldMemoryFrames.bind_eqv _ _ (storeMemoryValue_equivariant _ _ _ _) ?_; intro _
  refine HeldMemoryFrames.bind_eqv _ _ (equivariant pointer) ?_; intro _
  exact loadMemoryValue_equivariant _ _ _

theorem seqMapElement_fresh (ctx : EvalContext) (elemTy : Ty)
    (invoke : Value → Sem (List Value))
    (equivariant : ∀ pointer, HeldMemoryFrames.Equivariant (invoke pointer)) (elem : Value) :
    KeepsFresh (seqMapElement ctx elemTy invoke elem) :=
  equivariant_fresh _ (seqMapElement_equivariant ctx elemTy invoke equivariant elem)

private theorem seqMapInvoke_equivariant (ctx : EvalContext) (header : FunctionHeader) (id : FuncId)
    (invoke : EvalFunction → Value → Sem (List Value))
    (equivariant : ∀ callee pointer, HeldMemoryFrames.Equivariant (invoke callee pointer))
    (pointer : Value) :
    HeldMemoryFrames.Equivariant (seqMapInvoke ctx header id invoke pointer) := by
  unfold seqMapInvoke EvalContext.lookupDirectCallee requireUntypedAbi
  with_reducible (repeat' (first
    | exact HeldMemoryFrames.pure_eqv _
    | exact HeldMemoryFrames.throw_eqv _
    | (unfold Sem.throwTypeError; exact HeldMemoryFrames.throw_eqv _)
    | (unfold Sem.throwUnsupported; exact HeldMemoryFrames.throw_eqv _)
    | exact equivariant _ _
    | (refine HeldMemoryFrames.bind_eqv _ _ ?_ (fun value => ?_) <;> dsimp only)
    | (split <;> try dsimp only)))

private theorem seqMapApply_equivariant (ctx : EvalContext) (inst : Inst)
    (header : FunctionHeader) (id : FuncId) (elemTy : Ty)
    (invoke : EvalFunction → Value → Sem (List Value))
    (equivariant : ∀ callee pointer, HeldMemoryFrames.Equivariant (invoke callee pointer)) (elem : Value) :
    HeldMemoryFrames.Equivariant (seqMapApply ctx inst header id elemTy invoke elem) := by
  unfold seqMapApply
  refine HeldMemoryFrames.bind_eqv _ _ (HeldMemoryFrames.memoryExcept_eqv _) ?_; intro _
  exact seqMapElement_equivariant _ _ _
    (seqMapInvoke_equivariant ctx header id invoke equivariant) elem

private theorem seqMapElements_equivariant (ctx : EvalContext) (inst : Inst)
    (header : FunctionHeader) (id : FuncId) (elemTy : Ty)
    (invoke : EvalFunction → Value → Sem (List Value))
    (equivariant : ∀ callee pointer, HeldMemoryFrames.Equivariant (invoke callee pointer))
    (elems mapped : List Value) :
    HeldMemoryFrames.Equivariant (forIn elems mapped (fun elem mapped => do
      let value ← seqMapApply ctx inst header id elemTy invoke elem
      pure (.yield (mapped ++ [value])))) := by
  apply forIn_equivariant
  intro elem _ mapped
  exact HeldMemoryFrames.bind_eqv _ _
    (seqMapApply_equivariant ctx inst header id elemTy invoke equivariant elem)
    (fun _ => HeldMemoryFrames.pure_eqv _)

/-- Complete iteration preserves high-water freshness. Empty maps perform
    only header checks and actual result publication, just as production. -/
theorem seqMapRun_fresh (ctx : EvalContext) (inst : Inst) (dests : List ValueId)
    (id : FuncId) (elems : List Value)
    (invoke : EvalFunction → Value → Sem (List Value))
    (equivariant : ∀ callee pointer, HeldMemoryFrames.Equivariant (invoke callee pointer)) :
    KeepsFresh (seqMapRun ctx inst dests id elems invoke) := by
  have loopFresh (header : FunctionHeader) (elemTy : Ty) :
      KeepsFresh (forIn elems [] (fun elem mapped => do
        let value ← seqMapApply ctx inst header id elemTy invoke elem
        pure (.yield (mapped ++ [value])))) :=
    equivariant_fresh _ (seqMapElements_equivariant ctx inst header id elemTy invoke equivariant elems [])
  unfold seqMapRun EvalContext.lookupFunctionHeader requireUntypedAbi
  with_reducible (repeat' (first
    | exact pure_fresh _
    | exact throw_fresh _
    | exact equivariant_fresh _ (HeldMemoryFrames.memoryExcept_eqv _)
    | (unfold Sem.throwTypeError; exact throw_fresh _)
    | (unfold Sem.throwUnsupported; exact throw_fresh _)
    | exact loopFresh _ _
    | exact bindCallResults_fresh _ _ _ _
    | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
    | (split <;> try dsimp only)))

/-- Arbitrary recursive callbacks use the actual saved-frame protocol. No
    freshness, successful call, layout validity or caller premise is added. -/
theorem seqMapStep_fresh (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (inst : Inst) (dests : List ValueId)
    (id : FuncId) (elems : List Value) :
    KeepsFresh (seqMapStep recurse ctx depth strat inst dests id elems) := by
  cases depth with
  | zero => exact throw_fresh _
  | succ depth =>
    rw [seqMapStep_framed]
    apply seqMapRun_fresh
    intro callee pointer
    exact callFrameWith_equivariant _ _

end TrustIr.GenericCoro.Prefix
