-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SSAFreshOwnership

namespace TrustIr.SSAFreshAtomic
open SSAFreshFrames SSAFreshStep SSAFreshInstructions SSAFreshMemory

private theorem typeErrorFresh {α : Type} (message : String) :
    KeepsFresh (Sem.throwTypeError message : Sem α) := throw_fresh _

private theorem undefinedFresh {α : Type} (message : String) :
    KeepsFresh (Sem.throwUB message : Sem α) := throw_fresh _

private theorem unsupportedFresh {α : Type} (feature : UnsupportedFeature) (message : String) :
    KeepsFresh (Sem.throwUnsupported feature message : Sem α) := throw_fresh _

local macro "atomic_leaves" : tactic =>
  `(tactic| with_reducible (repeat' (first
    | exact expectPointer_fresh _ _
    | exact accessAlign_fresh _ _ _ _
    | exact checkedAccess_fresh _ _ _ _ _ _
    | exact pure_fresh _
    | apply typeErrorFresh
    | apply undefinedFresh
    | apply unsupportedFresh
    | exact throw_fresh _
    | exact bindFresh_fresh _
    | exact get_fresh
    | exact lookup_fresh _
    | exact rejectPartial_fresh _ _
    | (exact modify_fresh _ (fun state fresh => sameSSA_fresh state _ fresh rfl rfl))
    | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
    | (split <;> try dsimp only))))

theorem semAtomicLoadUsing_fresh (decode : Memory → List UInt8 → Except SemError Value)
    (ty : Ty) (pointer : ValueId) (ordering : MemOrdering) (model : ByteModel) :
    KeepsFresh (semAtomicLoadUsing decode ty pointer ordering model) := by
  unfold semAtomicLoadUsing
  atomic_leaves

theorem semAtomicStoreUsing_fresh (encode : Value → Except SemError (List UInt8))
    (ty : Ty) (pointer value : ValueId) (ordering : MemOrdering) (model : ByteModel) :
    KeepsFresh (semAtomicStoreUsing encode ty pointer value ordering model) := by
  unfold semAtomicStoreUsing
  atomic_leaves

theorem semAtomicRMWUsing_fresh (decode : Memory → List UInt8 → Except SemError Value)
    (encode : Value → Except SemError (List UInt8)) (op : AtomicRMWOp)
    (ty : Ty) (pointer value : ValueId) (ordering : MemOrdering) (model : ByteModel) :
    KeepsFresh (semAtomicRMWUsing decode encode op ty pointer value ordering model) := by
  unfold semAtomicRMWUsing
  atomic_leaves

private def cmpTail (encode : Value → Except SemError (List UInt8)) (ty : Ty)
    (addr : Addr) (currentVal expectedVal : Value) (desiredId : ValueId) : Sem (Value × Bool) := do
  -- The comparison INSPECTS `expected`: a poison `expected` is UB, never a
  -- silent "unequal" (mirror interpret.rs `Inst::CmpXchg`, WS2.10 review).
  Sem.rejectPartial expectedVal "CmpXchg expected"
  -- The comparison is BITWISE (LLVM `cmpxchg`, the interpreter's value
  -- equality over `FloatBits`): a float compares its IEEE pattern at `ty`,
  -- so `+0.0` and `-0.0` differ. A NaN refuses (`floatToBitsAt`): its payload
  -- is unobservable in Lean 4.8.0, so neither answer can be vouched for.
  -- (Before WS2.23 a float never compared equal, so an F32/F64 `cmpxchg`
  -- whose expected value matched memory reported failure and skipped the
  -- write.)
  let isEqual ← match currentVal, expectedVal with
    | .float a, .float b =>
      match floatToBitsAt ty a, floatToBitsAt ty b with
      | .ok x, .ok y => pure (x == y)
      | .error e, _ => throw e
      | _, .error e => throw e
    | .int _ a, .int _ b => pure (a == b)
    | .bool a,  .bool b  => pure (a == b)
    | .ptr a p, .ptr b q => pure (a == b && p == q)
    | .fnDef a f, .fnDef b g => pure (a == b && f == g)
    | .nullPtr, .nullPtr => pure true
    | _, _               => pure false
  -- If equal, write desired; otherwise leave memory unchanged
  if isEqual then do
    let desiredVal ← Sem.lookupValue desiredId
    -- The successful exchange is a STRICT store: poison `desired` is UB.
    Sem.rejectPartial desiredVal "CmpXchg"
    let desiredEncoded ← match encode desiredVal with
      | .ok bs   => pure bs
      | .error e => throw e
    let s' ← Sem.getState
    let mem' := s'.memory.writeBytes addr desiredEncoded
    Sem.modifyState fun st => { st with memory := mem' }
  pure (currentVal, isEqual)

private theorem cmpTail_fresh (encode : Value → Except SemError (List UInt8)) (ty : Ty)
    (addr : Addr) (currentVal expectedVal : Value) (desiredId : ValueId) :
    KeepsFresh (cmpTail encode ty addr currentVal expectedVal desiredId) := by
  unfold cmpTail
  atomic_leaves
  all_goals atomic_leaves

theorem semCmpXchgExchangeUsing_fresh (decode : Memory → List UInt8 → Except SemError Value)
    (encode : Value → Except SemError (List UInt8))
    (ty : Ty) (pointer expected desired : ValueId) (model : ByteModel) :
    KeepsFresh (semCmpXchgExchangeUsing decode encode ty pointer expected desired model) := by
  change KeepsFresh (do
  -- Read the current value from memory
  let ptrVal ← Sem.lookupValue pointer
  Sem.rejectPartial ptrVal "CmpXchg"
  let (ptrAddr, ptrAlloc) ← Sem.expectPointer "CmpXchg" ptrVal
  let byteSize ← match (ty.byteSizeFor model) with
    | some s => pure s
    | none   => Sem.throwUnsupported .layout "CmpXchg: type has no byte size"
  -- An atomic access is a strict access at the type's natural alignment
  -- through the operand's provenance (interpret.rs `eval_load(.., None, strict)`).
  let alignment ← Sem.accessAlign "CmpXchg" ty none model
  let addr ← Sem.checkedAccess "CmpXchg" ptrAddr ptrAlloc byteSize alignment model
  let s ← Sem.getState
  -- Read current value
  let bytes ← match s.memory.readBytes addr byteSize with
    | some bs => pure bs
    | none    => Sem.throwUB "CmpXchg: reading uninitialized memory"
  let currentVal ← match decode s.memory bytes with
    | .ok v    => pure v
    | .error e => throw e
  -- Compare with expected
  let expectedVal ← Sem.lookupValue expected
  cmpTail encode ty addr currentVal expectedVal desired)
  repeat' (first
    | with_reducible apply cmpTail_fresh
    | with_reducible exact expectPointer_fresh _ _
    | with_reducible exact accessAlign_fresh _ _ _ _
    | with_reducible exact checkedAccess_fresh _ _ _ _ _ _
    | with_reducible exact pure_fresh _
    | exact throw_fresh _
    | with_reducible exact get_fresh
    | with_reducible exact lookup_fresh _
    | with_reducible exact rejectPartial_fresh _ _
    | (with_reducible refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
    | (split <;> try dsimp only))

theorem semCmpXchg_fresh (ty : Ty) (pointer expected desired : ValueId)
    (success failure : MemOrdering) (model : ByteModel) :
    KeepsFresh (semCmpXchg ty pointer expected desired success failure model) := by
  unfold semCmpXchg semCmpXchgExchange
  exact bind_fresh _ _ (semCmpXchgExchangeUsing_fresh _ _ _ _ _ _ _) (fun _ => bindFreshPair_fresh _ _)

theorem semFence_fresh (ordering : MemOrdering) : KeepsFresh (semFence ordering) := pure_fresh _

end TrustIr.SSAFreshAtomic
