-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.SSAFreshDispatch
import TrustIr.Proofs.SSAFreshAggregate

namespace TrustIr.SSAFreshContext
open SSAFreshFrames SSAFreshStep SSAFreshInstructions SSAFreshMemory SSAFreshOwnership
  SSAFreshAtomic SSAFreshMemoryExtra SSAFreshDispatch SSAFreshAggregate

local macro "context_leaves" : tactic =>
  `(tactic| with_reducible (repeat' (first
    | apply load_fresh
    | apply store_fresh
    | apply atomicLoad_fresh
    | apply atomicStore_fresh
    | apply atomicRMW_fresh
    | apply cmpXchgExchange_fresh
    | apply semGlobalAddrInContext_fresh
    | apply stepInst_fresh
    | apply semBoolBinOpInst_fresh
    | apply semLoadUsing_fresh
    | apply semStoreUsing_fresh
    | apply semAllocaUsing_fresh
    | apply semHeapAllocUsing_fresh
    | apply semGEPUsing_fresh
    | apply semGlobalAddrUsing_fresh
    | apply semAtomicLoadUsing_fresh
    | apply semAtomicStoreUsing_fresh
    | apply semAtomicRMWUsing_fresh
    | apply semCmpXchgExchangeUsing_fresh
    | apply semExtractElementUsing_fresh
    | apply semInsertElementUsing_fresh
    | apply context_elementIndex_fresh
    | apply lookupLanes_fresh
    | exact semOpenFrame_fresh _
    | exact frameHandle_fresh _ _
    | exact setFrameState_fresh _ _
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
    | exact fromMemoryExcept_fresh _
    | exact mapM_fresh Sem.lookupValue _ lookup_fresh
    | (refine bind_fresh _ _ ?_ (fun value => ?_) <;> dsimp only)
    | intro value
    | (split <;> try dsimp only))))

private theorem context_BinOp_fresh (ctx : EvalContext) (op : BinOp) (ty : Ty) (lhs rhs : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.BinOp op ty lhs rhs)) := by
  cases ty <;> simp only [stepInstWithContext] <;> context_leaves
  all_goals context_leaves

private theorem context_UnOp_fresh (ctx : EvalContext) (op : UnOp) (ty : Ty) (operand : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.UnOp op ty operand)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Overflow_fresh (ctx : EvalContext) (op : OverflowOp) (ty : Ty) (lhs rhs : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.Overflow op ty lhs rhs)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_ICmp_fresh (ctx : EvalContext) (op : ICmpOp) (ty : Ty) (lhs rhs : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.ICmp op ty lhs rhs)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_FCmp_fresh (ctx : EvalContext) (op : FCmpOp) (ty : Ty) (lhs rhs : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.FCmp op ty lhs rhs)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

/-- The new reification leaf only reads a value and original headers before
    publishing a fresh pointer value. Pure refusals never alter the SSA state. -/
private theorem context_reify_item_fresh (ctx : EvalContext) (source : FuncId)
    (signature : FuncTyId) (operand : ValueId) :
    KeepsFresh (α := InstrResult) (do
      let value ← Sem.lookupValue operand
      Sem.rejectPartial value "ReifyFnPointer"
      match value with
      | .fnItem held =>
        if held != source then Sem.throwTypeError "ReifyFnPointer: item identity differs from source type"
        let declaration ← Sem.fromMemoryExcept (functionItemDeclaration ctx source)
        if declaration.signatureId != signature then
          Sem.throwTypeError "ReifyFnPointer: destination signature differs from item declaration"
        pure (.value (some (← Sem.bindFresh (.fnDef signature source))))
      | _ => Sem.throwTypeError "ReifyFnPointer: source is not a nominal function item") := by
  refine bind_fresh _ _ (lookup_fresh operand) (fun value => ?_)
  refine bind_fresh _ _ (rejectPartial_fresh value _) (fun _ => ?_)
  split
  · split
    · exact throwTypeError_fresh "ReifyFnPointer: item identity differs from source type"
    · try simp only [pure_bind]
      refine bind_fresh _ _ (fromMemoryExcept_fresh _) (fun declaration => ?_)
      split
      · exact throwTypeError_fresh "ReifyFnPointer: destination signature differs from item declaration"
      · try simp only [pure_bind]
        exact bind_fresh _ _ (bindFresh_fresh _) (fun _ => pure_fresh _)
  · exact throwTypeError_fresh "ReifyFnPointer: source is not a nominal function item"

/-- Source layout queries and byte encoding/decoding are pure computations.
    This leaf preserves the complete image and every refusal without reducing
    any source plan or recursive codec inside the freshness proof. -/
private theorem context_item_byte_cast_fresh (ctx : EvalContext) (source destination : Ty)
    (operand : ValueId) :
    KeepsFresh (α := InstrResult) (do
      let service ← match ctx.memoryService with
        | some service => pure service
        | none => Sem.throwTypeError "FnItem cast: original source layouts are absent"
      if service.model != ctx.byteModel then
        Sem.throwTypeError "FnItem cast: source layout target differs from evaluator target"
      let sourcePlan ← Sem.fromMemoryExcept (service.query source)
      let destinationPlan ← Sem.fromMemoryExcept (service.query destination)
      if sourcePlan.layout.size != destinationPlan.layout.size then
        Sem.throwTypeError "FnItem cast: byte extents differ"
      let value ← Sem.lookupValue operand
      Sem.rejectPartial value "FnItem cast"
      let image ← Sem.fromMemoryExcept
        (AggregateMemory.encode ctx.byteModel ctx.functionOrder sourcePlan value false)
      let state ← Sem.getState
      let result ← Sem.fromMemoryExcept
        (AggregateMemory.decode ctx.byteModel ctx.functionOrder state.memory destinationPlan image.bytes)
      pure (.value (some (← Sem.bindFresh result)))) := by
  cases servicePresent : ctx.memoryService with
  | none => exact throwTypeError_fresh "FnItem cast: original source layouts are absent"
  | some service =>
    simp only [servicePresent, pure_bind]
    split
    · exact throwTypeError_fresh "FnItem cast: source layout target differs from evaluator target"
    · try simp only [pure_bind]
      refine bind_fresh _ _ (fromMemoryExcept_fresh _) (fun sourcePlan => ?_)
      refine bind_fresh _ _ (fromMemoryExcept_fresh _) (fun destinationPlan => ?_)
      split
      · exact throwTypeError_fresh "FnItem cast: byte extents differ"
      · try simp only [pure_bind]
        refine bind_fresh _ _ (lookup_fresh operand) (fun value => ?_)
        refine bind_fresh _ _ (rejectPartial_fresh value _) (fun _ => ?_)
        refine bind_fresh _ _ (fromMemoryExcept_fresh _) (fun image => ?_)
        refine bind_fresh _ _ get_fresh (fun state => ?_)
        refine bind_fresh _ _ (fromMemoryExcept_fresh _) (fun result => ?_)
        exact bind_fresh _ _ (bindFresh_fresh result) (fun _ => pure_fresh _)

private theorem context_Cast_fresh (ctx : EvalContext) (op : CastOp) (srcTy dstTy : Ty) (operand : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.Cast op srcTy dstTy operand)) := by
  cases op
  case ReifyFnPointer =>
    cases srcTy
    case FnItem source =>
      cases dstTy
      case Func signature => exact context_reify_item_fresh ctx source signature operand
      all_goals
        simp only [stepInstWithContext]
        exact ite_fresh _ _ _ (context_item_byte_cast_fresh ctx _ _ operand)
          (stepInst_fresh _ _)
    all_goals
      simp only [stepInstWithContext]
      exact ite_fresh _ _ _ (context_item_byte_cast_fresh ctx _ _ operand)
        (stepInst_fresh _ _)
  all_goals
    simp only [stepInstWithContext]
    exact ite_fresh _ _ _ (context_item_byte_cast_fresh ctx _ _ operand)
      (stepInst_fresh _ _)

private theorem context_Load_fresh (ctx : EvalContext) (ty : Ty) (ptr : ValueId) (volatile : Bool) (align : Option Nat) :
    KeepsFresh (stepInstWithContext ctx (.Load ty ptr volatile align)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Store_fresh (ctx : EvalContext) (ty : Ty) (ptr : ValueId) (value : ValueId) (volatile : Bool) (align : Option Nat) :
    KeepsFresh (stepInstWithContext ctx (.Store ty ptr value volatile align)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Alloca_fresh (ctx : EvalContext) (ty : Ty) (count : Option ValueId) (align : Option Nat) :
    KeepsFresh (stepInstWithContext ctx (.Alloca ty count align)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_HeapAlloc_fresh (ctx : EvalContext) (ty : Ty) (count : Option ValueId) (align : Option Nat) (origin : AllocOrigin) :
    KeepsFresh (stepInstWithContext ctx (.HeapAlloc ty count align origin)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_GEP_fresh (ctx : EvalContext) (pointeeTy : Ty) (base : ValueId) (indices : List ValueId) (inbounds : Bool) :
    KeepsFresh (stepInstWithContext ctx (.GEP pointeeTy base indices inbounds)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_PtrData_fresh (ctx : EvalContext) (ptrTy : Ty) (ptr : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.PtrData ptrTy ptr)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_PtrMetadata_fresh (ctx : EvalContext) (ptrTy : Ty) (metadataTy : Ty) (ptr : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.PtrMetadata ptrTy metadataTy ptr)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_PtrFromParts_fresh (ctx : EvalContext) (ptrTy : Ty) (metadataTy : Ty) (data : ValueId) (metadata : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.PtrFromParts ptrTy metadataTy data metadata)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_GlobalAddr_fresh (ctx : EvalContext) (global : GlobalId) :
    KeepsFresh (stepInstWithContext ctx (.GlobalAddr global)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_AtomicLoad_fresh (ctx : EvalContext) (ty : Ty) (ptr : ValueId) (ordering : MemOrdering) :
    KeepsFresh (stepInstWithContext ctx (.AtomicLoad ty ptr ordering)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_AtomicStore_fresh (ctx : EvalContext) (ty : Ty) (ptr : ValueId) (value : ValueId) (ordering : MemOrdering) :
    KeepsFresh (stepInstWithContext ctx (.AtomicStore ty ptr value ordering)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_AtomicRMW_fresh (ctx : EvalContext) (op : AtomicRMWOp) (ty : Ty) (ptr : ValueId) (value : ValueId) (ordering : MemOrdering) :
    KeepsFresh (stepInstWithContext ctx (.AtomicRMW op ty ptr value ordering)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_CmpXchg_fresh (ctx : EvalContext) (ty : Ty) (ptr : ValueId) (expected desired : ValueId) (success failure : MemOrdering) (weak : Bool) :
    KeepsFresh (stepInstWithContext ctx (.CmpXchg ty ptr expected desired success failure weak)) := by
  cases weak <;> simp only [stepInstWithContext, Bool.false_eq_true, if_false, if_true]
  all_goals context_leaves

private theorem context_Fence_fresh (ctx : EvalContext) (ordering : MemOrdering) :
    KeepsFresh (stepInstWithContext ctx (.Fence ordering)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Br_fresh (ctx : EvalContext) (target : BlockId) (args : List ValueId) :
    KeepsFresh (stepInstWithContext ctx (.Br target args)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_CondBr_fresh (ctx : EvalContext) (cond : ValueId) (thenTarget : BlockId) (thenArgs : List ValueId) (elseTarget : BlockId) (elseArgs : List ValueId) :
    KeepsFresh (stepInstWithContext ctx (.CondBr cond thenTarget thenArgs elseTarget elseArgs)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Switch_fresh (ctx : EvalContext) (value : ValueId) (default_ : BlockId) (defaultArgs : List ValueId) (cases : List SwitchCase) (exhaustiveEnumUnreachable : Bool) :
    KeepsFresh (stepInstWithContext ctx (.Switch value default_ defaultArgs cases exhaustiveEnumUnreachable)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Call_fresh (ctx : EvalContext) (callee : FuncId) (args : List ValueId) :
    KeepsFresh (stepInstWithContext ctx (.Call callee args)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_CallIndirect_fresh (ctx : EvalContext) (callee : ValueId) (sig : FuncTyId) (args : List ValueId) (callingConv : CallingConv) :
    KeepsFresh (stepInstWithContext ctx (.CallIndirect callee sig args callingConv)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_CallCannotUnwind_fresh (ctx : EvalContext) (callee : FuncId) (args : List ValueId) :
    KeepsFresh (stepInstWithContext ctx (.CallCannotUnwind callee args)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_CallIndirectCannotUnwind_fresh (ctx : EvalContext) (callee : ValueId) (sig : FuncTyId) (args : List ValueId) (callingConv : CallingConv) :
    KeepsFresh (stepInstWithContext ctx (.CallIndirectCannotUnwind callee sig args callingConv)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Return_fresh (ctx : EvalContext) (values : List ValueId) :
    KeepsFresh (stepInstWithContext ctx (.Return values)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_ExtractField_fresh (ctx : EvalContext) (ty : Ty) (aggregate : ValueId) (field : Nat) :
    KeepsFresh (stepInstWithContext ctx (.ExtractField ty aggregate field)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_InsertField_fresh (ctx : EvalContext) (ty : Ty) (aggregate : ValueId) (field : Nat) (value : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.InsertField ty aggregate field value)) := by
  simp only [stepInstWithContext]
  refine bind_fresh _ _ (lookup_fresh aggregate) (fun held => ?_)
  refine bind_fresh _ _ (lookup_fresh value) (fun inserted => ?_)
  split <;> context_leaves
  all_goals context_leaves

private theorem context_MakeAggregate_fresh (ctx : EvalContext) (ty : Ty) (variant : Option Nat) (fields : List ValueId) :
    KeepsFresh (stepInstWithContext ctx (.MakeAggregate ty variant fields)) := by
  cases ty <;> simp only [stepInstWithContext] <;> context_leaves
  all_goals context_leaves

private theorem context_MakeClosure_fresh (ctx : EvalContext) (ty : ClosureTyId) (func : FuncId) (captures : List ValueId) :
    KeepsFresh (stepInstWithContext ctx (.MakeClosure ty func captures)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_ArraySplat_fresh (ctx : EvalContext) (ty : Ty) (value : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.ArraySplat ty value)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_ExtractElement_fresh (ctx : EvalContext) (ty : Ty) (array : ValueId) (index : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.ExtractElement ty array index)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_InsertElement_fresh (ctx : EvalContext) (ty : Ty) (array : ValueId) (index : ValueId) (value : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.InsertElement ty array index value)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Const_fresh (ctx : EvalContext) (ty : Ty) (value : Constant) :
    KeepsFresh (stepInstWithContext ctx (.Const ty value)) := by
  cases value <;> simp only [stepInstWithContext] <;> context_leaves
  all_goals context_leaves

private theorem context_NullPtr_fresh (ctx : EvalContext)  :
    KeepsFresh (stepInstWithContext ctx (.NullPtr)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Undef_fresh (ctx : EvalContext) (ty : Ty) :
    KeepsFresh (stepInstWithContext ctx (.Undef ty)) := by
  cases ty <;> simp only [stepInstWithContext] <;> context_leaves
  all_goals context_leaves

private theorem context_Assume_fresh (ctx : EvalContext) (cond : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.Assume cond)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Assert_fresh (ctx : EvalContext) (cond : ValueId) (kind : AssertKind) (site : Option PanicSite) :
    KeepsFresh (stepInstWithContext ctx (.Assert cond kind site)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Unreachable_fresh (ctx : EvalContext)  :
    KeepsFresh (stepInstWithContext ctx (.Unreachable)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_BoxDeref_fresh (ctx : EvalContext) (ptrTy : Ty) (pointee : BoxPointee)
    (operand : ValueId) (fact : BoxValidityFact) :
    KeepsFresh (stepInstWithContext ctx (.BoxDeref ptrTy pointee operand fact)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Copy_fresh (ctx : EvalContext) (ty : Ty) (operand : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.Copy ty operand)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Select_fresh (ctx : EvalContext) (ty : Ty) (cond : ValueId) (thenVal elseVal : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.Select ty cond thenVal elseVal)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_SeqMapAddK_fresh (ctx : EvalContext) (ty : Ty) (seq : ValueId) (k : Nat) :
    KeepsFresh (stepInstWithContext ctx (.SeqMapAddK ty seq k)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_SeqMapNot_fresh (ctx : EvalContext) (ty : Ty) (seq : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.SeqMapNot ty seq)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_SeqMap_fresh (ctx : EvalContext) (ty : Ty) (seq : ValueId) (fwd : FuncId) :
    KeepsFresh (stepInstWithContext ctx (.SeqMap ty seq fwd)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Borrow_fresh (ctx : EvalContext) (ptr : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.Borrow ptr)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_BorrowMut_fresh (ctx : EvalContext) (ptr : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.BorrowMut ptr)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_EndBorrow_fresh (ctx : EvalContext) (borrowPtr : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.EndBorrow borrowPtr)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Retain_fresh (ctx : EvalContext) (ptr : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.Retain ptr)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Release_fresh (ctx : EvalContext) (ptr : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.Release ptr)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_IsUnique_fresh (ctx : EvalContext) (ptr : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.IsUnique ptr)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Dealloc_fresh (ctx : EvalContext) (ptr : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.Dealloc ptr)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_MemCopy_fresh (ctx : EvalContext) (dst : ValueId) (src : ValueId) (bytes : ValueId) (overlap : Bool) :
    KeepsFresh (stepInstWithContext ctx (.MemCopy dst src bytes overlap)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_MemSet_fresh (ctx : EvalContext) (dst : ValueId) (byte : ValueId) (bytes : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.MemSet dst byte bytes)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Drop_fresh (ctx : EvalContext) (ty : Ty) (ptr : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.Drop ty ptr)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_OpenFrame_fresh (ctx : EvalContext) (def_ : BindingFrameDef) :
    KeepsFresh (stepInstWithContext ctx (.OpenFrame def_)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_BindSlot_fresh (ctx : EvalContext) (frame : ValueId) (slot : Nat) (value : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.BindSlot frame slot value)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_LoadSlot_fresh (ctx : EvalContext) (frame : ValueId) (slot : Nat) (ty : Ty) :
    KeepsFresh (stepInstWithContext ctx (.LoadSlot frame slot ty)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_CloseFrame_fresh (ctx : EvalContext) (frame : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.CloseFrame frame)) := by
  simp only [stepInstWithContext, semCloseFrame]
  context_leaves
  all_goals context_leaves

private theorem context_CoroSuspend_fresh (ctx : EvalContext) (frame : ValueId) (stateSlot : Nat) (nextState : Int) (value : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.CoroSuspend frame stateSlot nextState value)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Invoke_fresh (ctx : EvalContext) (callee : FuncId) (args : List ValueId) (normalDest : BlockId) (normalArgs : List ValueId) (unwindDest : BlockId) :
    KeepsFresh (stepInstWithContext ctx (.Invoke callee args normalDest normalArgs unwindDest)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_LandingPad_fresh (ctx : EvalContext) (isCleanup : Bool) (catchTypeIndices : List Nat) :
    KeepsFresh (stepInstWithContext ctx (.LandingPad isCleanup catchTypeIndices)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_Resume_fresh (ctx : EvalContext) (exn : ValueId) :
    KeepsFresh (stepInstWithContext ctx (.Resume exn)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_AssertInvoke_fresh (ctx : EvalContext) (cond : ValueId) (kind : AssertKind) (site : PanicSite) (normalDest : BlockId) (normalArgs : List ValueId) (unwindDest : BlockId) :
    KeepsFresh (stepInstWithContext ctx (.AssertInvoke cond kind site normalDest normalArgs unwindDest)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_DropInvoke_fresh (ctx : EvalContext) (ty : Ty) (ptr : ValueId) (normalDest : BlockId) (normalArgs : List ValueId) (unwindDest : BlockId) :
    KeepsFresh (stepInstWithContext ctx (.DropInvoke ty ptr normalDest normalArgs unwindDest)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_InvokeIndirect_fresh (ctx : EvalContext) (callee : ValueId) (sig : FuncTyId) (args : List ValueId) (callingConv : CallingConv) (normalDest : BlockId) (normalArgs : List ValueId) (unwindDest : BlockId) :
    KeepsFresh (stepInstWithContext ctx (.InvokeIndirect callee sig args callingConv normalDest normalArgs unwindDest)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

private theorem context_DialectOp_fresh (ctx : EvalContext) (op : DialectInst) :
    KeepsFresh (stepInstWithContext ctx (.DialectOp op)) := by
  simp only [stepInstWithContext]
  context_leaves
  all_goals context_leaves

/-- Context-directed instruction execution preserves freshness for every
    context and instruction. Context tables may be absent or return errors. -/
theorem stepInstWithContext_fresh (ctx : EvalContext) (inst : Inst) :
    KeepsFresh (stepInstWithContext ctx inst) := by
  cases inst with
  | BinOp op ty lhs rhs => exact context_BinOp_fresh ctx op ty lhs rhs
  | UnOp op ty operand => exact context_UnOp_fresh ctx op ty operand
  | Overflow op ty lhs rhs => exact context_Overflow_fresh ctx op ty lhs rhs
  | ICmp op ty lhs rhs => exact context_ICmp_fresh ctx op ty lhs rhs
  | FCmp op ty lhs rhs => exact context_FCmp_fresh ctx op ty lhs rhs
  | Cast op srcTy dstTy operand => exact context_Cast_fresh ctx op srcTy dstTy operand
  | Load ty ptr volatile align => exact context_Load_fresh ctx ty ptr volatile align
  | Store ty ptr value volatile align => exact context_Store_fresh ctx ty ptr value volatile align
  | Alloca ty count align => exact context_Alloca_fresh ctx ty count align
  | HeapAlloc ty count align origin => exact context_HeapAlloc_fresh ctx ty count align origin
  | GEP pointeeTy base indices inbounds => exact context_GEP_fresh ctx pointeeTy base indices inbounds
  | PtrData ptrTy ptr => exact context_PtrData_fresh ctx ptrTy ptr
  | PtrMetadata ptrTy metadataTy ptr => exact context_PtrMetadata_fresh ctx ptrTy metadataTy ptr
  | PtrFromParts ptrTy metadataTy data metadata => exact context_PtrFromParts_fresh ctx ptrTy metadataTy data metadata
  | GlobalAddr global => exact context_GlobalAddr_fresh ctx global
  | AtomicLoad ty ptr ordering => exact context_AtomicLoad_fresh ctx ty ptr ordering
  | AtomicStore ty ptr value ordering => exact context_AtomicStore_fresh ctx ty ptr value ordering
  | AtomicRMW op ty ptr value ordering => exact context_AtomicRMW_fresh ctx op ty ptr value ordering
  | CmpXchg ty ptr expected desired success failure weak => exact context_CmpXchg_fresh ctx ty ptr expected desired success failure weak
  | Fence ordering => exact context_Fence_fresh ctx ordering
  | Br target args => exact context_Br_fresh ctx target args
  | CondBr cond thenTarget thenArgs elseTarget elseArgs => exact context_CondBr_fresh ctx cond thenTarget thenArgs elseTarget elseArgs
  | Switch value default_ defaultArgs cases exhaustiveEnumUnreachable => exact context_Switch_fresh ctx value default_ defaultArgs cases exhaustiveEnumUnreachable
  | Call callee args => exact context_Call_fresh ctx callee args
  | CallIndirect callee sig args callingConv => exact context_CallIndirect_fresh ctx callee sig args callingConv
  | CallCannotUnwind callee args => exact context_CallCannotUnwind_fresh ctx callee args
  | CallIndirectCannotUnwind callee sig args callingConv => exact context_CallIndirectCannotUnwind_fresh ctx callee sig args callingConv
  | Return values => exact context_Return_fresh ctx values
  | ExtractField ty aggregate field => exact context_ExtractField_fresh ctx ty aggregate field
  | InsertField ty aggregate field value => exact context_InsertField_fresh ctx ty aggregate field value
  | MakeAggregate ty variant fields => exact context_MakeAggregate_fresh ctx ty variant fields
  | MakeClosure ty func captures => exact context_MakeClosure_fresh ctx ty func captures
  | ArraySplat ty value => exact context_ArraySplat_fresh ctx ty value
  | ExtractElement ty array index => exact context_ExtractElement_fresh ctx ty array index
  | InsertElement ty array index value => exact context_InsertElement_fresh ctx ty array index value
  | Const ty value => exact context_Const_fresh ctx ty value
  | NullPtr => exact context_NullPtr_fresh ctx
  | Undef ty => exact context_Undef_fresh ctx ty
  | Assume cond => exact context_Assume_fresh ctx cond
  | Assert cond kind site => exact context_Assert_fresh ctx cond kind site
  | Unreachable => exact context_Unreachable_fresh ctx
  | Copy ty operand => exact context_Copy_fresh ctx ty operand
  | BoxDeref ptrTy pointee operand fact => exact context_BoxDeref_fresh ctx ptrTy pointee operand fact
  | Select ty cond thenVal elseVal => exact context_Select_fresh ctx ty cond thenVal elseVal
  | SeqMapAddK ty seq k => exact context_SeqMapAddK_fresh ctx ty seq k
  | SeqMapNot ty seq => exact context_SeqMapNot_fresh ctx ty seq
  | SeqMap ty seq fwd => exact context_SeqMap_fresh ctx ty seq fwd
  | Borrow ptr => exact context_Borrow_fresh ctx ptr
  | BorrowMut ptr => exact context_BorrowMut_fresh ctx ptr
  | EndBorrow borrowPtr => exact context_EndBorrow_fresh ctx borrowPtr
  | Retain ptr => exact context_Retain_fresh ctx ptr
  | Release ptr => exact context_Release_fresh ctx ptr
  | IsUnique ptr => exact context_IsUnique_fresh ctx ptr
  | Dealloc ptr => exact context_Dealloc_fresh ctx ptr
  | MemCopy dst src bytes overlap => exact context_MemCopy_fresh ctx dst src bytes overlap
  | MemSet dst byte bytes => exact context_MemSet_fresh ctx dst byte bytes
  | Drop ty ptr => exact context_Drop_fresh ctx ty ptr
  | OpenFrame def_ => exact context_OpenFrame_fresh ctx def_
  | BindSlot frame slot value => exact context_BindSlot_fresh ctx frame slot value
  | LoadSlot frame slot ty => exact context_LoadSlot_fresh ctx frame slot ty
  | CloseFrame frame => exact context_CloseFrame_fresh ctx frame
  | CoroSuspend frame stateSlot nextState value => exact context_CoroSuspend_fresh ctx frame stateSlot nextState value
  | Invoke callee args normalDest normalArgs unwindDest => exact context_Invoke_fresh ctx callee args normalDest normalArgs unwindDest
  | LandingPad isCleanup catchTypeIndices => exact context_LandingPad_fresh ctx isCleanup catchTypeIndices
  | Resume exn => exact context_Resume_fresh ctx exn
  | AssertInvoke cond kind site normalDest normalArgs unwindDest => exact context_AssertInvoke_fresh ctx cond kind site normalDest normalArgs unwindDest
  | DropInvoke ty ptr normalDest normalArgs unwindDest => exact context_DropInvoke_fresh ctx ty ptr normalDest normalArgs unwindDest
  | InvokeIndirect callee sig args callingConv normalDest normalArgs unwindDest => exact context_InvokeIndirect_fresh ctx callee sig args callingConv normalDest normalArgs unwindDest
  | DialectOp op => exact context_DialectOp_fresh ctx op

end TrustIr.SSAFreshContext
