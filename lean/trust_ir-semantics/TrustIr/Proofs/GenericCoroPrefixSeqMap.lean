-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixCalls

namespace TrustIr.GenericCoro.Prefix

/-- Exact production SeqMap branch: original header checks precede the loop;
    layout, cells, decoder errors and executable callees are per element. -/
def seqMapStep (recurse : Recurse) (ctx : EvalContext) (callDepth : Nat)
    (strat : PanicStrategy) (inst : Inst) (resultDests : List ValueId)
    (fwdId : FuncId) (elems : List Value) : Sem (ForInStep Unit) := do
  match callDepth with
  | 0 => throw SemError.outOfFuel
  | callDepth + 1 => do
    let header ← ctx.lookupFunctionHeader fwdId
    requireUntypedAbi header.signature.abi
    if header.signature.isVararg then
      Sem.throwTypeError "SeqMap: element function must not be variadic"
    let elemTy ← match header.signature.params, header.signature.returns with
      | [Ty.RefMut element], [] => pure element
      | _, _ => Sem.throwTypeError "SeqMap: element function must have signature fn(&mut elem)"
    let mut mapped : List Value := []
    for elem in elems do
      Sem.fromMemoryExcept (ctx.checkSeqMapElement inst elemTy elem)
      -- Empty maps perform none of these per-element operations.
      let layout ← Sem.fromMemoryExcept (ctx.memoryLayout elemTy)
      let before ← Sem.getState
      Sem.checkTargetAllocation ctx.byteModel before.memory layout.size layout.alignment 0
      let (cellAddr, memory) := before.memory.alloc layout.size layout.alignment 0 .rustStack
      let allocId : AllocId := ⟨before.memory.nextAllocId⟩
      Sem.setState { before with memory := memory, permissions := before.permissions.set allocId .owned }
      let pointer := Value.ptr cellAddr (some allocId)
      ctx.storeMemoryValue elemTy pointer elem
      if let some error := ctx.functionErrors fwdId then throw error
      let callee ← ctx.lookupDirectCallee fwdId
        "SeqMap: element function is declared without a body" "SeqMap: undefined element function"
      if !(header.matches callee) then
        Sem.throwTypeError "SeqMap: original header does not match executable function metadata"
      requireUntypedAbi callee.body.abi
      let callerState ← Sem.getState
      let frame := saveFrame callerState none
      Sem.setState { callerState with locals := ValueMap.empty, nextValueId := 0 }
      let retVals ← recurse (ctx.forFunction callee) callDepth
        callee.cfg callee.entryBlock [pointer] strat
      match checkReturnArity retVals callee.body.returnTys with
      | .ok () => pure ()
      | .error msg => Sem.throwTypeError ("SeqMap: " ++ msg)
      Sem.rejectPoisonValues retVals "SeqMap returns"
      let calleeState ← Sem.getState
      Sem.setState (restoreFrame calleeState frame [])
      let newElem ← ctx.loadMemoryValue elemTy pointer
      mapped := mapped ++ [newElem]
    ctx.bindCallResults inst resultDests [Value.sequence mapped]
  pure (.yield ())

/-- Exact return checks retain the production SeqMap diagnostic. -/
def seqMapReturns (returnTys : List Ty) (values : List Value) : Sem Unit := do
  match checkReturnArity values returnTys with
  | .ok () => pure ()
  | .error msg => Sem.throwTypeError (trustIrStringBuild ("SeqMap: " ++ msg))
  Sem.rejectPoisonValues values "SeqMap returns"

theorem seqMapReturns_equivariant (returnTys : List Ty) (values : List Value) :
    HeldMemoryFrames.Equivariant (seqMapReturns returnTys values) := by
  unfold seqMapReturns Sem.rejectPoisonValues
  with_reducible (repeat' (first
    | exact HeldMemoryFrames.pure_eqv _
    | exact HeldMemoryFrames.throw_eqv _
    | (unfold Sem.throwTypeError; exact HeldMemoryFrames.throw_eqv _)
    | (unfold Sem.throwUB; exact HeldMemoryFrames.throw_eqv _)
    | (refine HeldMemoryFrames.bind_eqv _ _ ?_ (fun value => ?_) <;> dsimp only)
    | (split <;> try dsimp only)))

/-- A held element's exact allocation, typed store, opaque callback and load.
    No instruction or SSA declaration is fabricated inside the cell helper. -/
def seqMapElement (ctx : EvalContext) (elemTy : Ty)
    (invoke : Value → Sem (List Value)) (elem : Value) : Sem Value := do
  let layout ← Sem.fromMemoryExcept (ctx.memoryLayout elemTy)
  let before ← Sem.getState
  Sem.checkTargetAllocation ctx.byteModel before.memory layout.size layout.alignment 0
  let (cellAddr, memory) := before.memory.alloc layout.size layout.alignment 0 .rustStack
  let allocId : AllocId := ⟨before.memory.nextAllocId⟩
  Sem.setState { before with memory := memory, permissions := before.permissions.set allocId .owned }
  let pointer := Value.ptr cellAddr (some allocId)
  ctx.storeMemoryValue elemTy pointer elem
  let _ ← invoke pointer
  ctx.loadMemoryValue elemTy pointer

theorem seqMapElement_scoped (base : EvalContext)
    (functions : FuncId → Option EvalFunction) (types : Option LocalTypeTable)
    (elemTy : Ty) (invoke : Value → Sem (List Value)) (elem : Value) :
    seqMapElement (scopedContext base functions types) elemTy invoke elem =
      seqMapElement base elemTy invoke elem := rfl

/-- Original decoder refusal and executable-header checks occur after the
    cell's typed store, exactly when the element is actually applied. -/
def seqMapInvoke (ctx : EvalContext) (header : FunctionHeader) (id : FuncId)
    (invoke : EvalFunction → Value → Sem (List Value)) (pointer : Value) : Sem (List Value) := do
  if let some error := ctx.functionErrors id then throw error
  let callee ← ctx.lookupDirectCallee id
    "SeqMap: element function is declared without a body" "SeqMap: undefined element function"
  if !(header.matches callee) then
    Sem.throwTypeError "SeqMap: original header does not match executable function metadata"
  requireUntypedAbi callee.body.abi
  invoke callee pointer

def seqMapApply (ctx : EvalContext) (inst : Inst) (header : FunctionHeader) (id : FuncId)
    (elemTy : Ty) (invoke : EvalFunction → Value → Sem (List Value)) (elem : Value) : Sem Value := do
  Sem.fromMemoryExcept (ctx.checkSeqMapElement inst elemTy elem)
  seqMapElement ctx elemTy (seqMapInvoke ctx header id invoke) elem

def seqMapRun (ctx : EvalContext) (inst : Inst) (resultDests : List ValueId)
    (fwdId : FuncId) (elems : List Value)
    (invoke : EvalFunction → Value → Sem (List Value)) : Sem (ForInStep Unit) := do
  let header ← ctx.lookupFunctionHeader fwdId
  requireUntypedAbi header.signature.abi
  if header.signature.isVararg then
    Sem.throwTypeError "SeqMap: element function must not be variadic"
  let elemTy ← match header.signature.params, header.signature.returns with
    | [Ty.RefMut element], [] => pure element
    | _, _ => Sem.throwTypeError "SeqMap: element function must have signature fn(&mut elem)"
  let mapped ← forIn elems [] (fun elem mapped => do
    let newElem ← seqMapApply ctx inst header fwdId elemTy invoke elem
    pure (.yield (mapped ++ [newElem])))
  ctx.bindCallResults inst resultDests [Value.sequence mapped]
  pure (.yield ())

private theorem callFrameWith_bind {α : Type} (check : List Value → Sem Unit)
    (callee : Sem (List Value)) (next : List Value → Sem α) :
    (callFrameWith check callee >>= next) = (do
      let caller ← Sem.getState
      Sem.setState (callerWorld caller)
      let values ← callee
      check values
      let state ← Sem.getState
      Sem.setState (restoreFrame state (saveFrame caller none) [])
      next values) := by
  simp only [callFrameWith, finishCalleeWith, bind_assoc, pure_bind]

/-- The actual element body with its loop continuation kept opaque. -/
def seqMapApplyCallWith {α : Type} (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (inst : Inst) (header : FunctionHeader) (id : FuncId)
    (elemTy : Ty) (elem : Value) (next : Value → Sem α) : Sem α := do
  Sem.fromMemoryExcept (ctx.checkSeqMapElement inst elemTy elem)
  -- Empty maps perform none of these per-element operations.
  let layout ← Sem.fromMemoryExcept (ctx.memoryLayout elemTy)
  let before ← Sem.getState
  Sem.checkTargetAllocation ctx.byteModel before.memory layout.size layout.alignment 0
  let (cellAddr, memory) := before.memory.alloc layout.size layout.alignment 0 .rustStack
  let allocId : AllocId := ⟨before.memory.nextAllocId⟩
  Sem.setState { before with memory := memory, permissions := before.permissions.set allocId .owned }
  let pointer := Value.ptr cellAddr (some allocId)
  ctx.storeMemoryValue elemTy pointer elem
  if let some error := ctx.functionErrors id then throw error
  let callee ← ctx.lookupDirectCallee id
    "SeqMap: element function is declared without a body" "SeqMap: undefined element function"
  if !(header.matches callee) then
    Sem.throwTypeError "SeqMap: original header does not match executable function metadata"
  requireUntypedAbi callee.body.abi
  let callerState ← Sem.getState
  let frame := saveFrame callerState none
  Sem.setState { callerState with locals := ValueMap.empty, nextValueId := 0 }
  let retVals ← recurse (ctx.forFunction callee) depth
    callee.cfg callee.entryBlock [pointer] strat
  match checkReturnArity retVals callee.body.returnTys with
  | .ok () => pure ()
  | .error msg => Sem.throwTypeError ("SeqMap: " ++ msg)
  Sem.rejectPoisonValues retVals "SeqMap returns"
  let calleeState ← Sem.getState
  Sem.setState (restoreFrame calleeState frame [])
  let newElem ← ctx.loadMemoryValue elemTy pointer
  next newElem

theorem seqMapApply_framed {α : Type} (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (inst : Inst) (header : FunctionHeader) (id : FuncId)
    (elemTy : Ty) (elem : Value) (next : Value → Sem α) :
    (seqMapApply ctx inst header id elemTy (fun callee pointer =>
      callFrameWith (seqMapReturns callee.body.returnTys)
        (recurse (ctx.forFunction callee) depth callee.cfg callee.entryBlock [pointer] strat)) elem >>= next) =
      seqMapApplyCallWith recurse ctx depth strat inst header id elemTy elem next := by
  trustIrCompilerProof {
    simp only [seqMapApply, seqMapElement, seqMapInvoke, seqMapApplyCallWith,
      bind_assoc, callFrameWith_bind, seqMapReturns, callerWorld, pure_bind]
    with_reducible (repeat' (first
      | rfl
      | (refine bind_same _ ?_; intro value; dsimp only)
      | simp_all only [pure_bind, bind_assoc, Sem.throwTypeError, Sem.throwUB,
          Sem.throwUnsupported, throw_bind_sem, callFrameWith, finishCalleeWith, seqMapReturns, callerWorld]
      | (split <;> try dsimp only)))
  } {
    simp only [seqMapApply, seqMapElement, seqMapInvoke, seqMapApplyCallWith,
      bind_assoc, callFrameWith_bind, seqMapReturns, callerWorld, pure_bind]
    with_reducible (repeat' (first
      | rfl
      | (refine bind_same _ ?_; intro value; dsimp only)
      | simp_all only [pure_bind, bind_assoc, Sem.throwTypeError, Sem.throwUB,
          Sem.throwUnsupported, throw_bind_sem, callFrameWith, finishCalleeWith, seqMapReturns, callerWorld]
      | (split <;> try dsimp only)))
    all_goals rfl
  }

theorem seqMapStep_calls (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (inst : Inst) (dests : List ValueId)
    (id : FuncId) (elems : List Value) :
    seqMapStep recurse ctx (depth + 1) strat inst dests id elems = (do
      let header ← ctx.lookupFunctionHeader id
      requireUntypedAbi header.signature.abi
      if header.signature.isVararg then
        Sem.throwTypeError "SeqMap: element function must not be variadic"
      let elemTy ← match header.signature.params, header.signature.returns with
        | [Ty.RefMut element], [] => pure element
        | _, _ => Sem.throwTypeError "SeqMap: element function must have signature fn(&mut elem)"
      let mapped ← forIn elems [] (fun elem mapped =>
        seqMapApplyCallWith recurse ctx depth strat inst header id elemTy elem
          (fun newElem => pure (.yield (mapped ++ [newElem]))))
      ctx.bindCallResults inst dests [Value.sequence mapped]
      pure (.yield ())) := by rfl

theorem seqMapStep_framed (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (inst : Inst) (dests : List ValueId)
    (id : FuncId) (elems : List Value) :
    seqMapStep recurse ctx (depth + 1) strat inst dests id elems =
      seqMapRun ctx inst dests id elems (fun callee pointer =>
        callFrameWith (seqMapReturns callee.body.returnTys)
          (recurse (ctx.forFunction callee) depth callee.cfg callee.entryBlock [pointer] strat)) := by
  rw [seqMapStep_calls]
  simp only [seqMapRun, seqMapApply_framed]

private theorem lookupFunctionHeader_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (id : FuncId) :
    (scopedContext base source sourceTypes).lookupFunctionHeader id =
      (scopedContext base target targetTypes).lookupFunctionHeader id := by
  have related := headers id
  cases sourceFound : source id with
  | none =>
    cases targetFound : target id with
    | none => simp only [EvalContext.lookupFunctionHeader, scopedContext, sourceFound, targetFound]
    | some function => rw [sourceFound, targetFound] at related; cases related
  | some sourceFunction =>
    cases targetFound : target id with
    | none => rw [sourceFound, targetFound] at related; cases related
    | some targetFunction =>
      rw [sourceFound, targetFound] at related
      cases related with
      | present _ _ body convention =>
        simp only [EvalContext.lookupFunctionHeader, scopedContext, sourceFound, targetFound,
          EvalFunction.header, body, convention]

private theorem checkSeqMapElement_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (sourceTypes targetTypes : Option LocalTypeTable)
    (inst : Inst) (dests : List ValueId) (elemTy : Ty) (elem : Value)
    (types : TypesAgreeOn (dests ++ operandIds inst) sourceTypes targetTypes) :
    (scopedContext base source sourceTypes).checkSeqMapElement inst elemTy elem =
      (scopedContext base target targetTypes).checkSeqMapElement inst elemTy elem := by
  cases service : base.memoryService with
  | none => simp only [EvalContext.checkSeqMapElement, scopedContext, service]
  | some service =>
    simp only [EvalContext.checkSeqMapElement, scopedContext, service]
    cases inst <;> try rfl
    case SeqMap ty sequence fwd =>
      cases types with
      | absent => rfl
      | present sourceTable targetTable same =>
        have read := same sequence (trustIrListMemAppendRight _ ((trustIrListMemConsSelf _ _)))
        simp only [EvalContext.checkSeqMapElement, scopedContext, EvalContext.types, service, pure_bind,
          Except.bind, Except.pure, Bind.bind, Pure.pure, read]

private theorem seqMapInvoke_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (header : FunctionHeader) (id : FuncId)
    (sourceInvoke targetInvoke : EvalFunction → Value → Sem (List Value))
    (invokeSame : ∀ sourceFunction targetFunction, source id = some sourceFunction →
      target id = some targetFunction → ∀ pointer,
      sourceInvoke sourceFunction pointer = targetInvoke targetFunction pointer) (pointer : Value) :
    seqMapInvoke (scopedContext base source sourceTypes) header id sourceInvoke pointer =
      seqMapInvoke (scopedContext base target targetTypes) header id targetInvoke pointer := by
  have related := headers id
  cases sourceFound : source id with
  | none =>
    cases targetFound : target id with
    | none =>
      cases errorFound : base.functionErrors id <;> cases declaration : base.declared id <;>
        simp only [seqMapInvoke, EvalContext.lookupDirectCallee, scopedContext, sourceFound, targetFound,
          errorFound, declaration, Bool.false_eq_true, if_false, if_true,
          Sem.throwTypeError, Sem.throwUnsupported, throw_bind_sem, pure_bind]
    | some function => rw [sourceFound, targetFound] at related; cases related
  | some sourceFunction =>
    cases targetFound : target id with
    | none => rw [sourceFound, targetFound] at related; cases related
    | some targetFunction =>
      rw [sourceFound, targetFound] at related
      cases related with
      | present _ _ body convention =>
        have invoked := invokeSame sourceFunction targetFunction sourceFound targetFound pointer
        simp only [seqMapInvoke, EvalContext.lookupDirectCallee, scopedContext, sourceFound, targetFound,
          pure_bind, FunctionHeader.matches, body, convention, invoked]

theorem seqMapRun_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (inst : Inst) (dests : List ValueId)
    (id : FuncId) (elems : List Value)
    (sourceInvoke targetInvoke : EvalFunction → Value → Sem (List Value))
    (invokeSame : ∀ sourceFunction targetFunction, source id = some sourceFunction →
      target id = some targetFunction → ∀ pointer,
      sourceInvoke sourceFunction pointer = targetInvoke targetFunction pointer)
    (types : TypesAgreeOn (dests ++ operandIds inst) sourceTypes targetTypes) :
    seqMapRun (scopedContext base source sourceTypes) inst dests id elems sourceInvoke =
      seqMapRun (scopedContext base target targetTypes) inst dests id elems targetInvoke := by
  have applySame (header : FunctionHeader) (elemTy : Ty) (elem : Value) :
      seqMapApply (scopedContext base source sourceTypes) inst header id elemTy sourceInvoke elem =
        seqMapApply (scopedContext base target targetTypes) inst header id elemTy targetInvoke elem := by
    simp only [seqMapApply, checkSeqMapElement_congr base source target sourceTypes targetTypes
      inst dests elemTy elem types, seqMapElement_scoped]
    have invoked : seqMapInvoke (scopedContext base source sourceTypes) header id sourceInvoke =
        seqMapInvoke (scopedContext base target targetTypes) header id targetInvoke :=
      funext (seqMapInvoke_congr base source target headers sourceTypes targetTypes header id
        sourceInvoke targetInvoke invokeSame)
    rw [invoked]
  simp only [seqMapRun, lookupFunctionHeader_congr base source target headers sourceTypes targetTypes id,
    applySame, bindCallResults_congr base source target headers sourceTypes targetTypes inst dests _ types]

theorem seqMapStep_congr (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (depth : Nat)
    (strat : PanicStrategy) (inst : Inst) (dests : List ValueId)
    (id : FuncId) (elems : List Value)
    (types : TypesAgreeOn (dests ++ operandIds inst) sourceTypes targetTypes) :
    seqMapStep sourceRecurse (scopedContext base source sourceTypes) depth strat inst dests id elems =
      seqMapStep targetRecurse (scopedContext base target targetTypes) depth strat inst dests id elems := by
  cases depth with
  | zero => rfl
  | succ depth =>
    rw [seqMapStep_framed, seqMapStep_framed]
    apply seqMapRun_congr base source target headers sourceTypes targetTypes inst dests id elems
      _ _ ?_ types
    intro sourceFunction targetFunction sourceFound targetFound pointer
    have related := headers id
    rw [sourceFound, targetFound] at related
    cases related with
    | present _ _ body convention =>
      simp only [scopedContext_forFunction, ← body]
      exact callFrameWith_eq_of_effectRelation _
        (seqMapReturns_equivariant _) _ _
        (effects id sourceFunction targetFunction sourceFound targetFound depth [pointer] strat)

/-- Production fallback handling after the leaf has produced its result. -/
def producedStep (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (inst : Inst) (dests : List ValueId)
    (result : InstrResult) : Sem (ForInStep Unit) :=
  match result with
  | .value _ | .values _ => do
    ctx.bindInstructionResults inst result dests
    pure (.yield ())
  | .terminator (.SeqMapReq id elems) => seqMapStep recurse ctx depth strat inst dests id elems
  | .terminator _ => do
    Sem.throwTypeError "body instruction produced a terminator"
    pure (.yield ())

theorem producedStep_congr (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (depth : Nat)
    (strat : PanicStrategy) (inst : Inst) (dests : List ValueId) (result : InstrResult)
    (types : TypesAgreeOn (dests ++ operandIds inst) sourceTypes targetTypes) :
    producedStep sourceRecurse (scopedContext base source sourceTypes) depth strat inst dests result =
      producedStep targetRecurse (scopedContext base target targetTypes) depth strat inst dests result := by
  cases result with
  | value value =>
    simp only [producedStep,
      bindInstructionResults_congr base source target headers sourceTypes targetTypes inst dests _ types]
  | values values =>
    simp only [producedStep,
      bindInstructionResults_congr base source target headers sourceTypes targetTypes inst dests _ types]
  | terminator result =>
    cases result <;> first
      | exact seqMapStep_congr sourceRecurse targetRecurse base source target headers effects
          sourceTypes targetTypes depth strat inst dests _ _ types
      | rfl

end TrustIr.GenericCoro.Prefix

#trustIrAxiomsExact TrustIr.GenericCoro.Prefix.seqMapReturns == []
