-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixIndirect
import TrustIr.Proofs.GenericCoroPrefixSeqMap
import TrustIr.Proofs.SSAFreshUnwindBody

namespace TrustIr.GenericCoro.Prefix

/-- The exact production post-leaf handler before outlining its SeqMap loop. -/
def producedStepRaw (recurse : Recurse) (ctx : EvalContext) (callDepth : Nat)
    (strat : PanicStrategy) (inst : Inst) (resultDests : List ValueId)
    (instResult : InstrResult) : Sem (ForInStep Unit) := do
  match instResult with
  | .value _ => ctx.bindInstructionResults inst instResult resultDests
  | .values _ => ctx.bindInstructionResults inst instResult resultDests
  | .terminator (.SeqMapReq fwdId elems) => do
    -- SeqMap element application (give-back loop instruction):
    -- apply the element function `fwd : fn(&mut elem)` to every
    -- element via the standard call machinery. ONE call-depth level
    -- bounds the WHOLE map — the per-element calls are sequential,
    -- so depth bounds nesting, not sequence length (do not burn
    -- depth per element). Each element round-trips through a fresh
    -- per-element memory cell: alloc → write element → call
    -- fwd(&mut cell) → read the mutated element back through its
    -- source-derived typed image. The original header is checked
    -- even for an empty map; layout, cells and executable bodies
    -- are needed only when an element is actually applied.
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
  | .terminator _ =>
    Sem.throwTypeError "body instruction produced a terminator"

  pure (.yield ())

theorem producedStepRaw_eq (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (inst : Inst) (dests : List ValueId) (result : InstrResult) :
    producedStepRaw recurse ctx depth strat inst dests result =
      producedStep recurse ctx depth strat inst dests result := by
  cases result with
  | value value => rfl
  | values values => rfl
  | terminator result => cases result <;> rfl

trustIrDenseMatch
def bodyDispatch
    (onCall : FuncId → List ValueId → Sem (ForInStep Unit))
    (onIndirect : ValueId → FuncTyId → List ValueId → CallingConv → Sem (ForInStep Unit))
    (onAssert : Sem (ForInStep Unit)) (onPad : Bool → List Nat → Sem (ForInStep Unit))
    (onOther : Sem (ForInStep Unit)) (inst : Inst) : Sem (ForInStep Unit) :=
  match inst with
  | .Call id args => onCall id args
  | .CallIndirect id sig args conv => onIndirect id sig args conv
  | .Assert _ _ _ => onAssert
  | .LandingPad cleanup clauses => onPad cleanup clauses
  | _ => onOther

private theorem bodyCases_congr (inst : Inst)
    (sourceCall targetCall : FuncId → List ValueId → Sem (ForInStep Unit))
    (sourceIndirect targetIndirect : ValueId → FuncTyId → List ValueId → CallingConv → Sem (ForInStep Unit))
    (sourceAssert targetAssert : Sem (ForInStep Unit))
    (sourcePad targetPad : Bool → List Nat → Sem (ForInStep Unit))
    (sourceOther targetOther : Sem (ForInStep Unit))
    (calls : ∀ id args, inst = .Call id args → sourceCall id args = targetCall id args)
    (indirect : ∀ id sig args conv, inst = .CallIndirect id sig args conv →
      sourceIndirect id sig args conv = targetIndirect id sig args conv)
    (assertion : sourceAssert = targetAssert)
    (pad : ∀ cleanup clauses, inst = .LandingPad cleanup clauses →
      sourcePad cleanup clauses = targetPad cleanup clauses)
    (other : sourceOther = targetOther) :
    bodyDispatch sourceCall sourceIndirect sourceAssert sourcePad sourceOther inst =
      bodyDispatch targetCall targetIndirect targetAssert targetPad targetOther inst := by
  cases inst
  case Call id args => exact calls id args rfl
  case CallIndirect id sig args conv => exact indirect id sig args conv rfl
  case Assert condition kind site => exact assertion
  case LandingPad cleanup clauses => exact pad cleanup clauses rfl
  all_goals exact other

private theorem bodyDispatch_as_source
    (onCall : FuncId → List ValueId → Sem (ForInStep Unit))
    (onIndirect : ValueId → FuncTyId → List ValueId → CallingConv → Sem (ForInStep Unit))
    (onAssert : Sem (ForInStep Unit)) (onPad : Bool → List Nat → Sem (ForInStep Unit))
    (onOther : Sem (ForInStep Unit)) (inst : Inst) :
    bodyDispatch onCall onIndirect onAssert onPad onOther inst =
      ((fun instruction => match instruction with
        | .Call id args => onCall id args
        | .CallIndirect id sig args conv => onIndirect id sig args conv
        | .Assert _ _ _ => onAssert
        | .LandingPad cleanup clauses => onPad cleanup clauses
        | _ => onOther) inst) := by
  cases inst <;> rfl

private theorem bodySourceCases_congr (inst : Inst)
    (sourceCall targetCall : FuncId → List ValueId → Sem (ForInStep Unit))
    (sourceIndirect targetIndirect : ValueId → FuncTyId → List ValueId → CallingConv → Sem (ForInStep Unit))
    (sourceAssert targetAssert : Sem (ForInStep Unit))
    (sourcePad targetPad : Bool → List Nat → Sem (ForInStep Unit))
    (sourceOther targetOther : Sem (ForInStep Unit))
    (calls : ∀ id args, inst = .Call id args → sourceCall id args = targetCall id args)
    (indirect : ∀ id sig args conv, inst = .CallIndirect id sig args conv →
      sourceIndirect id sig args conv = targetIndirect id sig args conv)
    (assertion : sourceAssert = targetAssert)
    (pad : ∀ cleanup clauses, inst = .LandingPad cleanup clauses →
      sourcePad cleanup clauses = targetPad cleanup clauses)
    (other : sourceOther = targetOther) :
    ((fun instruction => match instruction with
      | .Call id args => sourceCall id args
      | .CallIndirect id sig args conv => sourceIndirect id sig args conv
      | .Assert _ _ _ => sourceAssert
      | .LandingPad cleanup clauses => sourcePad cleanup clauses
      | _ => sourceOther) inst) =
    ((fun instruction => match instruction with
      | .Call id args => targetCall id args
      | .CallIndirect id sig args conv => targetIndirect id sig args conv
      | .Assert _ _ _ => targetAssert
      | .LandingPad cleanup clauses => targetPad cleanup clauses
      | _ => targetOther) inst) := by
  cases inst
  case Call id args => exact calls id args rfl
  case CallIndirect id sig args conv => exact indirect id sig args conv rfl
  case Assert condition kind site => exact assertion
  case LandingPad cleanup clauses => exact pad cleanup clauses rfl
  all_goals exact other

/-- Outlining the five production body handlers adds no evaluation rule. -/
theorem evalBodyStep_dispatch (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strat : PanicStrategy) (inst : Inst) (dests : List ValueId) :
    evalBodyStep recurse ctx depth strat (inst, dests) =
      bodyDispatch
        (fun id args => bodyCall recurse ctx depth strat id args dests)
        (fun id sig args conv => bodyIndirect recurse ctx depth strat id sig args conv dests)
        (do let result ← raiseIfUnwind strat (stepInstWithContext ctx inst) ctx.byteModel
            ctx.bindInstructionResults inst result dests
            pure (.yield ()))
        (fun cleanup clauses => do semLandingPadWith strat ctx (.LandingPad cleanup clauses) dests
                                   pure (.yield ()))
        (stepInstWithContext ctx inst >>= producedStep recurse ctx depth strat inst dests)
        inst := by
  trustIrCompilerProof {
    unfold evalBodyStep
    dsimp only
    apply bodyCases_congr inst
    · intro id args equal
      subst inst
      exact evalBodyStep_call recurse ctx depth strat id args dests
    · intro id sig args conv equal
      subst inst
      exact evalBodyStep_indirect recurse ctx depth strat id sig args conv dests
    · rfl
    · intro cleanup clauses equal
      rfl
    · change (stepInstWithContext ctx inst >>= producedStepRaw recurse ctx depth strat inst dests) = _
      apply bind_same
      intro result
      exact producedStepRaw_eq recurse ctx depth strat inst dests result
  } {
    rw [bodyDispatch_as_source]
    unfold evalBodyStep
    dsimp only
    apply bodySourceCases_congr inst
    · intro id args equal
      subst inst
      exact evalBodyStep_call recurse ctx depth strat id args dests
    · intro id sig args conv equal
      subst inst
      exact evalBodyStep_indirect recurse ctx depth strat id sig args conv dests
    · rfl
    · intro cleanup clauses equal
      rfl
    · change (stepInstWithContext ctx inst >>= producedStepRaw recurse ctx depth strat inst dests) = _
      apply bind_same
      intro result
      exact producedStepRaw_eq recurse ctx depth strat inst dests result
  }

theorem semLandingPadWith_congr (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (strat : PanicStrategy)
    (pad : Inst) (dests : List ValueId)
    (types : TypesAgreeOn (dests ++ operandIds pad) sourceTypes targetTypes) :
    semLandingPadWith strat (scopedContext base source sourceTypes) pad dests =
      semLandingPadWith strat (scopedContext base target targetTypes) pad dests := by
  have leaf := stepInstWithContext_congr base source target headers sourceTypes targetTypes pad
    (types.mono (fun id member => trustIrListMemAppendRight _ member))
  cases strat <;>
    simp only [semLandingPadWith, leaf,
      bindInstructionResults_congr base source target headers sourceTypes targetTypes pad dests _ types,
      bindCallResults_congr base source target headers sourceTypes targetTypes pad dests _ types]

/-- The whole body node, including recursive direct/indirect calls, SeqMap,
    assertions and landing pads. Only its actual source SSA observations are
    related; recursive callees use their real, potentially different tables. -/
theorem evalBodyStep_congr (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (depth : Nat)
    (strat : PanicStrategy) (inst : Inst) (dests : List ValueId)
    (types : TypesAgreeOn (dests ++ operandIds inst) sourceTypes targetTypes) :
    evalBodyStep sourceRecurse (scopedContext base source sourceTypes) depth strat (inst, dests) =
      evalBodyStep targetRecurse (scopedContext base target targetTypes) depth strat (inst, dests) := by
  trustIrCompilerProof {
    have leaf := stepInstWithContext_congr base source target headers sourceTypes targetTypes inst
      (types.mono (fun id member => trustIrListMemAppendRight _ member))
    unfold evalBodyStep
    dsimp only
    apply bodyCases_congr inst
    · intro id args equal
      subst inst
      change evalBodyStep sourceRecurse (scopedContext base source sourceTypes) depth strat (.Call id args, dests) =
        evalBodyStep targetRecurse (scopedContext base target targetTypes) depth strat (.Call id args, dests)
      rw [evalBodyStep_call, evalBodyStep_call]
      exact bodyCall_congr sourceRecurse targetRecurse base source target headers effects
        sourceTypes targetTypes depth strat id args dests types
    · intro id sig args conv equal
      subst inst
      change evalBodyStep sourceRecurse (scopedContext base source sourceTypes) depth strat
          (.CallIndirect id sig args conv, dests) =
        evalBodyStep targetRecurse (scopedContext base target targetTypes) depth strat
          (.CallIndirect id sig args conv, dests)
      rw [evalBodyStep_indirect, evalBodyStep_indirect]
      exact bodyIndirect_congr sourceRecurse targetRecurse base source target headers effects
        sourceTypes targetTypes depth strat id sig args conv dests types
    · simp only [leaf,
        bindInstructionResults_congr base source target headers sourceTypes targetTypes inst dests _ types]
      rfl
    · intro cleanup clauses equal
      subst inst
      rw [semLandingPadWith_congr base source target headers sourceTypes targetTypes strat
        (.LandingPad cleanup clauses) dests types]
    · change
        (stepInstWithContext (scopedContext base source sourceTypes) inst >>=
          producedStepRaw sourceRecurse (scopedContext base source sourceTypes) depth strat inst dests) =
        (stepInstWithContext (scopedContext base target targetTypes) inst >>=
          producedStepRaw targetRecurse (scopedContext base target targetTypes) depth strat inst dests)
      rw [leaf]
      apply bind_same
      intro result
      rw [producedStepRaw_eq, producedStepRaw_eq]
      exact producedStep_congr sourceRecurse targetRecurse base source target headers effects
        sourceTypes targetTypes depth strat inst dests result types
  } {
    have leaf := stepInstWithContext_congr base source target headers sourceTypes targetTypes inst
      (types.mono (fun id member => trustIrListMemAppendRight _ member))
    unfold evalBodyStep
    dsimp only
    apply bodySourceCases_congr inst
    · intro id args equal
      subst inst
      change evalBodyStep sourceRecurse (scopedContext base source sourceTypes) depth strat (.Call id args, dests) =
        evalBodyStep targetRecurse (scopedContext base target targetTypes) depth strat (.Call id args, dests)
      rw [evalBodyStep_call, evalBodyStep_call]
      exact bodyCall_congr sourceRecurse targetRecurse base source target headers effects
        sourceTypes targetTypes depth strat id args dests types
    · intro id sig args conv equal
      subst inst
      change evalBodyStep sourceRecurse (scopedContext base source sourceTypes) depth strat
          (.CallIndirect id sig args conv, dests) =
        evalBodyStep targetRecurse (scopedContext base target targetTypes) depth strat
          (.CallIndirect id sig args conv, dests)
      rw [evalBodyStep_indirect, evalBodyStep_indirect]
      exact bodyIndirect_congr sourceRecurse targetRecurse base source target headers effects
        sourceTypes targetTypes depth strat id sig args conv dests types
    · simp only [leaf,
        bindInstructionResults_congr base source target headers sourceTypes targetTypes inst dests _ types]
      rfl
    · intro cleanup clauses equal
      subst inst
      rw [semLandingPadWith_congr base source target headers sourceTypes targetTypes strat
        (.LandingPad cleanup clauses) dests types]
    · change
        (stepInstWithContext (scopedContext base source sourceTypes) inst >>=
          producedStepRaw sourceRecurse (scopedContext base source sourceTypes) depth strat inst dests) =
        (stepInstWithContext (scopedContext base target targetTypes) inst >>=
          producedStepRaw targetRecurse (scopedContext base target targetTypes) depth strat inst dests)
      rw [leaf]
      apply bind_same
      intro result
      rw [producedStepRaw_eq, producedStepRaw_eq]
      exact producedStep_congr sourceRecurse targetRecurse base source target headers effects
        sourceTypes targetTypes depth strat inst dests result types
  }

#trustIrAxioms bodyDispatch_as_source <= [propext]
#trustIrAxioms bodySourceCases_congr <= [propext]

end TrustIr.GenericCoro.Prefix

#trustIrAxiomsExact TrustIr.GenericCoro.Prefix.bodyDispatch == []
