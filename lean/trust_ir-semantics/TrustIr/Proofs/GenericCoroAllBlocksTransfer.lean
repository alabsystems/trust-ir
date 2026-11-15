-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixTransfer
import TrustIr.Proofs.GenericCoroAllBlocksInvoke
import TrustIr.Proofs.GenericCoroAllBlocksEffect
import TrustIr.Proofs.GenericCoroPadViews

namespace TrustIr.GenericCoroAllBlocksTransfer
open GenericCoro GenericCoro.Prefix GenericCoro.AllBlocksEffect
open SSAFreshFrames SSAFreshStep SSAFreshInstructions SSAFreshDispatch

/-- The actual predecessor callbacks continue different caller CFGs with
    their own active declarations. Every error and non-SSA world field is
    retained; the only input invariant is the derived caller freshness. -/
def PairedCallbacks (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction)
    (sourceTypes targetTypes : Option LocalTypeTable) (sourceCFG targetCFG : CFG) : Prop :=
  ∀ depth pc args strategy state, FreshState state → EffectRelation
    (Sem.run (sourceRecurse (scopedContext base source sourceTypes) depth sourceCFG pc args strategy) state)
    (Sem.run (targetRecurse (scopedContext base target targetTypes) depth targetCFG pc args strategy) state)

theorem effect_refl (outcome : Except SemError (List Value × MachineState)) :
    EffectRelation outcome outcome := by
  cases outcome with
  | error error => exact .error error
  | ok result => exact .returned result.1 result.2 result.2 rfl

/-- Result publication has exactly the original terminator's destination
    and operand declaration domain. Edge-argument lookup itself is untyped. -/
theorem invokeNormal_effect (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (sourceCFG targetCFG : CFG)
    (paired : PairedCallbacks sourceRecurse targetRecurse base source target
      sourceTypes targetTypes sourceCFG targetCFG)
    (block : BasicBlock)
    (types : TypesAgreeOn (block.terminatorResultDests ++ operandIds block.terminator) sourceTypes targetTypes)
    (depth : Nat) (strategy : PanicStrategy) (next : BlockId) (argIds : List ValueId)
    (values : List Value) (state : MachineState) (fresh : FreshState state) :
    EffectRelation
      (Sem.run (do
        (scopedContext base source sourceTypes).bindCallResults block.terminator block.terminatorResultDests values
        let args ← argIds.mapM Sem.lookupValue
        sourceRecurse (scopedContext base source sourceTypes) depth sourceCFG next args strategy) state)
      (Sem.run (do
        (scopedContext base target targetTypes).bindCallResults block.terminator block.terminatorResultDests values
        let args ← argIds.mapM Sem.lookupValue
        targetRecurse (scopedContext base target targetTypes) depth targetCFG next args strategy) state) := by
  rw [bindCallResults_congr base source target headers sourceTypes targetTypes
    block.terminator block.terminatorResultDests values types]
  apply bind_effect _ _ _ (bindCallResults_fresh _ _ _ _) _ state fresh
  intro _unit after freshAfter
  apply bind_effect _ _ _ (mapM_fresh Sem.lookupValue argIds lookup_fresh) _ after freshAfter
  intro args final freshFinal
  exact paired depth next args strategy final freshFinal

theorem invokeUnwind_effect (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction)
    (sourceTypes targetTypes : Option LocalTypeTable) (sourceCFG targetCFG : CFG)
    (pads : PadViews.PadViewsAgree sourceCFG targetCFG)
    (paired : PairedCallbacks sourceRecurse targetRecurse base source target
      sourceTypes targetTypes sourceCFG targetCFG)
    (depth : Nat) (strategy : PanicStrategy) (next : BlockId) (exception : Addr)
    (state : MachineState) (fresh : FreshState state) :
    EffectRelation
      (Sem.run (do
        semEnterPad sourceCFG exception next
        sourceRecurse (scopedContext base source sourceTypes) depth sourceCFG next [] strategy) state)
      (Sem.run (do
        semEnterPad targetCFG exception next
        targetRecurse (scopedContext base target targetTypes) depth targetCFG next [] strategy) state) := by
  rw [PadViews.semEnterPad_congr sourceCFG targetCFG exception next (pads next)]
  apply bind_effect _ _ _ (PadViews.semEnterPad_fresh targetCFG exception next) _ state fresh
  intro _unit after freshAfter
  exact paired depth next [] strategy after freshAfter

/-- First change the separately framed callees using their complete
    relation, then change the caller continuations only at restored fresh
    states. No callee-freshness or successful-return premise is introduced. -/
theorem invokeFrame_effect (strategy : PanicStrategy) (check : List Value → Sem Unit)
    (equivariant : ∀ values, HeldMemoryFrames.Equivariant (check values))
    (sourceCallee targetCallee : Sem (List Value))
    (callees : ∀ world, EffectRelation
      (Sem.run sourceCallee (callerWorld world)) (Sem.run targetCallee (callerWorld world)))
    (sourceNormal targetNormal : List Value → Sem (List Value))
    (sourceUnwind targetUnwind : Addr → Sem (List Value))
    (normal : ∀ values state, FreshState state → EffectRelation
      (Sem.run (sourceNormal values) state) (Sem.run (targetNormal values) state))
    (unwind : ∀ exception state, FreshState state → EffectRelation
      (Sem.run (sourceUnwind exception) state) (Sem.run (targetUnwind exception) state))
    (state : MachineState) (fresh : FreshState state) :
    EffectRelation
      (Sem.run (invokeFrameWith strategy check sourceCallee sourceNormal sourceUnwind) state)
      (Sem.run (invokeFrameWith strategy check targetCallee targetNormal targetUnwind) state) := by
  rw [invokeFrameWith_eq_of_effectRelation strategy check equivariant sourceCallee targetCallee
    sourceNormal sourceUnwind callees]
  exact GenericCoroAllBlocksInvoke.invokeFrameWith_effect_on_fresh strategy check targetCallee
    sourceNormal targetNormal sourceUnwind targetUnwind normal unwind state fresh

private theorem requireAbi_fresh (abi : Option SignatureAbi) : KeepsFresh (requireUntypedAbi abi) := by
  unfold requireUntypedAbi
  split
  · exact throwUnsupported_fresh _ _
  · exact pure_fresh _

private theorem scoped_ptrs (base : EvalContext) (functions : FuncId → Option EvalFunction)
    (types : Option LocalTypeTable) : (scopedContext base functions types).funcPtrs = base.funcPtrs := rfl

private theorem scoped_signatures (base : EvalContext) (functions : FuncId → Option EvalFunction)
    (types : Option LocalTypeTable) : (scopedContext base functions types).funcTys = base.funcTys := rfl

theorem invoke_effect (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (sourceCFG targetCFG : CFG)
    (pads : PadViews.PadViewsAgree sourceCFG targetCFG)
    (paired : PairedCallbacks sourceRecurse targetRecurse base source target
      sourceTypes targetTypes sourceCFG targetCFG)
    (block : BasicBlock)
    (types : TypesAgreeOn (block.terminatorResultDests ++ operandIds block.terminator) sourceTypes targetTypes)
    (depth : Nat) (strategy : PanicStrategy) (id : FuncId) (args : List Value)
    (normal : BlockId) (normalArgs : List ValueId) (unwind : BlockId)
    (state : MachineState) (fresh : FreshState state) :
    EffectRelation
      (Sem.run (evalTransfer sourceRecurse (scopedContext base source sourceTypes) depth
        sourceCFG block strategy (.InvokeReq id args normal normalArgs unwind)) state)
      (Sem.run (evalTransfer targetRecurse (scopedContext base target targetTypes) depth
        targetCFG block strategy (.InvokeReq id args normal normalArgs unwind)) state) := by
  cases depth with
  | zero => exact .error .outOfFuel
  | succ depth =>
    rw [evalTransfer_invoke_succ, evalTransfer_invoke_succ]
    have related := headers id
    cases sourceFound : source id with
    | none =>
      cases targetFound : target id with
      | none =>
        simp only [EvalContext.lookupDirectCallee,
          show (scopedContext base source sourceTypes).functions id = none from sourceFound,
          show (scopedContext base target targetTypes).functions id = none from targetFound,
          show (scopedContext base source sourceTypes).declared = base.declared from rfl,
          show (scopedContext base target targetTypes).declared = base.declared from rfl]
        split <;> simp only [Sem.throwUnsupported, Sem.throwTypeError, throw_bind_sem]
        all_goals exact .error _
      | some function => rw [sourceFound, targetFound] at related; cases related
    | some sourceFunction =>
      cases targetFound : target id with
      | none => rw [sourceFound, targetFound] at related; cases related
      | some targetFunction =>
        rw [sourceFound, targetFound] at related
        cases related with
        | present _ _ body convention =>
          simp only [EvalContext.lookupDirectCallee,
            show (scopedContext base source sourceTypes).functions id = some sourceFunction from sourceFound,
            show (scopedContext base target targetTypes).functions id = some targetFunction from targetFound,
            pure_bind, scopedContext_forFunction, ← body, checkReturns_scoped_function]
          apply bind_effect _ _ _ (requireAbi_fresh _) _ state fresh
          intro _unit afterABI freshABI
          cases arity : checkCallArity args sourceFunction.body.paramTys with
          | error message =>
            simp only [arity, Sem.throwTypeError, throw_bind_sem]
            exact .error _
          | ok unit =>
            cases unit
            simp only [arity, pure_bind]
            apply bind_effect _ _ _ (rejectPoisonValues_fresh args "Call arguments") _ afterABI freshABI
            intro _unit afterPoison freshPoison
            apply invokeFrame_effect strategy _
              (checkReturns_equivariant base sourceFunction.body.returnTys true false "Invoke: ")
              _ _ (effects id sourceFunction targetFunction sourceFound targetFound depth args strategy)
              _ _ _ _ _ _ afterPoison freshPoison
            · intro values after freshAfter
              exact invokeNormal_effect sourceRecurse targetRecurse base source target headers
                sourceTypes targetTypes sourceCFG targetCFG paired block types (depth + 1)
                strategy normal normalArgs values after freshAfter
            · intro exception after freshAfter
              exact invokeUnwind_effect sourceRecurse targetRecurse base source target
                sourceTypes targetTypes sourceCFG targetCFG pads paired (depth + 1)
                strategy unwind exception after freshAfter

/-- The raw indirect-invoke prelude retains its original lookup order and
    deliberately performs no ABI prelude checks. -/
theorem invokeIndirect_effect (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (sourceCFG targetCFG : CFG)
    (pads : PadViews.PadViewsAgree sourceCFG targetCFG)
    (paired : PairedCallbacks sourceRecurse targetRecurse base source target
      sourceTypes targetTypes sourceCFG targetCFG)
    (block : BasicBlock)
    (types : TypesAgreeOn (block.terminatorResultDests ++ operandIds block.terminator) sourceTypes targetTypes)
    (depth : Nat) (strategy : PanicStrategy) (address : Nat) (signature : FuncTyId) (args : List Value)
    (normal : BlockId) (normalArgs : List ValueId) (unwind : BlockId)
    (state : MachineState) (fresh : FreshState state) :
    EffectRelation
      (Sem.run (evalTransfer sourceRecurse (scopedContext base source sourceTypes) depth sourceCFG block strategy
        (.InvokeIndirectReq address signature args normal normalArgs unwind)) state)
      (Sem.run (evalTransfer targetRecurse (scopedContext base target targetTypes) depth targetCFG block strategy
        (.InvokeIndirectReq address signature args normal normalArgs unwind)) state) := by
  cases depth with
  | zero => exact .error .outOfFuel
  | succ depth =>
    rw [evalTransfer_invokeIndirect_succ, evalTransfer_invokeIndirect_succ]
    simp only [scoped_ptrs, scoped_signatures]
    cases pointer : base.funcPtrs address with
    | none =>
      simp only [pointer, Sem.throwUB, throw_bind_sem]
      exact .error _
    | some id =>
      simp only [pointer, pure_bind]
      cases declaration : base.funcTys signature with
      | none =>
        simp only [declaration, Sem.throwTypeError, throw_bind_sem]
        exact .error _
      | some signatureDef =>
        simp only [declaration, pure_bind]
        have related := headers id
        cases sourceFound : source id with
        | none =>
          cases targetFound : target id with
          | none =>
            simp only [
              show (scopedContext base source sourceTypes).functions id = none from sourceFound,
              show (scopedContext base target targetTypes).functions id = none from targetFound,
              Sem.throwTypeError, throw_bind_sem]
            exact .error _
          | some function => rw [sourceFound, targetFound] at related; cases related
        | some sourceFunction =>
          cases targetFound : target id with
          | none => rw [sourceFound, targetFound] at related; cases related
          | some targetFunction =>
            rw [sourceFound, targetFound] at related
            cases related with
            | present _ _ body convention =>
              simp only [
                show (scopedContext base source sourceTypes).functions id = some sourceFunction from sourceFound,
                show (scopedContext base target targetTypes).functions id = some targetFunction from targetFound,
                pure_bind, scopedContext_forFunction, ← body, checkReturns_scoped_function]
              cases signatureCheck : checkIndirectSignature signatureDef sourceFunction.body with
              | error message =>
                simp only [signatureCheck, Sem.throwTypeError, throw_bind_sem]
                exact .error _
              | ok unit =>
                cases unit
                simp only [signatureCheck, pure_bind]
                cases arity : checkCallArity args sourceFunction.body.paramTys with
                | error message =>
                  simp only [arity, Sem.throwTypeError, throw_bind_sem]
                  exact .error _
                | ok unit =>
                  cases unit
                  simp only [arity, pure_bind]
                  apply bind_effect _ _ _ (rejectPoisonValues_fresh args "InvokeIndirect arguments") _ state fresh
                  intro _unit afterPoison freshPoison
                  apply invokeFrame_effect strategy _
                    (checkReturns_equivariant base sourceFunction.body.returnTys true false "InvokeIndirect: ")
                    _ _ (effects id sourceFunction targetFunction sourceFound targetFound depth args strategy)
                    _ _ _ _ _ _ afterPoison freshPoison
                  · intro values after freshAfter
                    exact invokeNormal_effect sourceRecurse targetRecurse base source target headers
                      sourceTypes targetTypes sourceCFG targetCFG paired block types (depth + 1)
                      strategy normal normalArgs values after freshAfter
                  · intro exception after freshAfter
                    exact invokeUnwind_effect sourceRecurse targetRecurse base source target
                      sourceTypes targetTypes sourceCFG targetCFG pads paired (depth + 1)
                      strategy unwind exception after freshAfter

/-- Complete actual terminal transfer for different caller CFGs and active
    declarations. Callee effects and paired predecessor callbacks are the
    genuine resource-induction hypotheses. No callee-freshness, successful
    normal path, FrameOk or non-poison premise is added. -/
theorem evalTransfer_effect (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (sourceCFG targetCFG : CFG)
    (pads : PadViews.PadViewsAgree sourceCFG targetCFG)
    (paired : PairedCallbacks sourceRecurse targetRecurse base source target
      sourceTypes targetTypes sourceCFG targetCFG)
    (block : BasicBlock)
    (types : TypesAgreeOn (block.terminatorResultDests ++ operandIds block.terminator) sourceTypes targetTypes)
    (depth : Nat) (strategy : PanicStrategy) (result : StepResult)
    (state : MachineState) (fresh : FreshState state) :
    EffectRelation
      (Sem.run (evalTransfer sourceRecurse (scopedContext base source sourceTypes)
        depth sourceCFG block strategy result) state)
      (Sem.run (evalTransfer targetRecurse (scopedContext base target targetTypes)
        depth targetCFG block strategy result) state) := by
  cases result with
  | Ret values => exact .returned values state state rfl
  | Stuck => exact .error _
  | Continue next args => exact paired depth next args strategy state fresh
  | CallReq id args =>
    rw [evalTransfer_call_scoped_congr sourceRecurse targetRecurse base source target headers effects
      sourceTypes targetTypes depth sourceCFG targetCFG block strategy id args]
    exact effect_refl _
  | CallIndirectReq address signature args =>
    rw [evalTransfer_indirect_scoped_congr sourceRecurse targetRecurse base source target headers effects
      sourceTypes targetTypes depth sourceCFG targetCFG block strategy address signature args]
    exact effect_refl _
  | InvokeReq id args normal normalArgs unwind =>
    exact invoke_effect sourceRecurse targetRecurse base source target headers effects
      sourceTypes targetTypes sourceCFG targetCFG pads paired block types depth strategy
      id args normal normalArgs unwind state fresh
  | InvokeIndirectReq address signature args normal normalArgs unwind =>
    exact invokeIndirect_effect sourceRecurse targetRecurse base source target headers effects
      sourceTypes targetTypes sourceCFG targetCFG pads paired block types depth strategy
      address signature args normal normalArgs unwind state fresh
  | SeqMapReq id elems => exact .error _

end TrustIr.GenericCoroAllBlocksTransfer
