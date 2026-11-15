-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixCalls
import TrustIr.Proofs.GenericCoroInvoke
import TrustIr.Proofs.GenericCoroPrefixInvokeFrame

namespace TrustIr.GenericCoro.Prefix

/-- The complete production terminal transfer, including the original raw
    indirect-invoke prelude and its exact resource/error ordering. -/
def evalTransfer (recurse : Recurse) (ctx : EvalContext) (callDepth : Nat)
    (cfg : CFG) (block : BasicBlock) (strat : PanicStrategy) (result : StepResult) : Sem (List Value) := do
  match result with
  | .Ret values => pure values
  | .Stuck => Sem.throwUB "reached unreachable"
  | .Continue nextPc nextArgs =>
    recurse ctx callDepth cfg nextPc nextArgs strat
  | .CallReq calleeId callArgs =>
    match callDepth with
    | 0 => throw SemError.outOfFuel
    | callDepth + 1 => do
      let callee ← ctx.lookupDirectCallee calleeId
        "Call: callee is a bodyless declaration" "Call: undefined function"
      requireUntypedAbi callee.body.abi
      match checkCallArity callArgs callee.body.paramTys with
      | .ok () => pure ()
      | .error msg => Sem.throwTypeError ("Call: " ++ msg)
      Sem.rejectPoisonValues callArgs "Call arguments"
      let callerState ← Sem.getState
      let frame := saveFrame callerState none
      Sem.setState
        { callerState with locals := ValueMap.empty, nextValueId := 0 }
      let retVals ← recurse (ctx.forFunction callee) callDepth
        callee.cfg callee.entryBlock callArgs strat
      match checkReturnArity retVals callee.body.returnTys with
      | .ok () => pure ()
      | .error msg => Sem.throwTypeError ("Call: " ++ msg)
      Sem.rejectPoisonValues retVals "Call returns"
      match block.terminator with
      | .CallIndirect valueId _ _ _ =>
        match frame.locals valueId with
        | some (.typedClosure _ _ _) =>
          for (t, v) in callee.body.returnTys.zip retVals do
            match checkClosureValue ctx t v with
            | .ok () => pure ()
            | .error e => throw e
        | _ => pure ()
      | _ => pure ()
      let calleeState ← Sem.getState
      Sem.setState (restoreFrame calleeState frame [])
      pure retVals
  | .CallIndirectReq addr sig callArgs =>
    match callDepth with
    | 0 => throw SemError.outOfFuel
    | callDepth + 1 => do
      let calleeId ← match ctx.funcPtrs addr with
        | some fid => pure fid
        | none => Sem.throwUB "CallIndirect: invalid function pointer"
      let sigDef ← match ctx.funcTys sig with
        | some def_ => pure def_
        | none => Sem.throwTypeError "CallIndirect: undefined function type"
      let callee ← match ctx.functions calleeId with
        | some f => pure f
        | none => Sem.throwTypeError "CallIndirect: undefined function"
      requireUntypedAbi sigDef.abi
      match checkIndirectSignature sigDef callee.body with
      | .ok () => pure ()
      | .error msg => Sem.throwTypeError ("CallIndirect: " ++ msg)
      requireUntypedAbi callee.body.abi
      match checkCallArity callArgs callee.body.paramTys with
      | .ok () => pure ()
      | .error msg => Sem.throwTypeError ("CallIndirect: " ++ msg)
      Sem.rejectPoisonValues callArgs "CallIndirect arguments"
      let callerState ← Sem.getState
      let frame := saveFrame callerState none
      Sem.setState
        { callerState with locals := ValueMap.empty, nextValueId := 0 }
      let retVals ← recurse (ctx.forFunction callee) callDepth
        callee.cfg callee.entryBlock callArgs strat
      match checkReturnArity retVals callee.body.returnTys with
      | .ok () => pure ()
      | .error msg => Sem.throwTypeError ("CallIndirect: " ++ msg)
      Sem.rejectPoisonValues retVals "Call returns"
      let calleeState ← Sem.getState
      Sem.setState (restoreFrame calleeState frame [])
      pure retVals
  | .InvokeReq calleeId callArgs normalDest normalArgIds unwindDest =>
    -- Mirrors interpret.rs Inst::Invoke: run the call exactly like
    -- CallReq, bind the callee's returns to the invoke node's result
    -- destinations, THEN evaluate the normal-edge arguments (they may
    -- reference those results) and take the normal edge. Under `.abort`
    -- the unwind destination is never taken; under `.unwind` an
    -- unwinding out of the callee enters its pad (R3, R4).
    match callDepth with
    | 0 => throw SemError.outOfFuel
    | innerDepth + 1 => do
      let callee ← ctx.lookupDirectCallee calleeId
        "Invoke: callee is a bodyless declaration" "Invoke: undefined function"
      requireUntypedAbi callee.body.abi
      match checkCallArity callArgs callee.body.paramTys with
      | .ok () => pure ()
      | .error msg => Sem.throwTypeError ("Invoke: " ++ msg)
      Sem.rejectPoisonValues callArgs "Call arguments"
      let callerState ← Sem.getState
      let frame := saveFrame callerState none
      Sem.setState
        { callerState with locals := ValueMap.empty, nextValueId := 0 }
      -- R3 (amendment D, Part 2): under `.unwind` an unwinding out of the
      -- callee is caught here; under `.abort` the outcome is always `inl`.
      let outcome ← invokeCatch strat (recurse (ctx.forFunction callee) innerDepth
        callee.cfg callee.entryBlock callArgs strat)
      match outcome with
      | .inl retVals => do
        match checkReturnArity retVals callee.body.returnTys with
        | .ok () => pure ()
        | .error msg => Sem.throwTypeError ("Invoke: " ++ msg)
        Sem.rejectPoisonValues retVals "Call returns"
        let calleeState ← Sem.getState
        Sem.setState (restoreFrame calleeState frame [])
        ctx.bindCallResults block.terminator block.terminatorResultDests retVals
        let edgeArgs ← normalArgIds.mapM Sem.lookupValue
        -- The normal edge continues the CALLER: depth bounds NESTING only
        -- (mirrors interpret.rs, where the caller resumes at its own depth
        -- after Step::Jump), so the continuation runs at the UNdecremented
        -- depth — an Invoke must not permanently burn depth budget.
        recurse ctx (innerDepth + 1) cfg normalDest edgeArgs strat
      | .inr (exn, st) => do
        -- The caller's frame back over the memory the unwinding left; no
        -- result binds and the normal-edge arguments are not evaluated.
        Sem.setState (restoreFrame st frame [])
        semEnterPad cfg exn unwindDest
        recurse ctx (innerDepth + 1) cfg unwindDest [] strat
  | .InvokeIndirectReq addr sig callArgs normalDest normalArgIds unwindDest =>
    -- Amendment D, Part 2: `CallIndirect`'s unwinding twin (mirrors
    -- interpret.rs Inst::InvokeIndirect): resolve and check the callee
    -- exactly as `CallIndirectReq`, run it, bind its returns to the
    -- node's result destinations, then evaluate the normal-edge
    -- arguments and take the normal edge at the CALLER's (undecremented)
    -- depth, exactly as `InvokeReq`, whose unwind rules it shares.
    match callDepth with
    | 0 => throw SemError.outOfFuel
    | innerDepth + 1 => do
      let calleeId ← match ctx.funcPtrs addr with
        | some fid => pure fid
        | none => Sem.throwUB "InvokeIndirect: invalid function pointer"
      let sigDef ← match ctx.funcTys sig with
        | some def_ => pure def_
        | none => Sem.throwTypeError "InvokeIndirect: undefined function type"
      let callee ← match ctx.functions calleeId with
        | some f => pure f
        | none => Sem.throwTypeError "InvokeIndirect: undefined function"
      match checkIndirectSignature sigDef callee.body with
      | .ok () => pure ()
      | .error msg => Sem.throwTypeError ("InvokeIndirect: " ++ msg)
      match checkCallArity callArgs callee.body.paramTys with
      | .ok () => pure ()
      | .error msg => Sem.throwTypeError ("InvokeIndirect: " ++ msg)
      Sem.rejectPoisonValues callArgs "InvokeIndirect arguments"
      let callerState ← Sem.getState
      let frame := saveFrame callerState none
      Sem.setState
        { callerState with locals := ValueMap.empty, nextValueId := 0 }
      let outcome ← invokeCatch strat (recurse (ctx.forFunction callee) innerDepth
        callee.cfg callee.entryBlock callArgs strat)
      match outcome with
      | .inl retVals => do
        match checkReturnArity retVals callee.body.returnTys with
        | .ok () => pure ()
        | .error msg => Sem.throwTypeError ("InvokeIndirect: " ++ msg)
        Sem.rejectPoisonValues retVals "Call returns"
        let calleeState ← Sem.getState
        Sem.setState (restoreFrame calleeState frame [])
        ctx.bindCallResults block.terminator block.terminatorResultDests retVals
        let edgeArgs ← normalArgIds.mapM Sem.lookupValue
        recurse ctx (innerDepth + 1) cfg normalDest edgeArgs strat
      | .inr (exn, st) => do
        Sem.setState (restoreFrame st frame [])
        semEnterPad cfg exn unwindDest
        recurse ctx (innerDepth + 1) cfg unwindDest [] strat
  | .SeqMapReq _ _ =>
    -- A SeqMap in terminator position is malformed IR (it is not a
    -- terminator; Rust-side validation rejects it). Fail closed.
    Sem.throwTypeError "SeqMap is not a terminator"

/-- Extraction exposes only the final transfer; the actual layer prefix is
    preserved definitionally, including drop resolution and result checking. -/
theorem evalLayer_eq_transfer (recurse : Recurse) (ctx : EvalContext) (callDepth : Nat)
    (cfg : CFG) (pc : BlockId) (args : List Value) (strat : PanicStrategy) :
    evalLayer recurse ctx callDepth cfg pc args strat = (do
      match cfg pc with
      | none => Sem.throwTypeError s!"undefined block: {repr pc}"
      | some blk => do
        -- Amendment D (§20 rule 3): every drop of the block is resolved
        -- through the context's drop-glue table BEFORE dispatch, so a resolved
        -- drop runs the `Call` / `Invoke` rules below verbatim, and an
        -- unresolved one reaches the bare `stepInst`, which refuses it.
        let block := ctx.resolveBlock blk
        bindBlockParamsChecked block.params args
        evalBody recurse ctx callDepth strat (bodyInstsWithResultDests block.body block.bodyResultDests)
        -- Under `.unwind` a failing `AssertInvoke` enters its pad and `Resume`
        -- re-raises (`stepTermUnwind`); under `.abort` the bare step.
        let termResult ← stepTermWithContext ctx callDepth cfg block.terminator strat
        let result ← match termResult with
          | .terminator sr => pure sr
          | .value _ => Sem.throwTypeError "basic block does not end with a terminator"
          | .values _ => Sem.throwTypeError "basic block does not end with a terminator"
        evalTransfer recurse ctx callDepth cfg block strat result) := by rfl

def terminalClosureCheck (term : Inst) (frame : StackFrame) : Bool :=
  match term with
  | .CallIndirect valueId _ _ _ =>
    match frame.locals valueId with
    | some (.typedClosure _ _ _) => true
    | _ => false
  | _ => false

private theorem storedClosure_branch_bind {α β : Type} (stored : Option Value)
    (yes no : Sem α) (next : α → Sem β) :
    ((if (match stored with | some (.typedClosure _ _ _) => true | _ => false) then yes else no) >>= next) =
      (match stored with
       | some (.typedClosure _ _ _) => yes >>= next
       | _ => no >>= next) := by
  cases stored with
  | none => rfl
  | some value => cases value <;> rfl

private theorem finishCalleeWith_terminal_checks (ctx : EvalContext) (returns : List Ty)
    (term : Inst) (frame : StackFrame) (callee : Sem (List Value)) :
    finishCalleeWith (checkReturns ctx returns true (terminalClosureCheck term frame) "Call: ") frame callee =
      (do
        let values ← callee
        match checkReturnArity values returns with
        | .ok () => pure ()
        | .error message => Sem.throwTypeError ("Call: " ++ message)
        Sem.rejectPoisonValues values "Call returns"
        match term with
        | .CallIndirect valueId _ _ _ =>
          match frame.locals valueId with
          | some (.typedClosure _ _ _) =>
            for (ty, value) in returns.zip values do
              match checkClosureValue ctx ty value with
              | .ok () => pure ()
              | .error error => throw error
          | _ => pure ()
        | _ => pure ()
        let state ← Sem.getState
        Sem.setState (restoreFrame state frame [])
        pure values) := by
  trustIrCompilerProof {
    simp only [finishCalleeWith, bind_assoc]
    apply bind_same
    intro values
    cases arity : checkReturnArity values returns with
    | error message =>
      simp only [checkReturns, arity, Sem.throwTypeError, throw_bind_sem, bind_assoc]
    | ok unit =>
      cases unit
      simp only [checkReturns, arity, pure_bind, Bool.true_eq, if_true, bind_assoc]
      apply bind_same
      intro unit
      cases term <;> simp only [terminalClosureCheck, Bool.false_eq_true, if_false, pure_bind]
      rw [storedClosure_branch_bind]
      simp only [bind_assoc, pure_bind]
      rfl
  } {
    simp only [finishCalleeWith, bind_assoc]
    apply bind_same
    intro values
    cases arity : checkReturnArity values returns with
    | error message =>
      simp only [checkReturns, arity, Sem.throwTypeError, throw_bind_sem, bind_assoc]
    | ok unit =>
      cases unit
      simp only [checkReturns, arity, pure_bind, Bool.true_eq, if_true, bind_assoc]
      apply bind_same
      intro unit
      cases term <;> simp only [terminalClosureCheck, Bool.false_eq_true, if_false, pure_bind]
      split <;> split <;> simp_all [bind_assoc, pure_bind]
      all_goals rfl
  }

def terminalCall (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (block : BasicBlock) (strategy : PanicStrategy) (id : FuncId) (args : List Value) : Sem (List Value) :=
  match depth with
  | 0 => throw SemError.outOfFuel
  | depth + 1 => do
    let callee ← ctx.lookupDirectCallee id
      "Call: callee is a bodyless declaration" "Call: undefined function"
    directCallHeader callee.body args
    let caller ← Sem.getState
    Sem.setState (callerWorld caller)
    finishCalleeWith
      (checkReturns ctx callee.body.returnTys true
        (terminalClosureCheck block.terminator (saveFrame caller none)) "Call: ")
      (saveFrame caller none)
      (recurse (ctx.forFunction callee) depth callee.cfg callee.entryBlock args strategy)

theorem evalTransfer_call_eq (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy) (id : FuncId) (args : List Value) :
    evalTransfer recurse ctx depth cfg block strategy (.CallReq id args) =
      terminalCall recurse ctx depth block strategy id args := by
  cases depth with
  | zero => rfl
  | succ depth =>
    simp only [evalTransfer, terminalCall, directCallHeader, bind_assoc]
    apply bind_same
    intro callee
    apply bind_same
    intro unit
    cases arity : checkCallArity args callee.body.paramTys with
    | error message =>
      simp only [arity, Sem.throwTypeError, throw_bind_sem, bind_assoc]
    | ok unit =>
      cases unit
      simp only [arity, pure_bind]
      apply bind_same
      intro unit
      apply bind_same
      intro caller
      apply bind_same
      intro unit
      exact (finishCalleeWith_terminal_checks ctx callee.body.returnTys block.terminator
        (saveFrame caller none) _).symm

private theorem typesAgreeOn_refl (ids : List ValueId) (types : Option LocalTypeTable) :
    TypesAgreeOn ids types types := by
  cases types with
  | none => exact .absent
  | some table => exact .present table table (fun _ _ => rfl)

private theorem terminalCall_congr (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (types : Option LocalTypeTable) (depth : Nat) (block : BasicBlock)
    (strategy : PanicStrategy) (id : FuncId) (args : List Value) :
    terminalCall sourceRecurse (scopedContext base source types) depth block strategy id args =
      terminalCall targetRecurse (scopedContext base target types) depth block strategy id args := by
  cases depth with
  | zero => rfl
  | succ depth =>
    have related := headers id
    cases sourceFound : source id with
    | none =>
      cases targetFound : target id with
      | none =>
        simp only [terminalCall, EvalContext.lookupDirectCallee, scopedContext, sourceFound, targetFound]
        split <;> rfl
      | some function => rw [sourceFound, targetFound] at related; cases related
    | some sourceFunction =>
      cases targetFound : target id with
      | none => rw [sourceFound, targetFound] at related; cases related
      | some targetFunction =>
        rw [sourceFound, targetFound] at related
        cases related with
        | present _ _ body convention =>
          simp only [terminalCall, EvalContext.lookupDirectCallee,
            show (scopedContext base source types).functions id = some sourceFunction from sourceFound,
            show (scopedContext base target types).functions id = some targetFunction from targetFound,
            pure_bind, scopedContext_forFunction, ← body, checkReturns_scoped_function]
          apply bind_same
          intro unit
          funext world
          exact finishCalleeWith_eq_of_effectRelation
            (checkReturns base sourceFunction.body.returnTys true
              (terminalClosureCheck block.terminator (saveFrame world none)) "Call: ")
            (checkReturns_equivariant base sourceFunction.body.returnTys true
              (terminalClosureCheck block.terminator (saveFrame world none)) "Call: ")
            (saveFrame world none) _ _ (callerWorld world) (callerWorld world)
            (effects id sourceFunction targetFunction sourceFound targetFound depth args strategy world)

private theorem callFrameWith_poison_eq (ctx : EvalContext) (returns : List Ty)
    (message : String) (callee : Sem (List Value)) :
    callFrameWith (checkReturns ctx returns true false message) callee = (do
      let caller ← Sem.getState
      Sem.setState (callerWorld caller)
      let values ← callee
      match checkReturnArity values returns with
      | .ok () => pure ()
      | .error error => Sem.throwTypeError (message ++ error)
      Sem.rejectPoisonValues values "Call returns"
      let state ← Sem.getState
      Sem.setState (restoreFrame state (saveFrame caller none) [])
      pure values) := by
  simpa only [bind_pure, Bool.true_eq, Bool.false_eq_true, if_true, if_false, pure_bind] using
    callFrameWith_checkReturns_bind ctx returns true false message callee pure

def terminalIndirect (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (strategy : PanicStrategy) (address : Nat) (signature : FuncTyId) (args : List Value) : Sem (List Value) :=
  match depth with
  | 0 => throw SemError.outOfFuel
  | depth + 1 => do
    let id ← match ctx.funcPtrs address with
      | some id => pure id
      | none => Sem.throwUB "CallIndirect: invalid function pointer"
    let declaration ← match ctx.funcTys signature with
      | some declaration => pure declaration
      | none => Sem.throwTypeError "CallIndirect: undefined function type"
    let callee ← match ctx.functions id with
      | some callee => pure callee
      | none => Sem.throwTypeError "CallIndirect: undefined function"
    requireUntypedAbi declaration.abi
    match checkIndirectSignature declaration callee.body with
    | .ok () => pure ()
    | .error message => Sem.throwTypeError ("CallIndirect: " ++ message)
    requireUntypedAbi callee.body.abi
    match checkCallArity args callee.body.paramTys with
    | .ok () => pure ()
    | .error message => Sem.throwTypeError ("CallIndirect: " ++ message)
    Sem.rejectPoisonValues args "CallIndirect arguments"
    callFrameWith (checkReturns ctx callee.body.returnTys true false "CallIndirect: ")
      (recurse (ctx.forFunction callee) depth callee.cfg callee.entryBlock args strategy)

theorem evalTransfer_indirect_eq (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy)
    (address : Nat) (signature : FuncTyId) (args : List Value) :
    evalTransfer recurse ctx depth cfg block strategy (.CallIndirectReq address signature args) =
      terminalIndirect recurse ctx depth strategy address signature args := by
  cases depth with
  | zero => rfl
  | succ depth =>
    simp only [evalTransfer, terminalIndirect]
    cases pointer : ctx.funcPtrs address with
    | none => simp only [pointer, Sem.throwUB, throw_bind_sem]
    | some id =>
      simp only [pointer, pure_bind]
      cases declaration : ctx.funcTys signature with
      | none => simp only [declaration, Sem.throwTypeError, throw_bind_sem]
      | some signatureDef =>
        simp only [declaration, pure_bind]
        cases function : ctx.functions id with
        | none => simp only [function, Sem.throwTypeError, throw_bind_sem]
        | some callee =>
          simp only [function, pure_bind]
          apply bind_same
          intro unit
          cases checked : checkIndirectSignature signatureDef callee.body with
          | error message => simp only [checked, Sem.throwTypeError, throw_bind_sem]
          | ok unit =>
            cases unit
            simp only [checked, pure_bind]
            apply bind_same
            intro unit
            cases arity : checkCallArity args callee.body.paramTys with
            | error message => simp only [arity, Sem.throwTypeError, throw_bind_sem]
            | ok unit =>
              cases unit
              simp only [arity, pure_bind]
              apply bind_same
              intro unit
              exact (callFrameWith_poison_eq ctx callee.body.returnTys "CallIndirect: " _).symm

private theorem scoped_funcPtrs (base : EvalContext) (functions : FuncId → Option EvalFunction)
    (types : Option LocalTypeTable) : (scopedContext base functions types).funcPtrs = base.funcPtrs := rfl

private theorem scoped_funcTys (base : EvalContext) (functions : FuncId → Option EvalFunction)
    (types : Option LocalTypeTable) : (scopedContext base functions types).funcTys = base.funcTys := rfl

private theorem terminalIndirect_congr (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (types : Option LocalTypeTable) (depth : Nat) (strategy : PanicStrategy)
    (address : Nat) (signature : FuncTyId) (args : List Value) :
    terminalIndirect sourceRecurse (scopedContext base source types) depth strategy address signature args =
      terminalIndirect targetRecurse (scopedContext base target types) depth strategy address signature args := by
  cases depth with
  | zero => rfl
  | succ depth =>
    simp only [terminalIndirect, scoped_funcPtrs, scoped_funcTys]
    cases pointer : base.funcPtrs address with
    | none => simp only [pointer, Sem.throwUB, throw_bind_sem]
    | some id =>
      simp only [pointer, pure_bind]
      cases declaration : base.funcTys signature with
      | none => simp only [declaration, Sem.throwTypeError, throw_bind_sem]
      | some signatureDef =>
        simp only [declaration, pure_bind]
        have related := headers id
        cases sourceFound : source id with
        | none =>
          cases targetFound : target id with
          | none =>
            simp only [
              show (scopedContext base source types).functions id = none from sourceFound,
              show (scopedContext base target types).functions id = none from targetFound,
              Sem.throwTypeError, throw_bind_sem]
          | some function => rw [sourceFound, targetFound] at related; cases related
        | some sourceFunction =>
          cases targetFound : target id with
          | none => rw [sourceFound, targetFound] at related; cases related
          | some targetFunction =>
            rw [sourceFound, targetFound] at related
            cases related with
            | present _ _ body convention =>
              have framed := callFrameWith_eq_of_effectRelation
                (checkReturns base sourceFunction.body.returnTys true false "CallIndirect: ")
                (checkReturns_equivariant base sourceFunction.body.returnTys true false "CallIndirect: ")
                (sourceRecurse (scopedContext base source sourceFunction.localTypes) depth
                  sourceFunction.cfg sourceFunction.entryBlock args strategy)
                (targetRecurse (scopedContext base target targetFunction.localTypes) depth
                  targetFunction.cfg targetFunction.entryBlock args strategy)
                (effects id sourceFunction targetFunction sourceFound targetFound depth args strategy)
              simp only [
                show (scopedContext base source types).functions id = some sourceFunction from sourceFound,
                show (scopedContext base target types).functions id = some targetFunction from targetFound,
                pure_bind, scopedContext_forFunction, ← body, checkReturns_scoped_function, framed]

private abbrev SameCFGRecursors (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) : Prop :=
  ∀ types depth cfg pc args strategy,
    sourceRecurse (scopedContext base source types) depth cfg pc args strategy =
      targetRecurse (scopedContext base target types) depth cfg pc args strategy

private def invokeNormal (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (cfg : CFG)
    (block : BasicBlock) (strategy : PanicStrategy) (next : BlockId) (argIds : List ValueId)
    (values : List Value) : Sem (List Value) := do
  ctx.bindCallResults block.terminator block.terminatorResultDests values
  let args ← argIds.mapM Sem.lookupValue
  recurse ctx depth cfg next args strategy

private def invokeUnwind (recurse : Recurse) (ctx : EvalContext) (depth : Nat) (cfg : CFG)
    (strategy : PanicStrategy) (next : BlockId) (exception : Addr) : Sem (List Value) := do
  semEnterPad cfg exception next
  recurse ctx depth cfg next [] strategy

private theorem invokeNormal_congr (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (sameCFG : SameCFGRecursors sourceRecurse targetRecurse base source target)
    (types : Option LocalTypeTable) (depth : Nat) (cfg : CFG) (block : BasicBlock)
    (strategy : PanicStrategy) (next : BlockId) (argIds : List ValueId) :
    invokeNormal sourceRecurse (scopedContext base source types) depth cfg block strategy next argIds =
      invokeNormal targetRecurse (scopedContext base target types) depth cfg block strategy next argIds := by
  funext values
  unfold invokeNormal
  rw [bindCallResults_congr base source target headers types types block.terminator
    block.terminatorResultDests values (typesAgreeOn_refl _ types)]
  apply bind_same
  intro unit
  apply bind_same
  intro args
  exact sameCFG types depth cfg next args strategy

private theorem invokeUnwind_congr (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction)
    (sameCFG : SameCFGRecursors sourceRecurse targetRecurse base source target)
    (types : Option LocalTypeTable) (depth : Nat) (cfg : CFG)
    (strategy : PanicStrategy) (next : BlockId) :
    invokeUnwind sourceRecurse (scopedContext base source types) depth cfg strategy next =
      invokeUnwind targetRecurse (scopedContext base target types) depth cfg strategy next := by
  funext exception
  unfold invokeUnwind
  apply bind_same
  intro unit
  exact sameCFG types depth cfg next [] strategy

private def terminalInvoke (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy)
    (id : FuncId) (args : List Value) (normal : BlockId) (normalArgs : List ValueId)
    (unwind : BlockId) : Sem (List Value) :=
  match depth with
  | 0 => throw SemError.outOfFuel
  | innerDepth + 1 => do
    let callee ← ctx.lookupDirectCallee id
      "Invoke: callee is a bodyless declaration" "Invoke: undefined function"
    requireUntypedAbi callee.body.abi
    match checkCallArity args callee.body.paramTys with
    | .ok () => pure ()
    | .error message => Sem.throwTypeError ("Invoke: " ++ message)
    Sem.rejectPoisonValues args "Call arguments"
    invokeFrameWith strategy (checkReturns ctx callee.body.returnTys true false "Invoke: ")
      (recurse (ctx.forFunction callee) innerDepth callee.cfg callee.entryBlock args strategy)
      (invokeNormal recurse ctx (innerDepth + 1) cfg block strategy normal normalArgs)
      (invokeUnwind recurse ctx (innerDepth + 1) cfg strategy unwind)

private theorem evalTransfer_invoke_eq (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy) (id : FuncId) (args : List Value)
    (normal : BlockId) (normalArgs : List ValueId) (unwind : BlockId) :
    evalTransfer recurse ctx depth cfg block strategy (.InvokeReq id args normal normalArgs unwind) =
      terminalInvoke recurse ctx depth cfg block strategy id args normal normalArgs unwind := by
  cases depth with
  | zero => rfl
  | succ depth =>
    simp only [evalTransfer, terminalInvoke]
    apply bind_same
    intro callee
    apply bind_same
    intro unit
    cases arity : checkCallArity args callee.body.paramTys with
    | error message => simp only [arity, Sem.throwTypeError, throw_bind_sem]
    | ok unit =>
      cases unit
      simp only [arity, pure_bind]
      apply bind_same
      intro unit
      exact (invokeFrameWith_checkReturns strategy ctx callee.body.returnTys "Invoke: " _
        (invokeNormal recurse ctx (depth + 1) cfg block strategy normal normalArgs)
        (invokeUnwind recurse ctx (depth + 1) cfg strategy unwind)).symm

/-- Resolve both original callable tables before comparing their continuations.
    Keeping the continuations abstract avoids duplicating the complete invoke
    computation in each dependent lookup case. No header field is weakened. -/
private theorem lookupDirectCallee_bind_headers {α : Type} (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (types : Option LocalTypeTable) (id : FuncId) (declaredMessage missingMessage : String)
    (left right : EvalFunction → Sem α)
    (same : ∀ sourceFunction targetFunction,
      source id = some sourceFunction → target id = some targetFunction →
      sourceFunction.body = targetFunction.body →
      sourceFunction.callingConv = targetFunction.callingConv →
      left sourceFunction = right targetFunction) :
    ((scopedContext base source types).lookupDirectCallee id declaredMessage missingMessage >>= left) =
      ((scopedContext base target types).lookupDirectCallee id declaredMessage missingMessage >>= right) := by
  have related := headers id
  cases sourceFound : source id with
  | none =>
    cases targetFound : target id with
    | none =>
      simp only [EvalContext.lookupDirectCallee, scopedContext, sourceFound, targetFound]
      split <;> rfl
    | some function => rw [sourceFound, targetFound] at related; cases related
  | some sourceFunction =>
    cases targetFound : target id with
    | none => rw [sourceFound, targetFound] at related; cases related
    | some targetFunction =>
      rw [sourceFound, targetFound] at related
      cases related with
      | present _ _ body convention =>
        simp only [EvalContext.lookupDirectCallee,
          show (scopedContext base source types).functions id = some sourceFunction from sourceFound,
          show (scopedContext base target types).functions id = some targetFunction from targetFound,
          pure_bind]
        exact same sourceFunction targetFunction sourceFound targetFound body convention

private theorem terminalInvoke_congr (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (sameCFG : SameCFGRecursors sourceRecurse targetRecurse base source target)
    (types : Option LocalTypeTable) (depth : Nat) (cfg : CFG) (block : BasicBlock)
    (strategy : PanicStrategy) (id : FuncId) (args : List Value)
    (normal : BlockId) (normalArgs : List ValueId) (unwind : BlockId) :
    terminalInvoke sourceRecurse (scopedContext base source types) depth cfg block strategy
      id args normal normalArgs unwind =
      terminalInvoke targetRecurse (scopedContext base target types) depth cfg block strategy
        id args normal normalArgs unwind := by
  cases depth with
  | zero => rfl
  | succ depth =>
    simp only [terminalInvoke]
    apply lookupDirectCallee_bind_headers (α := List Value) base source target headers types id
      "Invoke: callee is a bodyless declaration" "Invoke: undefined function"
    intro sourceFunction targetFunction sourceFound targetFound body convention
    have normalEqual := invokeNormal_congr sourceRecurse targetRecurse base source target headers
      sameCFG types (depth + 1) cfg block strategy normal normalArgs
    have unwindEqual := invokeUnwind_congr sourceRecurse targetRecurse base source target
      sameCFG types (depth + 1) cfg strategy unwind
    have framed := invokeFrameWith_eq_of_effectRelation strategy
      (checkReturns base sourceFunction.body.returnTys true false "Invoke: ")
      (checkReturns_equivariant base sourceFunction.body.returnTys true false "Invoke: ")
      (sourceRecurse (scopedContext base source sourceFunction.localTypes) depth
        sourceFunction.cfg sourceFunction.entryBlock args strategy)
      (targetRecurse (scopedContext base target targetFunction.localTypes) depth
        targetFunction.cfg targetFunction.entryBlock args strategy)
      (invokeNormal targetRecurse (scopedContext base target types) (depth + 1)
        cfg block strategy normal normalArgs)
      (invokeUnwind targetRecurse (scopedContext base target types) (depth + 1) cfg strategy unwind)
      (effects id sourceFunction targetFunction sourceFound targetFound depth args strategy)
    simp only [pure_bind, scopedContext_forFunction, ← body, checkReturns_scoped_function,
      normalEqual, unwindEqual, framed]

private def terminalInvokeIndirect (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy)
    (address : Nat) (signature : FuncTyId) (args : List Value)
    (normal : BlockId) (normalArgs : List ValueId) (unwind : BlockId) : Sem (List Value) :=
  match depth with
  | 0 => throw SemError.outOfFuel
  | innerDepth + 1 => do
    let id ← match ctx.funcPtrs address with
      | some id => pure id
      | none => Sem.throwUB "InvokeIndirect: invalid function pointer"
    let declaration ← match ctx.funcTys signature with
      | some declaration => pure declaration
      | none => Sem.throwTypeError "InvokeIndirect: undefined function type"
    let callee ← match ctx.functions id with
      | some callee => pure callee
      | none => Sem.throwTypeError "InvokeIndirect: undefined function"
    match checkIndirectSignature declaration callee.body with
    | .ok () => pure ()
    | .error message => Sem.throwTypeError ("InvokeIndirect: " ++ message)
    match checkCallArity args callee.body.paramTys with
    | .ok () => pure ()
    | .error message => Sem.throwTypeError ("InvokeIndirect: " ++ message)
    Sem.rejectPoisonValues args "InvokeIndirect arguments"
    invokeFrameWith strategy (checkReturns ctx callee.body.returnTys true false "InvokeIndirect: ")
      (recurse (ctx.forFunction callee) innerDepth callee.cfg callee.entryBlock args strategy)
      (invokeNormal recurse ctx (innerDepth + 1) cfg block strategy normal normalArgs)
      (invokeUnwind recurse ctx (innerDepth + 1) cfg strategy unwind)

private theorem evalTransfer_invokeIndirect_eq (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy)
    (address : Nat) (signature : FuncTyId) (args : List Value)
    (normal : BlockId) (normalArgs : List ValueId) (unwind : BlockId) :
    evalTransfer recurse ctx depth cfg block strategy
      (.InvokeIndirectReq address signature args normal normalArgs unwind) =
      terminalInvokeIndirect recurse ctx depth cfg block strategy address signature args normal normalArgs unwind := by
  cases depth with
  | zero => rfl
  | succ depth =>
    simp only [evalTransfer, terminalInvokeIndirect]
    cases pointer : ctx.funcPtrs address with
    | none => simp only [pointer, Sem.throwUB, throw_bind_sem]
    | some id =>
      simp only [pointer, pure_bind]
      cases declaration : ctx.funcTys signature with
      | none => simp only [declaration, Sem.throwTypeError, throw_bind_sem]
      | some signatureDef =>
        simp only [declaration, pure_bind]
        cases function : ctx.functions id with
        | none => simp only [function, Sem.throwTypeError, throw_bind_sem]
        | some callee =>
          simp only [function, pure_bind]
          cases checked : checkIndirectSignature signatureDef callee.body with
          | error message => simp only [checked, Sem.throwTypeError, throw_bind_sem]
          | ok unit =>
            cases unit
            simp only [checked, pure_bind]
            cases arity : checkCallArity args callee.body.paramTys with
            | error message => simp only [arity, Sem.throwTypeError, throw_bind_sem]
            | ok unit =>
              cases unit
              simp only [arity, pure_bind]
              apply bind_same
              intro unit
              exact (invokeFrameWith_checkReturns strategy ctx callee.body.returnTys "InvokeIndirect: " _
                (invokeNormal recurse ctx (depth + 1) cfg block strategy normal normalArgs)
                (invokeUnwind recurse ctx (depth + 1) cfg strategy unwind)).symm

private theorem terminalInvokeIndirect_congr (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (sameCFG : SameCFGRecursors sourceRecurse targetRecurse base source target)
    (types : Option LocalTypeTable) (depth : Nat) (cfg : CFG) (block : BasicBlock)
    (strategy : PanicStrategy) (address : Nat) (signature : FuncTyId) (args : List Value)
    (normal : BlockId) (normalArgs : List ValueId) (unwind : BlockId) :
    terminalInvokeIndirect sourceRecurse (scopedContext base source types) depth cfg block strategy
      address signature args normal normalArgs unwind =
      terminalInvokeIndirect targetRecurse (scopedContext base target types) depth cfg block strategy
        address signature args normal normalArgs unwind := by
  cases depth with
  | zero => rfl
  | succ depth =>
    simp only [terminalInvokeIndirect, scoped_funcPtrs, scoped_funcTys]
    cases pointer : base.funcPtrs address with
    | none => simp only [pointer, Sem.throwUB, throw_bind_sem]
    | some id =>
      simp only [pointer, pure_bind]
      cases declaration : base.funcTys signature with
      | none => simp only [declaration, Sem.throwTypeError, throw_bind_sem]
      | some signatureDef =>
        simp only [declaration, pure_bind]
        have related := headers id
        cases sourceFound : source id with
        | none =>
          cases targetFound : target id with
          | none =>
            simp only [
              show (scopedContext base source types).functions id = none from sourceFound,
              show (scopedContext base target types).functions id = none from targetFound,
              Sem.throwTypeError, throw_bind_sem]
          | some function => rw [sourceFound, targetFound] at related; cases related
        | some sourceFunction =>
          cases targetFound : target id with
          | none => rw [sourceFound, targetFound] at related; cases related
          | some targetFunction =>
            rw [sourceFound, targetFound] at related
            cases related with
            | present _ _ body convention =>
              have normalEqual := invokeNormal_congr sourceRecurse targetRecurse base source target headers
                sameCFG types (depth + 1) cfg block strategy normal normalArgs
              have unwindEqual := invokeUnwind_congr sourceRecurse targetRecurse base source target
                sameCFG types (depth + 1) cfg strategy unwind
              have framed := invokeFrameWith_eq_of_effectRelation strategy
                (checkReturns base sourceFunction.body.returnTys true false "InvokeIndirect: ")
                (checkReturns_equivariant base sourceFunction.body.returnTys true false "InvokeIndirect: ")
                (sourceRecurse (scopedContext base source sourceFunction.localTypes) depth
                  sourceFunction.cfg sourceFunction.entryBlock args strategy)
                (targetRecurse (scopedContext base target targetFunction.localTypes) depth
                  targetFunction.cfg targetFunction.entryBlock args strategy)
                (invokeNormal targetRecurse (scopedContext base target types) (depth + 1)
                  cfg block strategy normal normalArgs)
                (invokeUnwind targetRecurse (scopedContext base target types) (depth + 1) cfg strategy unwind)
                (effects id sourceFunction targetFunction sourceFound targetFound depth args strategy)
              simp only [
                show (scopedContext base source types).functions id = some sourceFunction from sourceFound,
                show (scopedContext base target types).functions id = some targetFunction from targetFound,
                pure_bind, scopedContext_forFunction, ← body, checkReturns_scoped_function,
                normalEqual, unwindEqual, framed]

/-- Complete terminal transfer congruence for the actual evaluator layer.
    Callee effects and same-CFG callbacks are precisely the two smaller-fuel
    induction hypotheses; the caller state and its SSA frame are arbitrary. -/
theorem evalTransfer_congr (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (sameCFG : ∀ types depth cfg pc args strategy,
      sourceRecurse (scopedContext base source types) depth cfg pc args strategy =
        targetRecurse (scopedContext base target types) depth cfg pc args strategy)
    (types : Option LocalTypeTable) (depth : Nat) (cfg : CFG) (block : BasicBlock)
    (strategy : PanicStrategy) (result : StepResult) :
    evalTransfer sourceRecurse (scopedContext base source types) depth cfg block strategy result =
      evalTransfer targetRecurse (scopedContext base target types) depth cfg block strategy result := by
  cases result with
  | Ret values => rfl
  | Stuck => rfl
  | Continue next args => exact sameCFG types depth cfg next args strategy
  | CallReq id args =>
    rw [evalTransfer_call_eq, evalTransfer_call_eq]
    exact terminalCall_congr sourceRecurse targetRecurse base source target headers effects types depth block strategy id args
  | CallIndirectReq address signature args =>
    rw [evalTransfer_indirect_eq, evalTransfer_indirect_eq]
    exact terminalIndirect_congr sourceRecurse targetRecurse base source target headers effects types depth strategy address signature args
  | InvokeReq id args normal normalArgs unwind =>
    rw [evalTransfer_invoke_eq, evalTransfer_invoke_eq]
    exact terminalInvoke_congr sourceRecurse targetRecurse base source target headers effects sameCFG
      types depth cfg block strategy id args normal normalArgs unwind
  | InvokeIndirectReq address signature args normal normalArgs unwind =>
    rw [evalTransfer_invokeIndirect_eq, evalTransfer_invokeIndirect_eq]
    exact terminalInvokeIndirect_congr sourceRecurse targetRecurse base source target headers effects sameCFG
      types depth cfg block strategy address signature args normal normalArgs unwind
  | SeqMapReq id elems => rfl

/-- Public all-block consumer bridge. Caller declarations and caller CFGs
    do not enter a terminal Call's separately framed callee computation. -/
theorem evalTransfer_call_scoped_congr (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (depth : Nat)
    (sourceCFG targetCFG : CFG) (block : BasicBlock) (strategy : PanicStrategy)
    (id : FuncId) (args : List Value) :
    evalTransfer sourceRecurse (scopedContext base source sourceTypes) depth sourceCFG block strategy (.CallReq id args) =
      evalTransfer targetRecurse (scopedContext base target targetTypes) depth targetCFG block strategy (.CallReq id args) := by
  rw [evalTransfer_call_eq, evalTransfer_call_eq]
  apply Eq.trans _ (terminalCall_congr sourceRecurse targetRecurse base source target headers effects
    targetTypes depth block strategy id args)
  cases depth <;> simp only [terminalCall, EvalContext.lookupDirectCallee,
    scopedContext_forFunction, checkReturns_scoped_function,
    show (scopedContext base source sourceTypes).functions = source from rfl,
    show (scopedContext base source targetTypes).functions = source from rfl,
    show (scopedContext base source sourceTypes).declared = base.declared from rfl,
    show (scopedContext base source targetTypes).declared = base.declared from rfl]

/-- The indirect Call prelude retains its existing ABI checks. This bridge
    changes no lookup, error ordering, header or callee resource condition. -/
theorem evalTransfer_indirect_scoped_congr (sourceRecurse targetRecurse : Recurse) (base : EvalContext)
    (source target : FuncId → Option EvalFunction) (headers : HeaderAgreement source target)
    (effects : CalleeEffects sourceRecurse targetRecurse base source target)
    (sourceTypes targetTypes : Option LocalTypeTable) (depth : Nat)
    (sourceCFG targetCFG : CFG) (block : BasicBlock) (strategy : PanicStrategy)
    (address : Nat) (signature : FuncTyId) (args : List Value) :
    evalTransfer sourceRecurse (scopedContext base source sourceTypes) depth sourceCFG block strategy
      (.CallIndirectReq address signature args) =
      evalTransfer targetRecurse (scopedContext base target targetTypes) depth targetCFG block strategy
        (.CallIndirectReq address signature args) := by
  rw [evalTransfer_indirect_eq, evalTransfer_indirect_eq]
  apply Eq.trans _ (terminalIndirect_congr sourceRecurse targetRecurse base source target headers effects
    targetTypes depth strategy address signature args)
  cases depth <;> simp only [terminalIndirect, scoped_funcPtrs, scoped_funcTys,
    scopedContext_forFunction, checkReturns_scoped_function,
    show (scopedContext base source sourceTypes).functions = source from rfl,
    show (scopedContext base source targetTypes).functions = source from rfl]

/-- Expose the existing private normalized branch without duplicating its
    production extraction proof or changing any old declaration. -/
theorem evalTransfer_invoke_succ (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy) (id : FuncId) (args : List Value)
    (normal : BlockId) (normalArgs : List ValueId) (unwind : BlockId) :
    evalTransfer recurse ctx (depth + 1) cfg block strategy (.InvokeReq id args normal normalArgs unwind) = (do
      let callee ← ctx.lookupDirectCallee id
        "Invoke: callee is a bodyless declaration" "Invoke: undefined function"
      requireUntypedAbi callee.body.abi
      match checkCallArity args callee.body.paramTys with
      | .ok () => pure ()
      | .error message => Sem.throwTypeError ("Invoke: " ++ message)
      Sem.rejectPoisonValues args "Call arguments"
      invokeFrameWith strategy (checkReturns ctx callee.body.returnTys true false "Invoke: ")
        (recurse (ctx.forFunction callee) depth callee.cfg callee.entryBlock args strategy)
        (fun values => do
          ctx.bindCallResults block.terminator block.terminatorResultDests values
          let edgeArgs ← normalArgs.mapM Sem.lookupValue
          recurse ctx (depth + 1) cfg normal edgeArgs strategy)
        (fun exception => do
          semEnterPad cfg exception unwind
          recurse ctx (depth + 1) cfg unwind [] strategy)) := by
  rw [evalTransfer_invoke_eq]
  rfl

/-- RAW InvokeIndirect intentionally has no ABI prelude. It is the existing
    production branch verbatim, not the body-call or typed Invoke prelude. -/
theorem evalTransfer_invokeIndirect_succ (recurse : Recurse) (ctx : EvalContext) (depth : Nat)
    (cfg : CFG) (block : BasicBlock) (strategy : PanicStrategy)
    (address : Nat) (signature : FuncTyId) (args : List Value)
    (normal : BlockId) (normalArgs : List ValueId) (unwind : BlockId) :
    evalTransfer recurse ctx (depth + 1) cfg block strategy
      (.InvokeIndirectReq address signature args normal normalArgs unwind) = (do
      let id ← match ctx.funcPtrs address with
        | some id => pure id
        | none => Sem.throwUB "InvokeIndirect: invalid function pointer"
      let declaration ← match ctx.funcTys signature with
        | some declaration => pure declaration
        | none => Sem.throwTypeError "InvokeIndirect: undefined function type"
      let callee ← match ctx.functions id with
        | some callee => pure callee
        | none => Sem.throwTypeError "InvokeIndirect: undefined function"
      match checkIndirectSignature declaration callee.body with
      | .ok () => pure ()
      | .error message => Sem.throwTypeError ("InvokeIndirect: " ++ message)
      match checkCallArity args callee.body.paramTys with
      | .ok () => pure ()
      | .error message => Sem.throwTypeError ("InvokeIndirect: " ++ message)
      Sem.rejectPoisonValues args "InvokeIndirect arguments"
      invokeFrameWith strategy (checkReturns ctx callee.body.returnTys true false "InvokeIndirect: ")
        (recurse (ctx.forFunction callee) depth callee.cfg callee.entryBlock args strategy)
        (fun values => do
          ctx.bindCallResults block.terminator block.terminatorResultDests values
          let edgeArgs ← normalArgs.mapM Sem.lookupValue
          recurse ctx (depth + 1) cfg normal edgeArgs strategy)
        (fun exception => do
          semEnterPad cfg exception unwind
          recurse ctx (depth + 1) cfg unwind [] strategy)) := by
  rw [evalTransfer_invokeIndirect_eq]
  rfl

#trustIrAxioms lookupDirectCallee_bind_headers <= [propext, Classical.choice, Quot.sound]
#trustIrAxiomsExact terminalInvoke_congr == [propext, Classical.choice, Quot.sound]

end TrustIr.GenericCoro.Prefix
