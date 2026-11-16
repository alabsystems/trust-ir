-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Semantics.Eval

namespace TrustIr.GenericCoro.Prefix

/-- The actual smaller-fuel recursive evaluator, abstracted only so the
    induction can state its hypotheses at every direct/indirect call site. -/
abbrev Recurse := EvalContext → Nat → CFG → BlockId → List Value → PanicStrategy → Sem (List Value)

/-- One production body node, with the recursive evaluator exposed. The
    layer anchoring equation checks every branch and its exact error order. -/
def evalBodyStep (recurse : Recurse) (ctx : EvalContext) (callDepth : Nat)
    (strat : PanicStrategy) (bodyInst : Inst × List ValueId) : Sem (ForInStep Unit) := do
  let inst := bodyInst.fst
  let resultDests := bodyInst.snd
  match inst with
  | .Call calleeId argIds => do
    let callArgs ← argIds.mapM Sem.lookupValue
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
      let calleeState ← Sem.getState
      Sem.setState (restoreFrame calleeState frame [])
      ctx.bindCallResults inst resultDests retVals
  | .CallIndirect calleeValId sig argIds conv => do
    let calleeVal ← Sem.lookupValue calleeValId
    let _ ← Sem.fromMemoryExcept (checkFunctionItemCalleeType ctx calleeValId calleeVal)
    -- Validate a pointer before argument lookup as before. A nominal
    -- closure is resolved only after the same call-depth boundary.
    let addr ← match calleeVal with
      | .ptr a _ => pure a
      | .fnDef _ _ => pure 0
      | .fnItem _ => pure 0
      | .typedClosure _ _ _ => pure 0
      | .nullPtr => Sem.throwTypeError "CallIndirect: null function pointer"
      | _ => Sem.throwTypeError "CallIndirect: callee is not a pointer or typed closure"
    let args ← match calleeVal with
      | .fnItem _ => pure []
      | _ => argIds.mapM Sem.lookupValue
    match callDepth with
    | 0 => throw SemError.outOfFuel
    | callDepth + 1 => do
      let (calleeId, callArgs) ← match calleeVal with
        | .fnItem target =>
          match functionItemCall ctx target sig conv with
          | .ok fn => do pure (fn, ← argIds.mapM Sem.lookupValue)
          | .error e => throw e
        | .fnDef held target =>
          match functionCallWithConvention ctx held target sig conv with
          | .ok fn => pure (fn, args)
          | .error e => throw e
        | .typedClosure cid fn captures =>
          match closureCall ctx cid fn captures sig args conv with
          | .ok call => pure call
          | .error e => throw e
        | _ => do
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
          pure (calleeId, args)
      let callee ← match ctx.functions calleeId with
        | some f => pure f
        | none =>
          match calleeVal with
          | .fnItem _ => Sem.fromMemoryExcept (resolveFunctionItemBody ctx calleeId)
          | _ => Sem.throwTypeError "CallIndirect: undefined function"
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
      if let .typedClosure _ _ _ := calleeVal then
        for (t, v) in callee.body.returnTys.zip retVals do
          match checkClosureValue ctx t v with
          | .ok () => pure ()
          | .error e => throw e
      let calleeState ← Sem.getState
      Sem.setState (restoreFrame calleeState frame [])
      ctx.bindCallResults inst resultDests retVals
  -- R1 (amendment D, Part 2): a failed check raises under `.unwind`.
  -- An `Assert` never yields a terminator, so binding its (empty)
  -- result is exactly the generic arm below.
  | .Assert _ _ _ => do
    let instResult ← raiseIfUnwind strat (stepInstWithContext ctx inst) ctx.byteModel
    ctx.bindInstructionResults inst instResult resultDests
  -- R5: a landing pad binds the exception in hand under `.unwind`.
  | .LandingPad isCleanup clauses =>
    semLandingPadWith strat ctx (.LandingPad isCleanup clauses) resultDests
  | _ => do
    let instResult ← stepInstWithContext ctx inst
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

def evalBody (recurse : Recurse) (ctx : EvalContext) (callDepth : Nat)
    (strat : PanicStrategy) (rows : List (Inst × List ValueId)) : Sem Unit :=
  forIn rows () (fun row _ => evalBodyStep recurse ctx callDepth strat row)

/-- One complete production block. Fuel is represented by the supplied
    smaller-fuel callback; the public equation retains the actual resource
    indices and does not assume any callback or block succeeds. -/
def evalLayer (recurse : Recurse) (ctx : EvalContext) (callDepth : Nat)
    (cfg : CFG) (pc : BlockId) (args : List Value) (strat : PanicStrategy) : Sem (List Value) := do
  match cfg pc with
  | none => Sem.throwTypeError s!"undefined block: {repr pc}"
  | some blk => do
    -- Amendment D (§20 rule 3): every drop of the block is resolved
    -- through the context's drop-glue table BEFORE dispatch, so a resolved
    -- drop runs the `Call` / `Invoke` rules below verbatim, and an
    -- unresolved one reaches the bare `stepInst`, which refuses it.
    let block := ctx.resolveBlock blk
    let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx (block.params.map (·.snd)) args)
    bindBlockParamsChecked block.params args
    evalBody recurse ctx callDepth strat (bodyInstsWithResultDests block.body block.bodyResultDests)
    -- Under `.unwind` a failing `AssertInvoke` enters its pad and `Resume`
    -- re-raises (`stepTermUnwind`); under `.abort` the bare step.
    let termResult ← stepTermWithContext ctx callDepth cfg block.terminator strat
    let result ← match termResult with
      | .terminator sr => pure sr
      | .value _ => Sem.throwTypeError "basic block does not end with a terminator"
      | .values _ => Sem.throwTypeError "basic block does not end with a terminator"
    match result with
    | .Ret values =>
      if let some expected := ctx.functionReturnTypes then
        let _ ← Sem.fromMemoryExcept (checkFunctionItemValues ctx expected values)
        pure values
      else pure values
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

theorem stepNWithContext_succ_layer (ctx : EvalContext) (fuel depth : Nat)
    (cfg : CFG) (pc : BlockId) (args : List Value) (strat : PanicStrategy) :
    stepNWithContext ctx (fuel + 1) depth cfg pc args strat =
      evalLayer (fun context depth cfg pc args strat =>
        stepNWithContext context fuel depth cfg pc args strat) ctx depth cfg pc args strat := by rfl

end TrustIr.GenericCoro.Prefix
