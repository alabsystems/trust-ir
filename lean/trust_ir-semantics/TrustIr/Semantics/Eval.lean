-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Multi-step evaluation: stepBlock, stepN (fuel-based).
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 2

import TrustIr.Semantics.Step

namespace TrustIr

/-!
# Multi-Step Evaluation

## Basic Blocks

A basic block is a sequence of non-terminator instructions followed
by exactly one terminator. Block parameters receive values from
incoming branches (replaces phi nodes).

## Fuel-Based Termination

For Lean's termination checker, we use a fuel parameter for loops.
`stepN` takes `fuel : Nat` and decrements it on each block step.
`SemError.outOfFuel` is produced when fuel runs out.

For terminating programs with sufficient fuel, `outOfFuel` is never
produced. Proofs about total correctness prove sufficient fuel exists.
Proofs about partial correctness ignore the fuel parameter.
-/

/-- A basic block: parameters, body instructions, and terminator. -/
structure BasicBlock where
  params     : List (ValueId × Ty)     -- Block parameters
  body       : List Inst               -- Non-terminator instructions
  /-- Result destinations for `body`, positionally mirroring Rust
      `InstrNode.results`.  Older Lean fixtures that only rely on fresh
      sequential SSA ids leave this empty. -/
  bodyResultDests : List (List ValueId) := []
  terminator : Inst                    -- Terminator instruction
  /-- Result destinations for a value-producing TERMINATOR (`Inst.Invoke`:
      the callee's returns bind the invoke node's own results on the normal
      edge), mirroring Rust `InstrNode.results`. Empty for ordinary
      terminators. -/
  terminatorResultDests : List ValueId := []
  deriving Repr

/-- A control flow graph: mapping from BlockId to BasicBlock. -/
def CFG := BlockId → Option BasicBlock

/-- Bind block parameters to incoming values. -/
def bindBlockParams (params : List (ValueId × Ty)) (args : List Value) : Sem Unit := do
  if params.length != args.length then
    Sem.throwTypeError s!"block parameter count mismatch: expected {params.length}, got {args.length}"
  else
    let s ← Sem.getState
    let locals' := (params.zip args).foldl
      (fun locals binding => locals.set binding.fst.fst binding.snd)
      s.locals
    let nextValueId' := params.foldl
      (fun next param => max next (param.fst.index + 1))
      s.nextValueId
    Sem.setState { s with locals := locals', nextValueId := nextValueId' }

/-- Pair body instructions with their call-site/result destinations.
    Missing destination rows default to `[]` so existing Lean blocks keep their
    historical fresh-result behavior. -/
def bodyInstsWithResultDests :
    List Inst → List (List ValueId) → List (Inst × List ValueId)
  | [], _ => []
  | inst :: insts, [] =>
      (inst, []) :: bodyInstsWithResultDests insts []
  | inst :: insts, dests :: restDests =>
      (inst, dests) :: bodyInstsWithResultDests insts restDests

/-- Bind returned values to explicit SSA destinations from the enclosing
    instruction node. -/
def bindResultDests (dests : List ValueId) (values : List Value) : Sem Unit := do
  if dests.length != values.length then
    Sem.throwTypeError
      s!"call result count mismatch: expected {dests.length}, got {values.length}"
  else
    let s ← Sem.getState
    let locals' := (dests.zip values).foldl
      (fun locals binding => locals.set binding.fst binding.snd)
      s.locals
    let nextValueId' := dests.foldl
      (fun next dest => max next (dest.index + 1))
      s.nextValueId
    Sem.setState { s with locals := locals', nextValueId := nextValueId' }

/-- Bind an ordinary single-result body instruction to an explicit result
    destination when one is supplied. -/
def bindInstrResultDests : InstrResult → List ValueId → Sem Unit
  | .value none, [] => pure ()
  | .value none, _ :: _ =>
      Sem.throwTypeError "instruction result count mismatch"
  | .value (some _), [] => pure ()
  | .value (some result), dest :: [] => do
      let value ← Sem.lookupValue result
      bindResultDests [dest] [value]
  | .value (some _), _ :: _ :: _ =>
      Sem.throwTypeError "instruction result count mismatch"
  | .terminator _, _ =>
      Sem.throwTypeError "body instruction produced a terminator"

/-- Step through a single basic block.
    Execute all body instructions, then the terminator.
    Returns the step result (Continue/Ret/Stuck). -/
def stepBlock (block : BasicBlock) (args : List Value) : Sem StepResult := do
  -- Bind block parameters
  bindBlockParams block.params args
  -- Execute body instructions
  for inst in block.body do
    let instResult ← stepInst inst
    match instResult with
    | .value _ => pure ()
    | .terminator (.CallReq _ _) =>
      Sem.throwUnsupported .interproceduralCall
        "stepBlock: inter-procedural call in block body requires function table context"
    | .terminator (.CallIndirectReq _ _ _) =>
      Sem.throwUnsupported .interproceduralIndirectCall
        "stepBlock: inter-procedural indirect call in block body requires function table context"
    | .terminator (.SeqMapReq _ _) =>
      Sem.throwUnsupported .interproceduralCall
        "stepBlock: SeqMap element application in block body requires function table context"
    | .terminator _ =>
      Sem.throwTypeError "body instruction produced a terminator"
  -- Execute terminator
  let result ← stepInst block.terminator
  match result with
  | .terminator sr => pure sr
  | .value _       => Sem.throwTypeError "basic block does not end with a terminator"

/-- Multi-step evaluation with fuel-based termination.
    Executes blocks until Return, Stuck, or fuel exhaustion.

    `fuel` ensures termination for Lean's kernel. For terminating
    programs, sufficient fuel always exists. -/
def stepN (fuel : Nat) (cfg : CFG) (pc : BlockId) (args : List Value)
    : Sem (List Value) := do
  match fuel with
  | 0 => throw SemError.outOfFuel
  | fuel + 1 =>
    match cfg pc with
    | none => Sem.throwTypeError s!"undefined block: {repr pc}"
    | some block => do
      let result ← stepBlock block args
      match result with
      | .Ret values     => pure values
      | .Stuck          => Sem.throwUB "reached unreachable"
      | .Continue nextPc nextArgs => stepN fuel cfg nextPc nextArgs
      -- Call requests: the evaluator would need function tables to
      -- dispatch these. For now, signal that inter-procedural
      -- evaluation is not yet supported at this level.
      | .CallReq _ _ =>
        Sem.throwUnsupported .interproceduralCall
          "stepN: inter-procedural call requires function table context"
      | .CallIndirectReq _ _ _ =>
        Sem.throwUnsupported .interproceduralIndirectCall
          "stepN: inter-procedural indirect call requires function table context"
      | .InvokeReq _ _ _ _ _ =>
        Sem.throwUnsupported .interproceduralCall
          "stepN: invoke requires function table context"
      | .SeqMapReq _ _ =>
        Sem.throwUnsupported .interproceduralCall
          "stepN: SeqMap element application requires function table context"

/-- Evaluate a function from its entry block.
    Convenience wrapper around stepN with a default fuel limit. -/
def evalFunction (cfg : CFG) (entryBlock : BlockId) (args : List Value)
    (fuel : Nat := 10000) : Sem (List Value) :=
  stepN fuel cfg entryBlock args

/-!
## Contextual Interprocedural Evaluation

`stepN` is the historical single-function evaluator and intentionally keeps
its fail-closed behavior for calls.  `stepNWithContext` is the executable
interprocedural entry point: it carries function and function-pointer tables,
sets up a fresh local frame for callees, restores the caller frame on return,
and bounds calls by both block fuel and call depth.
-/

/-- Executable function body carried by an evaluator context. -/
structure EvalFunction where
  body       : FuncBody
  cfg        : CFG
  entryBlock : BlockId

/-- A module-level global's definition (type + optional initializer), carried by
    the evaluator context so `GlobalAddr` can reserve the global's TRUE byte size
    and write its initializer with full storage fidelity. Mirrors Rust `Global`. -/
structure GlobalDef where
  ty          : Ty
  initializer : Option Constant

/-- GlobalId -> definition lookup, mirroring `Module.globals`. -/
def GlobalsTable := GlobalId → Option GlobalDef

/-- Evaluator context for interprocedural execution. -/
structure EvalContext where
  functions    : FuncId -> Option EvalFunction
  funcPtrs     : FuncPtrTable
  funcTys      : FuncTyTable
  maxCallDepth : Nat
  /-- Module globals, enabling full-fidelity `GlobalAddr` (real size + initializer)
      under `stepNWithContext`. The bare `stepInst` keeps the honest size-1
      partial when no module context is available. -/
  globalsTable : GlobalsTable

namespace EvalContext

/-- Empty context used by tests that want fail-closed call behavior. -/
def empty : EvalContext :=
  { functions := fun _ => none
    funcPtrs := fun _ => none
    funcTys := fun _ => none
    maxCallDepth := 0
    globalsTable := fun _ => none }

end EvalContext

/-- Check that a returned value list matches the declared result arity. -/
def checkReturnArity (values : List Value) (returnTys : List Ty) :
    Except String Unit :=
  if values.length == returnTys.length then .ok ()
  else .error "return arity mismatch"

/-- Check that an indirect-call signature denotes the resolved callee. -/
def checkIndirectSignature (sig : FuncTyDef) (body : FuncBody) :
    Except String Unit :=
  if sig.params == body.paramTys && sig.returns == body.returnTys && !sig.isVararg then
    .ok ()
  else
    .error "indirect call signature mismatch"

/-- Convert a constant to its runtime value at the global's declared type,
    matching the `Const` instruction's width refinement (Step.lean `semConst`):
    integer constants take the type's bit width; other shapes use the default. -/
def valueOfConstAtTy (ty : Ty) (c : Constant) : Value :=
  match c with
  | .int i =>
    match ty.bitWidth with
    | some w => Value.int w i
    | none => Value.int 64 i
  | other => Value.ofConstant other

/-- Full-fidelity `GlobalAddr`: materialize a pointer to a module global with its
    TRUE byte size and initializer content. The first address-of a `GlobalId`
    reserves `def.ty.byteSize` bytes from the allocator, writes the encoded
    initializer (if present) OR zero-fills the storage (BSS/.tbss loader
    semantics) when there is no initializer, and caches the address; a later
    address-of returns the cached address — cache lookup happens FIRST, so the
    existing `semGlobalAddr_cache_hit` aliasing reasoning carries over to the
    cached branch. Faithful to the Rust reference interpreter's `global_pointer`
    (crates/trust-ir/src/interpret.rs:1216-1245; BSS zero-fill, commit 2b3954e).

    PARTIAL (honest, NOT faked): an initializer whose value has no byte encoding
    (`encodeValue` returns none — aggregate/sequence/set/record/closure) is
    rejected with a structured `unsupported` error rather than silently
    mis-encoded. Byte-layout for those shapes is documented follow-up. -/
def semGlobalAddrWithCtx (globalsTable : GlobalsTable) (global : GlobalId) :
    Sem ValueId := do
  let s ← Sem.getState
  match s.lookupGlobal global with
  | some addr => Sem.bindFresh (.ptr addr)
  | none =>
    let gdef ← match globalsTable global with
      | some d => pure d
      | none => Sem.throwTypeError "GlobalAddr: global not in module table"
    let byteSize ← match gdef.ty.byteSize with
      | some n => pure n
      | none => Sem.throwTypeError "GlobalAddr: global type has no byte size"
    let (baseAddr, mem') := s.memory.alloc byteSize .rustHeap
    let allocId := AllocId.mk s.memory.nextAllocId
    let perms' := s.permissions.set allocId .owned
    let mem'' ← match gdef.initializer with
      | none =>
        -- BSS / .tbss loader semantics: a global with NO initializer is
        -- zero-filled at load time, so a Load through its pointer reads a
        -- DEFINED zero (not uninitialized / poison). Mirrors the Rust
        -- reference interpreter (interpret.rs commit 2b3954e).
        pure (mem'.writeBytes baseAddr (List.replicate byteSize 0))
      | some initC =>
        match encodeValue (valueOfConstAtTy gdef.ty initC) with
        | some bytes => pure (mem'.writeBytes baseAddr bytes)
        | none =>
          Sem.throwUnsupported .vectorShape
            "GlobalAddr: initializer value has no byte encoding (aggregate/record/etc.)"
    Sem.setState
      { s with
        memory := mem''
        permissions := perms'
        globals := (global, baseAddr) :: s.globals }
    Sem.bindFresh (.ptr baseAddr)

/-- Dispatch a body instruction WITH module context: `GlobalAddr` uses the
    full-fidelity `semGlobalAddrWithCtx`; every other instruction delegates to the
    bare `stepInst` (whose `GlobalAddr` arm is the honest size-1 partial). -/
def stepInstWithContext (globalsTable : GlobalsTable) (inst : Inst) :
    Sem InstrResult := do
  match inst with
  | .GlobalAddr global =>
    let vid ← semGlobalAddrWithCtx globalsTable global
    pure (.value (some vid))
  | _ => stepInst inst

-- The heartbeat bump covers the `SeqMap` element-application arm below: the
-- per-element runner (alloc → write → call → read-back inside a `for`) makes
-- `stepNWithContext` one large elaborated definition. (Raised 1.6M → 3.2M at
-- v25: the four B1 Ty ctors — Isize/Usize/Char/Error — enlarge every Ty
-- match this definition elaborates through.)
set_option maxHeartbeats 3200000 in
/-- Multi-step evaluation with an interprocedural context.  Calls are executed
    either as tail call-transfer terminators or as body instructions with
    explicit result destinations mirroring Rust `InstrNode.results`. -/
def stepNWithContext (ctx : EvalContext) (fuel : Nat) (callDepth : Nat)
    (cfg : CFG) (pc : BlockId) (args : List Value) : Sem (List Value) := do
  match fuel with
  | 0 => throw SemError.outOfFuel
  | fuel + 1 =>
    match cfg pc with
    | none => Sem.throwTypeError s!"undefined block: {repr pc}"
    | some block => do
      bindBlockParams block.params args
      for bodyInst in bodyInstsWithResultDests block.body block.bodyResultDests do
        let inst := bodyInst.fst
        let resultDests := bodyInst.snd
        match inst with
        | .Call calleeId argIds => do
          let callArgs ← argIds.mapM Sem.lookupValue
          match callDepth with
          | 0 => throw SemError.outOfFuel
          | callDepth + 1 => do
            let callee ← match ctx.functions calleeId with
              | some f => pure f
              | none => Sem.throwTypeError "Call: undefined function"
            match checkCallArity callArgs callee.body.paramTys with
            | .ok () => pure ()
            | .error msg => Sem.throwTypeError ("Call: " ++ msg)
            let callerState ← Sem.getState
            let frame := saveFrame callerState none
            Sem.setState
              { callerState with locals := ValueMap.empty, nextValueId := 0 }
            let retVals ← stepNWithContext ctx fuel callDepth
              callee.cfg callee.entryBlock callArgs
            match checkReturnArity retVals callee.body.returnTys with
            | .ok () => pure ()
            | .error msg => Sem.throwTypeError ("Call: " ++ msg)
            let calleeState ← Sem.getState
            Sem.setState (restoreFrame calleeState frame [])
            bindResultDests resultDests retVals
        | .CallIndirect calleeValId sig argIds => do
          let calleeVal ← Sem.lookupValue calleeValId
          let addr ← match calleeVal with
            | .ptr a   => pure a
            | .nullPtr => Sem.throwUB "CallIndirect: null function pointer"
            | _        => Sem.throwTypeError "CallIndirect: callee is not a pointer"
          let callArgs ← argIds.mapM Sem.lookupValue
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
            match checkIndirectSignature sigDef callee.body with
            | .ok () => pure ()
            | .error msg => Sem.throwTypeError ("CallIndirect: " ++ msg)
            match checkCallArity callArgs callee.body.paramTys with
            | .ok () => pure ()
            | .error msg => Sem.throwTypeError ("CallIndirect: " ++ msg)
            let callerState ← Sem.getState
            let frame := saveFrame callerState none
            Sem.setState
              { callerState with locals := ValueMap.empty, nextValueId := 0 }
            let retVals ← stepNWithContext ctx fuel callDepth
              callee.cfg callee.entryBlock callArgs
            match checkReturnArity retVals callee.body.returnTys with
            | .ok () => pure ()
            | .error msg => Sem.throwTypeError ("CallIndirect: " ++ msg)
            let calleeState ← Sem.getState
            Sem.setState (restoreFrame calleeState frame [])
            bindResultDests resultDests retVals
        | _ => do
          let instResult ← stepInstWithContext ctx.globalsTable inst
          match instResult with
          | .value _ => bindInstrResultDests instResult resultDests
          | .terminator (.SeqMapReq fwdId elems) => do
            -- SeqMap element application (give-back loop instruction):
            -- apply the element function `fwd : fn(&mut elem)` to every
            -- element via the standard call machinery. ONE call-depth level
            -- bounds the WHOLE map — the per-element calls are sequential,
            -- so depth bounds nesting, not sequence length (do not burn
            -- depth per element). Each element round-trips through a fresh
            -- per-element memory cell: alloc → write element → call
            -- fwd(&mut cell) → read the mutated element back. Executable
            -- subset boundary (honest, fail-closed): elements must have a
            -- byte encoding (`encodeValue`) at the pointee type — scalar
            -- element types; aggregate elements are a documented follow-up.
            match callDepth with
            | 0 => throw SemError.outOfFuel
            | callDepth + 1 => do
              let callee ← match ctx.functions fwdId with
                | some f => pure f
                | none => Sem.throwTypeError "SeqMap: undefined element function"
              -- The element function must be the single-&mut form
              -- `fn(&mut elem)` (no returns) — its Aeneas forward view is
              -- elem -> elem.
              let elemTy ← match callee.body.paramTys, callee.body.returnTys with
                | [Ty.RefMut e], [] => pure e
                | _, _ =>
                    Sem.throwTypeError "SeqMap: element function must have signature fn(&mut elem)"
              let byteSize ← match elemTy.byteSize with
                | some n => pure n
                | none => Sem.throwTypeError "SeqMap: element type has no byte size"
              let mut mapped : List Value := []
              for elem in elems do
                -- Type guard (fail-closed, mirrors interpret.rs `elem.ty !=
                -- elem_ty`): the element VALUE must inhabit the element
                -- function's pointee TYPE — same-byte-width cross-type
                -- elements (e.g. Bool vs `&mut i8`) are a type error, never
                -- a silent reinterpret. Float elements are a structured
                -- unsupported until `encodeValue` gets a real IEEE-754 byte
                -- codec (the current placeholder would silently zero them —
                -- interpret.rs computes real float maps, so this is a
                -- documented executable-subset boundary, not agreement).
                let typeOk : Bool :=
                  match elemTy, elem with
                  | .Bool, .bool _ => true
                  | t, .int w _ => t.isInteger && t.bitWidth == some w
                  | _, _ => false
                if elemTy.isFloat then
                  Sem.throwUnsupported .vectorShape
                    "SeqMap: float elements need the IEEE-754 byte codec (placeholder encodeValue would zero them)"
                if !typeOk then
                  Sem.throwTypeError "SeqMap: element does not match the element function's pointee type"
                let bytes ← match encodeValue elem with
                  | some bs => pure bs
                  | none =>
                      Sem.throwTypeError "SeqMap: element value has no byte encoding"
                if bytes.length != byteSize then
                  Sem.throwTypeError "SeqMap: element does not match the element function's pointee type"
                -- Allocate the per-element cell and write the element into it.
                let s ← Sem.getState
                let (cellAddr, mem') := s.memory.alloc byteSize .rustStack
                let allocId := AllocId.mk s.memory.nextAllocId
                let perms' := s.permissions.set allocId .owned
                Sem.setState
                  { s with
                    memory := mem'.writeBytes cellAddr bytes
                    permissions := perms' }
                -- Call fwd(&mut cell) with the standard frame discipline.
                let callerState ← Sem.getState
                let frame := saveFrame callerState none
                Sem.setState
                  { callerState with locals := ValueMap.empty, nextValueId := 0 }
                let retVals ← stepNWithContext ctx fuel callDepth
                  callee.cfg callee.entryBlock [.ptr cellAddr]
                match checkReturnArity retVals callee.body.returnTys with
                | .ok () => pure ()
                | .error msg => Sem.throwTypeError ("SeqMap: " ++ msg)
                let calleeState ← Sem.getState
                Sem.setState (restoreFrame calleeState frame [])
                -- Read the mutated element back out of the cell.
                let s' ← Sem.getState
                let outBytes ← match s'.memory.readBytes cellAddr byteSize with
                  | some bs => pure bs
                  | none => Sem.throwUB "SeqMap: element cell read failed"
                let newElem ← match decodeValue elemTy outBytes with
                  | some v => pure v
                  | none =>
                      Sem.throwTypeError "SeqMap: element cell does not decode at the element type"
                mapped := mapped ++ [newElem]
              bindResultDests resultDests [Value.sequence mapped]
          | .terminator _ =>
            Sem.throwTypeError "body instruction produced a terminator"
      let termResult ← stepInst block.terminator
      let result ← match termResult with
        | .terminator sr => pure sr
        | .value _ => Sem.throwTypeError "basic block does not end with a terminator"
      match result with
      | .Ret values => pure values
      | .Stuck => Sem.throwUB "reached unreachable"
      | .Continue nextPc nextArgs =>
        stepNWithContext ctx fuel callDepth cfg nextPc nextArgs
      | .CallReq calleeId callArgs =>
        match callDepth with
        | 0 => throw SemError.outOfFuel
        | callDepth + 1 => do
          let callee ← match ctx.functions calleeId with
            | some f => pure f
            | none => Sem.throwTypeError "Call: undefined function"
          match checkCallArity callArgs callee.body.paramTys with
          | .ok () => pure ()
          | .error msg => Sem.throwTypeError ("Call: " ++ msg)
          let callerState ← Sem.getState
          let frame := saveFrame callerState none
          Sem.setState
            { callerState with locals := ValueMap.empty, nextValueId := 0 }
          let retVals ← stepNWithContext ctx fuel callDepth
            callee.cfg callee.entryBlock callArgs
          match checkReturnArity retVals callee.body.returnTys with
          | .ok () => pure ()
          | .error msg => Sem.throwTypeError ("Call: " ++ msg)
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
          match checkIndirectSignature sigDef callee.body with
          | .ok () => pure ()
          | .error msg => Sem.throwTypeError ("CallIndirect: " ++ msg)
          match checkCallArity callArgs callee.body.paramTys with
          | .ok () => pure ()
          | .error msg => Sem.throwTypeError ("CallIndirect: " ++ msg)
          let callerState ← Sem.getState
          let frame := saveFrame callerState none
          Sem.setState
            { callerState with locals := ValueMap.empty, nextValueId := 0 }
          let retVals ← stepNWithContext ctx fuel callDepth
            callee.cfg callee.entryBlock callArgs
          match checkReturnArity retVals callee.body.returnTys with
          | .ok () => pure ()
          | .error msg => Sem.throwTypeError ("CallIndirect: " ++ msg)
          let calleeState ← Sem.getState
          Sem.setState (restoreFrame calleeState frame [])
          pure retVals
      | .InvokeReq calleeId callArgs normalDest normalArgIds _unwindDest =>
        -- Non-throwing executable model (mirrors interpret.rs Inst::Invoke):
        -- run the call exactly like CallReq, bind the callee's returns to the
        -- invoke node's result destinations, THEN evaluate the normal-edge
        -- arguments (they may reference those results) and take the normal
        -- edge. The unwind destination is never taken under evaluation.
        match callDepth with
        | 0 => throw SemError.outOfFuel
        | innerDepth + 1 => do
          let callee ← match ctx.functions calleeId with
            | some f => pure f
            | none => Sem.throwTypeError "Invoke: undefined function"
          match checkCallArity callArgs callee.body.paramTys with
          | .ok () => pure ()
          | .error msg => Sem.throwTypeError ("Invoke: " ++ msg)
          let callerState ← Sem.getState
          let frame := saveFrame callerState none
          Sem.setState
            { callerState with locals := ValueMap.empty, nextValueId := 0 }
          let retVals ← stepNWithContext ctx fuel innerDepth
            callee.cfg callee.entryBlock callArgs
          match checkReturnArity retVals callee.body.returnTys with
          | .ok () => pure ()
          | .error msg => Sem.throwTypeError ("Invoke: " ++ msg)
          let calleeState ← Sem.getState
          Sem.setState (restoreFrame calleeState frame [])
          bindResultDests block.terminatorResultDests retVals
          let edgeArgs ← normalArgIds.mapM Sem.lookupValue
          -- The normal edge continues the CALLER: depth bounds NESTING only
          -- (mirrors interpret.rs, where the caller resumes at its own depth
          -- after Step::Jump), so the continuation runs at the UNdecremented
          -- depth — an Invoke must not permanently burn depth budget.
          stepNWithContext ctx fuel (innerDepth + 1) cfg normalDest edgeArgs
      | .SeqMapReq _ _ =>
        -- A SeqMap in terminator position is malformed IR (it is not a
        -- terminator; Rust-side validation rejects it). Fail closed.
        Sem.throwTypeError "SeqMap is not a terminator"

/-- Evaluate a function by FuncId through an interprocedural context. -/
def evalFunctionInContext (ctx : EvalContext) (entryFunc : FuncId)
    (args : List Value) (fuel : Nat := 10000) : Sem (List Value) := do
  let func ← match ctx.functions entryFunc with
    | some f => pure f
    | none => Sem.throwTypeError "evalFunctionInContext: undefined entry function"
  match checkCallArity args func.body.paramTys with
  | .ok () => pure ()
  | .error msg => Sem.throwTypeError ("evalFunctionInContext: " ++ msg)
  stepNWithContext ctx fuel ctx.maxCallDepth func.cfg func.entryBlock args

end TrustIr
