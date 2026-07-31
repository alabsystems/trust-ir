-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Instruction dispatch: stepInst routes each instruction to its semantics.

import TrustIr.Inst
import TrustIr.Semantics.Arith
import TrustIr.Semantics.Compare
import TrustIr.Semantics.Cast
import TrustIr.Semantics.Control
import TrustIr.Semantics.Memory
import TrustIr.Semantics.Borrow
import TrustIr.Semantics.ARC
import TrustIr.Semantics.Atomic
import TrustIr.Semantics.Aggregate
import TrustIr.Semantics.Call
import TrustIr.Semantics.Frame
import TrustIr.Semantics.Coroutine

namespace TrustIr

/-!
# Instruction Step

`stepInst` dispatches each instruction variant to its per-category
semantic function. This is the central routing function for the
TrustIr formalization.

For non-terminator instructions, `stepInst` returns the ValueId
of the result (if any) and `none` for the StepResult.
For terminator instructions, it returns `some StepResult`.

## Design note

This two-level dispatch (stepInst for individual instructions,
stepBlock for basic blocks) follows the design document's
recommendation for Phase 1 completeness.
-/

/-- Result of stepping a single instruction.
    Non-terminators produce an optional ValueId.
    Terminators produce a StepResult. -/
inductive InstrResult where
  | value      : Option ValueId → InstrResult   -- non-terminator
  | terminator : StepResult → InstrResult        -- terminator
  deriving Repr

/-- Lane-wise vector select. The mask must be a logical bool vector; physical
    integer masks remain a lowering artifact and are rejected here. -/
def semVectorSelectLanes
    : List Value → List Value → List Value → Except SemError (List Value)
  | [], [], [] => .ok []
  | .bool true :: maskRest, thenLane :: thenRest, _ :: elseRest => do
    let rest ← semVectorSelectLanes maskRest thenRest elseRest
    pure (thenLane :: rest)
  | .bool false :: maskRest, _ :: thenRest, elseLane :: elseRest => do
    let rest ← semVectorSelectLanes maskRest thenRest elseRest
    pure (elseLane :: rest)
  | _ :: _, [], _ => .error (.typeError "Vector Select: then lane count mismatch")
  | _ :: _, _, [] => .error (.typeError "Vector Select: else lane count mismatch")
  | [], _ :: _, _ => .error (.typeError "Vector Select: mask lane count mismatch")
  | [], _, _ :: _ => .error (.typeError "Vector Select: mask lane count mismatch")
  | _ :: _, _ :: _, _ :: _ => .error (.typeError "Vector Select: non-bool mask lane")

/-- Step a single TrustIr instruction.
    Routes to the appropriate per-category semantic function. -/
def stepInst (inst : Inst) : Sem InstrResult := do
  match inst with
  -- Arithmetic
  | .BinOp op ty lhs rhs => do
    let vid ← semBinOp op ty lhs rhs
    pure (.value (some vid))

  | .UnOp op ty operand => do
    let vid ← semUnOp op ty operand
    pure (.value (some vid))

  | .Overflow op ty lhs rhs => do
    let vid ← semOverflow op ty lhs rhs
    pure (.value (some vid))

  -- Comparison
  | .ICmp op ty lhs rhs => do
    let vid ← semICmpInst op ty lhs rhs
    pure (.value (some vid))

  | .FCmp op ty lhs rhs => do
    let vid ← semFCmpInst op ty lhs rhs
    pure (.value (some vid))

  -- Casts
  | .Cast op srcTy dstTy operand => do
    let vid ← semCast op srcTy dstTy operand
    pure (.value (some vid))

  -- Constants
  | .Const ty val => do
    -- For int constants we keep the bitWidth refinement from the Const
    -- instruction's declared Ty (the Value.ofConstant default is i64).
    -- For every other shape we delegate to Value.ofConstant so that
    -- aggregate / sequence / set / record / closure constants evaluate
    -- to their runtime denotation (issue #56 / #52).
    let v := match ty, val with
      | _, .int i => match ty.bitWidth with
        | some w => Value.int w i
        | none   => Value.int 64 i  -- fallback
      | .Vector _ elemTy, .vector cs =>
        match elemTy.bitWidth with
        | some w =>
          .vector (cs.map (fun c =>
            match c with
            | .int i => Value.int w i
            | other  => Value.ofConstant other))
        | none => Value.ofConstant (.vector cs)
      | _, c        => Value.ofConstant c
    let vid ← Sem.bindFresh v
    pure (.value (some vid))

  | .NullPtr => do
    let vid ← Sem.bindFresh .nullPtr
    pure (.value (some vid))

  | .Undef ty => do
    let vid ← Sem.bindFresh (.undef ty)
    pure (.value (some vid))

  -- Pseudo instructions
  | .Copy _ty operand => do
    let v ← Sem.lookupValue operand
    let vid ← Sem.bindFresh v
    pure (.value (some vid))

  | .Select ty cond thenVal elseVal => do
    -- Scalar Bool gates the whole value. A same-lane `<N x Bool>` mask selects
    -- lane-wise for the bounded executable vector subset.
    let condV ← Sem.lookupValue cond
    -- The condition is inspected; the arms are transported (either may itself
    -- be a poison value passed through unchanged), so only `cond` is gated.
    Sem.rejectPartial condV "Select"
    let chosen ← match condV with
      | .bool true  => Sem.lookupValue thenVal
      | .bool false => Sem.lookupValue elseVal
      | .vector mask =>
        match ty.executableVectorLanes? with
        | some lanes =>
          if mask.length != lanes then
            Sem.throwTypeError "Vector Select: mask lane count does not match type"
          else do
            let thenV ← Sem.lookupValue thenVal
            let elseV ← Sem.lookupValue elseVal
            match thenV, elseV with
            | .vector thenLanes, .vector elseLanes =>
              let thenOk := ty.executableVectorPayloadMatches thenLanes
              let elseOk := ty.executableVectorPayloadMatches elseLanes
              if thenOk && elseOk then
                match semVectorSelectLanes mask thenLanes elseLanes with
                | .ok result => pure (.vector result)
                | .error e   => throw e
              else
                Sem.throwTypeError "Vector Select: value lanes do not match vector type"
            | _, _ => Sem.throwTypeError "Vector Select: vector mask with non-vector values"
        | none =>
          Sem.throwUnsupported .vectorType
            s!"Vector Select: unsupported vector type {repr ty}"
      | _ => Sem.throwTypeError "Select: condition is not bool"
    let vid ← Sem.bindFresh chosen
    pure (.value (some vid))

  -- Proof instructions
  | .Assume _cond =>
    -- Assume: add to assumption set (no-op in execution semantics)
    pure (.value none)

  | .Assert cond => do
    -- Assert requires a Bool condition; anything else (including integers) is
    -- a type error, NOT a truthiness test. Matches the Rust reference
    -- interpreter (interpret.rs Inst::Assert: `as_bool` else TypeError) and
    -- validation (validate.rs: check_predicate_is_bool). A former int-accepting
    -- branch here ("nonzero passes") was a Lean-only relaxation; locked out by
    -- assert_int_condition_type_error_stable in ExecutableFixtures.lean.
    let condV ← Sem.lookupValue cond
    -- Inspecting a poison condition is UB (copy-propagates-poison use site).
    Sem.rejectPartial condV "Assert"
    match condV with
    | .bool true  => pure (.value none)
    | .bool false => Sem.throwPanic "assertion failed"
    | _           => Sem.throwTypeError "Assert: non-boolean condition"

  | .Unreachable =>
    pure (.terminator .Stuck)

  -- Control flow terminators
  | .Br target args => do
    let result ← semBr target args
    pure (.terminator result)

  | .CondBr cond thenTarget thenArgs elseTarget elseArgs => do
    let result ← semCondBr cond thenTarget thenArgs elseTarget elseArgs
    pure (.terminator result)

  | .Return values => do
    let result ← semReturn values
    pure (.terminator result)

  -- Memory (Phase 2)
  | .Load ty ptr volatile align => do
    -- A VOLATILE load keeps the strict all-initialized discipline
    -- (`strict := volatile`); a plain load participates in copy-propagates-
    -- poison. `align` is the declared alignment (checked by semLoad).
    let vid ← semLoad ty ptr volatile align
    pure (.value (some vid))

  | .Store ty ptr value volatile align => do
    -- A VOLATILE store keeps the strict discipline (a poison value may not be
    -- stored volatilely); a plain store transports a `.partial` image verbatim.
    -- `align` is the declared alignment (checked by semStore).
    semStore ty ptr value volatile align
    pure (.value none)

  | .Alloca ty count => do
    let vid ← semAlloca ty count
    pure (.value (some vid))

  | .HeapAlloc ty count origin => do
    let vid ← semHeapAlloc ty count origin
    pure (.value (some vid))

  | .GlobalAddr global => do
    let vid ← semGlobalAddr global
    pure (.value (some vid))

  | .GEP pointeeTy base indices _inbounds => do
    -- `_inbounds` is the no-wrap claim; the poison-on-OOB refinement is deferred
    -- (MemoryProps §"GEP in-bounds"). semGEP computes the address either way.
    let vid ← semGEP pointeeTy base indices
    pure (.value (some vid))

  | .PtrData ptrTy ptr => do
    let vid ← semPtrData ptrTy ptr
    pure (.value (some vid))

  | .PtrMetadata ptrTy metadataTy ptr => do
    let vid ← semPtrMetadata ptrTy metadataTy ptr
    pure (.value (some vid))

  | .PtrFromParts ptrTy metadataTy data metadata => do
    let vid ← semPtrFromParts ptrTy metadataTy data metadata
    pure (.value (some vid))

  -- Atomics (Phase 4)
  | .AtomicLoad ty ptr ordering => do
    let vid ← semAtomicLoad ty ptr ordering
    pure (.value (some vid))

  | .AtomicStore ty ptr value ordering => do
    semAtomicStore ty ptr value ordering
    pure (.value none)

  | .AtomicRMW op ty ptr value ordering => do
    let vid ← semAtomicRMW op ty ptr value ordering
    pure (.value (some vid))

  | .CmpXchg ty ptr expected desired success failure => do
    let vid ← semCmpXchg ty ptr expected desired success failure
    pure (.value (some vid))

  | .Fence ordering => do
    semFence ordering
    pure (.value none)

  -- Switch (Phase 4)
  | .Switch value default_ defaultArgs cases => do
    let result ← semSwitch value default_ defaultArgs cases
    pure (.terminator result)

  -- Calls (Phase 4): resolve arguments and produce a CallReq for
  -- the evaluator to handle frame push/pop.
  | .Call calleeId argIds => do
    let args ← argIds.mapM Sem.lookupValue
    pure (.terminator (.CallReq calleeId args))

  | .CallIndirect calleeValId sig argIds => do
    let calleeVal ← Sem.lookupValue calleeValId
    let addr ← match calleeVal with
      | .ptr a   => pure a
      | .nullPtr => Sem.throwUB "CallIndirect: null function pointer"
      | _        => Sem.throwTypeError "CallIndirect: callee is not a pointer"
    let args ← argIds.mapM Sem.lookupValue
    -- The evaluator resolves addr to a FuncId via the function pointer table
    -- and checks that the callee matches sig.
    pure (.terminator (.CallIndirectReq addr sig args))

  -- Sequence element-op map (give-back loop instruction). Applying the
  -- element function per element is INTERPROCEDURAL, so stepInst validates
  -- the operand and returns a SeqMapReq for the contextual evaluator
  -- (mirrors the Call/CallReq split). The bare single-function evaluators
  -- fail closed with a structured unsupported error.
  | .SeqMap _ty seq fwd => do
    let seqVal ← Sem.lookupValue seq
    match seqVal with
    | .sequence elems => pure (.terminator (.SeqMapReq fwd elems))
    | _ => Sem.throwTypeError "SeqMap: operand is not a sequence"

  -- Aggregates (Phase 4)
  | .ExtractField ty aggregate field => do
    let vid ← semExtractField ty aggregate field
    pure (.value (some vid))

  | .InsertField ty aggregate field value => do
    let vid ← semInsertField ty aggregate field value
    pure (.value (some vid))

  | .ExtractElement ty array index => do
    let vid ← semExtractElement ty array index
    pure (.value (some vid))

  | .InsertElement ty array index value => do
    let vid ← semInsertElement ty array index value
    pure (.value (some vid))

  -- Sequence element-op loops (give-back / Aeneas loopFwd)
  | .SeqMapAddK ty seq k => do
    let vid ← semSeqMapAddK ty seq k
    pure (.value (some vid))

  | .SeqMapNot ty seq => do
    let vid ← semSeqMapNot ty seq
    pure (.value (some vid))

  -- Borrow (Phase 3)
  | .Borrow ptr     => do
    let vid ← semBorrow ptr
    pure (.value (some vid))
  | .BorrowMut ptr  => do
    let vid ← semBorrowMut ptr
    pure (.value (some vid))
  | .EndBorrow ptr  => do
    semEndBorrow ptr
    pure (.value none)

  -- ARC (Phase 3)
  | .Retain ptr     => do
    semRetain ptr
    pure (.value none)
  | .Release ptr    => do
    semRelease ptr
    pure (.value none)
  | .IsUnique ptr   => do
    let vid ← semIsUnique ptr
    pure (.value (some vid))

  -- Binding frames (TrustIr#32): typed quantifier lowering.
  | .OpenFrame def_ => do
    let vid ← semOpenFrame def_
    pure (.value (some vid))
  | .BindSlot frame slot value => do
    let vid ← semBindSlot frame slot value
    pure (.value (some vid))
  | .LoadSlot frame slot ty => do
    let vid ← semLoadSlot frame slot ty
    pure (.value (some vid))
  | .CloseFrame frame => do
    semCloseFrame frame
    pure (.value none)

  -- Heap deallocation (TrustIr#54). Mirrors Rust Inst::Dealloc.
  | .Dealloc ptr => do
    semDealloc ptr
    pure (.value none)

  -- Coroutine suspend: store the resume state index into the frame, then
  -- return the yielded value (a terminator; the resumer sees a plain Ret).
  | .CoroSuspend frame stateSlot nextState value => do
    let result ← semCoroSuspend frame stateSlot nextState value
    pure (.terminator result)

  -- Exception handling. The executable model, like the reference
  -- interpreter (interpret.rs), models a NON-THROWING callee (panic=abort):
  -- an Invoke requests the call exactly like Call and the evaluator always
  -- takes the normal edge; the unwind machinery is structural fidelity.
  | .Invoke callee argIds normalDest normalArgs unwindDest => do
    let args ← argIds.mapM Sem.lookupValue
    pure (.terminator (.InvokeReq callee args normalDest normalArgs unwindDest))

  | .LandingPad _isCleanup _catchTypeIndices => do
    -- Only reachable via an unwind edge, which evaluation never takes. If
    -- reached directly it binds a null exception pointer and zero type
    -- selector — unobservable in well-formed programs, but total, mirroring
    -- interpret.rs. Packed as an aggregate pair (Overflow convention).
    let vid ← Sem.bindFresh (.aggregate [.nullPtr, .int 32 0])
    pure (.value (some vid))

  | .Resume _exn =>
    -- Re-raising to the host unwinder is outside the executable model: a
    -- resume is only reachable after an unwind edge was taken, which never
    -- happens under evaluation. Structured unsupported, not silent success.
    Sem.throwUnsupported .hostUnwind
      "Resume: the executable model does not model in-flight host exceptions"

  -- Dialect op (TrustIr#54). Core TrustIr semantics do not interpret dialect
  -- ops: dialect-aware passes must lower them to core instructions
  -- before evaluation. Running stepInst on a DialectOp is a structured
  -- unsupported-subset error
  -- (the lowering-correctness obligation in TrustIr.Semantics.Dialect is
  -- what producer repos discharge). The op payload is preserved in the
  -- error message for diagnosability.
  | .DialectOp op =>
    Sem.throwUnsupported .dialectOp
      ("stepInst: DialectOp " ++ op.qualifiedName
        ++ " must be lowered to core TrustIr instructions before evaluation")

end TrustIr
