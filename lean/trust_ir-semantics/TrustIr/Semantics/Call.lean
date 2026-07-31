-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Function call semantics: Call, CallIndirect, Switch.
-- Phase 4 of the formalization roadmap.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 6 Phase 4
--
-- Function calls push a new stack frame, bind arguments to parameters,
-- and transfer control to the callee. Return pops the frame and
-- propagates the return value.

import TrustIr.Inst
import TrustIr.Semantics.Monad
import TrustIr.Semantics.Control

namespace TrustIr

/-!
# Function Call Semantics

## Overview

Function calls in TrustIr follow a standard call/return discipline:

1. **Call**: lookup callee, validate argument types, produce resolved
   argument values for the evaluator to push a new frame.

2. **CallIndirect**: resolve a function pointer value to a FuncId
   via a function pointer table, then proceed as Call.

3. **Switch**: multi-way branch matching an integer value against
   a list of cases.

## Stack Frame Model

Each call creates a `StackFrame` that captures the caller's local
value map so it can be restored on return.  The actual frame
push/pop is performed by the evaluator (`Eval.lean`), not by the
instruction semantics.  The semantics here produce the information
the evaluator needs.

## Design Decisions

* Call semantics are kept independent of `Eval.lean` to avoid
  circular imports.

* Switch is grouped with calls because both are Phase 4 control
  flow extensions.

Reference: Ho & Protzenko, "Aeneas: Rust verification by functional
           translation", ICFP 2022 -- Section 4, call semantics.
-/

-- =================================================================
-- Stack frame (for call/return discipline)
-- =================================================================

/-- A stack frame captures the caller's context so it can be restored
    after the callee returns.

    - `locals`: the caller's SSA value map at the call site
    - `returnDest`: the SSA value id where the return value is bound
    - `savedNextValueId`: the caller's nextValueId counter
    -/
structure StackFrame where
  locals           : ValueMap
  returnDest       : Option ValueId
  savedNextValueId : Nat
  deriving Repr

/-- The call stack: a list of stack frames.
    The head is the most recent (deepest) caller. -/
def CallStack := List StackFrame

/-- Empty call stack (top-level). -/
def CallStack.empty : CallStack := []

-- =================================================================
-- Function metadata (for call validation)
-- =================================================================

/-- Function body metadata -- what the call site needs to validate
    a call.  The actual CFG execution is in `Eval.lean`. -/
structure FuncBody where
  paramTys  : List Ty
  returnTys : List Ty
  deriving Repr

/-- Function table: maps FuncId to function metadata. -/
def FuncTable := FuncId -> Option FuncBody

/-- Function type table: maps FuncTyId to FuncTyDef for indirect
    call signature validation. -/
def FuncTyTable := FuncTyId -> Option FuncTyDef

/-- Function pointer table: maps a pointer address (from a function
    pointer value) to the FuncId it points to. -/
def FuncPtrTable := Nat -> Option FuncId

-- =================================================================
-- Call argument validation (pure helpers)
-- =================================================================

/-- Check that argument values match the expected parameter types.
    Returns unit on success, or an error message on mismatch.

    In Phase 4 we check arity only; full type checking is future work
    (requires resolving aggregate types from the module context). -/
def checkCallArity (args : List Value) (paramTys : List Ty) : Except String Unit :=
  if args.length == paramTys.length then .ok ()
  else .error "call arity mismatch"

-- =================================================================
-- Save / restore frame helpers
-- =================================================================

/-- Save the current MachineState into a StackFrame. -/
def saveFrame (s : MachineState) (dest : Option ValueId) : StackFrame :=
  { locals           := s.locals
  , returnDest       := dest
  , savedNextValueId := s.nextValueId }

/-- Restore the caller's context from a StackFrame, binding the
    return value to the returnDest if present. -/
def restoreFrame (s : MachineState) (frame : StackFrame) (retVals : List Value)
    : MachineState :=
  let s' := { s with
    locals      := frame.locals
    nextValueId := frame.savedNextValueId }
  match frame.returnDest, retVals with
  | some dest, [v] =>
    { s' with locals := s'.locals.set dest v }
  | _, _ => s'

-- =================================================================
-- Call semantics
-- =================================================================

/-- Evaluate a Call instruction.
    Looks up the callee in the function table, validates argument arity,
    and returns the resolved argument values plus the callee metadata.

    The evaluator uses the returned argument values to set up the
    callee frame.

    Mirrors Rust `Inst::Call`. -/
def semCall (funcTable : FuncTable) (calleeId : FuncId) (argIds : List ValueId)
    : Sem (List Value × FuncBody) := do
  -- Resolve callee
  let body ← match funcTable calleeId with
    | some fb => pure fb
    | none    => Sem.throwTypeError "Call: undefined function"
  -- Resolve argument values
  let args ← argIds.mapM Sem.lookupValue
  -- Check arity
  match checkCallArity args body.paramTys with
  | .ok () => pure ()
  | .error msg => Sem.throwTypeError msg
  pure (args, body)

/-- Evaluate a CallIndirect instruction.
    Resolves the function pointer to a FuncId, then proceeds as Call.

    Mirrors Rust `Inst::CallIndirect`. -/
def semCallIndirect (funcTable : FuncTable) (funcPtrTable : FuncPtrTable)
    (funcTyTable : FuncTyTable)
    (calleeValId : ValueId) (sig : FuncTyId) (argIds : List ValueId)
    : Sem (List Value × FuncBody) := do
  -- Resolve the function pointer value
  let calleeVal ← Sem.lookupValue calleeValId
  let addr ← match calleeVal with
    | .ptr a   => pure a
    | .nullPtr => Sem.throwUB "CallIndirect: null function pointer"
    | _        => Sem.throwTypeError "CallIndirect: callee is not a pointer"
  -- Resolve pointer to FuncId
  let funcId ← match funcPtrTable addr with
    | some fid => pure fid
    | none     => Sem.throwUB "CallIndirect: invalid function pointer"
  -- Validate signature exists
  let _sigDef ← match funcTyTable sig with
    | some def_ => pure def_
    | none      => Sem.throwTypeError "CallIndirect: undefined function type"
  -- Delegate to semCall
  semCall funcTable funcId argIds

-- =================================================================
-- Switch semantics
-- =================================================================

/-- Match a switch value against a list of cases.
    Returns the first matching case target and args, or none. -/
def matchSwitchCase (switchVal : Value) (cases : List SwitchCase)
    : Option SwitchCase :=
  cases.find? fun sc =>
    match switchVal, sc.value with
    | .int _w v, .int cv    => v == cv
    | .bool b,   .bool cb   => b == cb
    | _, _                  => false

/-- Evaluate a Switch instruction.
    Matches the value against cases, branching to the first match
    or falling through to the default target.

    Mirrors Rust `Inst::Switch`. -/
def semSwitch (valueId : ValueId) (default_ : BlockId)
    (defaultArgIds : List ValueId) (cases : List SwitchCase)
    : Sem StepResult := do
  let val ← Sem.lookupValue valueId
  -- The scrutinee is inspected: a poison switch value is UB (without this
  -- guard `matchSwitchCase` would silently fall through to the default edge).
  Sem.rejectPartial val "Switch"
  match matchSwitchCase val cases with
  | some sc => do
    let args ← sc.args.mapM Sem.lookupValue
    pure (.Continue sc.target args)
  | none => do
    let args ← defaultArgIds.mapM Sem.lookupValue
    pure (.Continue default_ args)

-- =================================================================
-- Call stack predicates (for theorem statements)
-- =================================================================

/-- Predicate: the call stack depth is bounded by a given fuel. -/
def callStackBounded (stack : CallStack) (bound : Nat) : Prop :=
  stack.length <= bound

/-- Predicate: the call stack is empty (top-level execution). -/
def isTopLevel (stack : CallStack) : Prop :=
  stack.length = 0

end TrustIr
