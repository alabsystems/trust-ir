-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Atomic operation semantics: AtomicLoad, AtomicStore, AtomicRMW,
-- CmpXchg, Fence.
-- Phase 4 of the formalization roadmap.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 6 Phase 4
-- Reference: Batty et al., "Mathematizing C++ concurrency", POPL 2011
-- Reference: ISO/IEC 9899:2011 (C11) Section 7.17 -- Atomics

import TrustIr.Inst
import TrustIr.Semantics.Monad
import TrustIr.Semantics.Memory

namespace TrustIr

/-!
# Atomic Operation Semantics

## Sequential Consistency Model

For Phase 4, all atomic operations are modeled with **sequential
consistency** (SC) semantics.  Under SC, all threads observe the
same total order of atomic operations.  Since TrustIr evaluation is
single-threaded (no concurrency in the semantic model), SC semantics
reduce to plain load/store with the memory ordering annotation
carried as metadata.

## Relaxed Orderings

The `MemOrdering` parameter is recorded but does not affect the
Phase 4 semantics.  Weaker orderings (Relaxed, Acquire, Release,
AcqRel) will be modeled in Phase 5 when concurrency is introduced.

## Operations

- **AtomicLoad**: Identical to Load under SC.
- **AtomicStore**: Identical to Store under SC.
- **AtomicRMW**: Read-modify-write.  Atomically reads the value at a
  pointer, applies a binary operation, and writes the result back.
  Returns the *old* value (pre-modification), matching LLVM IR
  semantics.
- **CmpXchg**: Compare-and-exchange.  Atomically compares the value
  at a pointer with an expected value.  If they match, writes the
  desired value.  Returns a pair `(old_value, success_flag)`.
- **Fence**: Memory fence.  Under SC, this is a no-op (all accesses
  are already totally ordered).

## Encoding

Atomic operations reuse the byte encoding/decoding functions from
`Memory.lean`.  The atomicity guarantee is semantic (no interleaving
in the single-threaded model), not represented in the byte encoding.
-/

-- =================================================================
-- Ordering validation
-- =================================================================

/-- Check that a load ordering is valid (not Release or AcqRel). -/
def isValidLoadOrdering : MemOrdering -> Bool
  | .Relaxed => true
  | .Acquire => true
  | .SeqCst  => true
  | _        => false

/-- Check that a store ordering is valid (not Acquire or AcqRel). -/
def isValidStoreOrdering : MemOrdering -> Bool
  | .Relaxed => true
  | .Release => true
  | .SeqCst  => true
  | _        => false

-- =================================================================
-- AtomicLoad
-- =================================================================

/-- Evaluate an AtomicLoad instruction.
    Under SC, this is identical to a regular Load plus ordering
    validation.

    Mirrors Rust `Inst::AtomicLoad`. -/
def semAtomicLoad (ty : Ty) (ptrId : ValueId) (ordering : MemOrdering)
    : Sem ValueId := do
  -- Validate ordering
  if !isValidLoadOrdering ordering then
    Sem.throwTypeError "AtomicLoad: invalid load ordering"
  -- Delegate to regular load logic
  let ptrVal ← Sem.lookupValue ptrId
  let addr ← match ptrVal with
    | .ptr a    => pure a
    | .nullPtr  => Sem.throwUB "AtomicLoad: null pointer dereference"
    | _         => Sem.throwTypeError "AtomicLoad: operand is not a pointer"
  if addr == 0 then Sem.throwUB "AtomicLoad: null pointer dereference"
  let byteSize ← match ty.byteSize with
    | some s => pure s
    | none   => Sem.throwTypeError "AtomicLoad: type has no byte size"
  let s ← Sem.getState
  if !s.memory.isInBounds addr byteSize then
    Sem.throwUB "AtomicLoad: access is out of bounds"
  let bytes ← match s.memory.readBytes addr byteSize with
    | some bs => pure bs
    | none    => Sem.throwUB "AtomicLoad: reading uninitialized memory"
  match decodeValue ty bytes with
  | some v => Sem.bindFresh v
  | none   => Sem.throwTypeError "AtomicLoad: failed to decode bytes"

-- =================================================================
-- AtomicStore
-- =================================================================

/-- Evaluate an AtomicStore instruction.
    Under SC, this is identical to a regular Store plus ordering
    validation.

    Mirrors Rust `Inst::AtomicStore`. -/
def semAtomicStore (ty : Ty) (ptrId valueId : ValueId) (ordering : MemOrdering)
    : Sem Unit := do
  -- Validate ordering
  if !isValidStoreOrdering ordering then
    Sem.throwTypeError "AtomicStore: invalid store ordering"
  -- Delegate to regular store logic
  let ptrVal ← Sem.lookupValue ptrId
  let addr ← match ptrVal with
    | .ptr a    => pure a
    | .nullPtr  => Sem.throwUB "AtomicStore: null pointer dereference"
    | _         => Sem.throwTypeError "AtomicStore: first operand is not a pointer"
  if addr == 0 then Sem.throwUB "AtomicStore: null pointer dereference"
  let byteSize ← match ty.byteSize with
    | some s => pure s
    | none   => Sem.throwTypeError "AtomicStore: type has no byte size"
  let s ← Sem.getState
  if !s.memory.isInBounds addr byteSize then
    Sem.throwUB "AtomicStore: access is out of bounds"
  let val ← Sem.lookupValue valueId
  let encoded ← match encodeValue val with
    | some bs => pure bs
    | none    => Sem.throwTypeError "AtomicStore: cannot encode value"
  if encoded.length != byteSize then
    Sem.throwTypeError "AtomicStore: encoded size does not match type size"
  let mem' := s.memory.writeBytes addr encoded
  Sem.modifyState fun st => { st with memory := mem' }

-- =================================================================
-- AtomicRMW helper: apply the RMW operation
-- =================================================================

/-- Apply an atomic read-modify-write operation to two integer values.
    Returns the new value to be written back.

    For Max/Min/UMax/UMin, we need signed vs unsigned comparison.
    In Phase 4 we use simple Int comparison (treating all values as
    signed).  UMax/UMin treat values as unsigned by masking. -/
def applyAtomicRMWOp (op : AtomicRMWOp) (width : Nat) (old new_ : Int) : Int :=
  let modulus := (2 : Int) ^ width
  let wrap (v : Int) := ((v % modulus) + modulus) % modulus
  match op with
  | .Xchg => new_
  | .Add  => wrap (old + new_)
  | .Sub  => wrap (old - new_)
  | .And  => Int.land old new_
  | .Or   => Int.lor old new_
  | .Xor  => Int.xor old new_
  | .Max  => if old >= new_ then old else new_
  | .Min  => if old <= new_ then old else new_
  | .UMax =>
    let uOld := wrap old
    let uNew := wrap new_
    if uOld >= uNew then old else new_
  | .UMin =>
    let uOld := wrap old
    let uNew := wrap new_
    if uOld <= uNew then old else new_

-- =================================================================
-- AtomicRMW
-- =================================================================

/-- Evaluate an AtomicRMW instruction.
    Atomically reads the value at the pointer, applies the RMW
    operation, and writes the result back.  Returns the *old*
    value (before modification), matching LLVM IR semantics.

    Mirrors Rust `Inst::AtomicRMW`. -/
def semAtomicRMW (op : AtomicRMWOp) (ty : Ty) (ptrId valueId : ValueId)
    (_ordering : MemOrdering) : Sem ValueId := do
  -- Read the old value from memory
  let ptrVal ← Sem.lookupValue ptrId
  let addr ← match ptrVal with
    | .ptr a    => pure a
    | .nullPtr  => Sem.throwUB "AtomicRMW: null pointer dereference"
    | _         => Sem.throwTypeError "AtomicRMW: operand is not a pointer"
  if addr == 0 then Sem.throwUB "AtomicRMW: null pointer dereference"
  let byteSize ← match ty.byteSize with
    | some s => pure s
    | none   => Sem.throwTypeError "AtomicRMW: type has no byte size"
  let s ← Sem.getState
  if !s.memory.isInBounds addr byteSize then
    Sem.throwUB "AtomicRMW: access is out of bounds"
  -- Read old value
  let bytes ← match s.memory.readBytes addr byteSize with
    | some bs => pure bs
    | none    => Sem.throwUB "AtomicRMW: reading uninitialized memory"
  let oldVal ← match decodeValue ty bytes with
    | some v => pure v
    | none   => Sem.throwTypeError "AtomicRMW: failed to decode bytes"
  -- Get the operand value
  let operandVal ← Sem.lookupValue valueId
  -- Apply the RMW operation
  let newVal ← match oldVal, operandVal with
    | .int w oldInt, .int _ operandInt =>
      let result := applyAtomicRMWOp op w oldInt operandInt
      pure (.int w result)
    | _, _ => Sem.throwTypeError "AtomicRMW: expected integer operands"
  -- Write back the new value
  let newEncoded ← match encodeValue newVal with
    | some bs => pure bs
    | none    => Sem.throwTypeError "AtomicRMW: cannot encode new value"
  let s' ← Sem.getState
  let mem' := s'.memory.writeBytes addr newEncoded
  Sem.modifyState fun st => { st with memory := mem' }
  -- Return the OLD value
  Sem.bindFresh oldVal

-- =================================================================
-- CmpXchg
-- =================================================================

/-- Evaluate a CmpXchg (compare-and-exchange) instruction.
    Atomically compares the value at `ptr` with `expected`:
    - If equal: writes `desired` and returns `(old, true)`
    - If not equal: leaves memory unchanged and returns `(old, false)`

    Returns an aggregate value `[old_value, success_flag]`.

    Mirrors Rust `Inst::CmpXchg`. -/
def semCmpXchg (ty : Ty) (ptrId expectedId desiredId : ValueId)
    (_success _failure : MemOrdering) : Sem ValueId := do
  -- Read the current value from memory
  let ptrVal ← Sem.lookupValue ptrId
  let addr ← match ptrVal with
    | .ptr a    => pure a
    | .nullPtr  => Sem.throwUB "CmpXchg: null pointer dereference"
    | _         => Sem.throwTypeError "CmpXchg: operand is not a pointer"
  if addr == 0 then Sem.throwUB "CmpXchg: null pointer dereference"
  let byteSize ← match ty.byteSize with
    | some s => pure s
    | none   => Sem.throwTypeError "CmpXchg: type has no byte size"
  let s ← Sem.getState
  if !s.memory.isInBounds addr byteSize then
    Sem.throwUB "CmpXchg: access is out of bounds"
  -- Read current value
  let bytes ← match s.memory.readBytes addr byteSize with
    | some bs => pure bs
    | none    => Sem.throwUB "CmpXchg: reading uninitialized memory"
  let currentVal ← match decodeValue ty bytes with
    | some v => pure v
    | none   => Sem.throwTypeError "CmpXchg: failed to decode bytes"
  -- Compare with expected
  let expectedVal ← Sem.lookupValue expectedId
  let isEqual := match currentVal, expectedVal with
    | .int _ a, .int _ b => a == b
    | .bool a,  .bool b  => a == b
    | .ptr a,   .ptr b   => a == b
    | _, _               => false
  -- If equal, write desired; otherwise leave memory unchanged
  if isEqual then do
    let desiredVal ← Sem.lookupValue desiredId
    let desiredEncoded ← match encodeValue desiredVal with
      | some bs => pure bs
      | none    => Sem.throwTypeError "CmpXchg: cannot encode desired value"
    let s' ← Sem.getState
    let mem' := s'.memory.writeBytes addr desiredEncoded
    Sem.modifyState fun st => { st with memory := mem' }
  -- Return aggregate (old_value, success_flag)
  Sem.bindFresh (.aggregate [currentVal, .bool isEqual])

-- =================================================================
-- Fence
-- =================================================================

/-- Evaluate a Fence instruction.
    Under sequential consistency, Fence is a no-op -- all memory
    accesses are already totally ordered.

    In a concurrent model (Phase 5), Fence would emit ordering
    constraints into the memory order graph.

    Mirrors Rust `Inst::Fence`. -/
def semFence (_ordering : MemOrdering) : Sem Unit :=
  pure ()

-- =================================================================
-- Atomic safety predicates (for theorem statements)
-- =================================================================

/-- Predicate: the given ordering is valid for a load operation. -/
def isValidLoadOrderingPred (ord : MemOrdering) : Prop :=
  ord = .Relaxed \/ ord = .Acquire \/ ord = .SeqCst

/-- Predicate: the given ordering is valid for a store operation. -/
def isValidStoreOrderingPred (ord : MemOrdering) : Prop :=
  ord = .Relaxed \/ ord = .Release \/ ord = .SeqCst

/-- Predicate: AtomicRMW with Xchg writes exactly the operand value. -/
def xchgWritesOperand (width : Nat) (old new_ : Int) : Prop :=
  applyAtomicRMWOp .Xchg width old new_ = new_

end TrustIr
