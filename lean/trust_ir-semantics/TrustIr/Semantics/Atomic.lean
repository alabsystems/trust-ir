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
def semAtomicLoadUsing (decode : Memory → List UInt8 → Except SemError Value)
    (ty : Ty) (ptrId : ValueId) (ordering : MemOrdering)
    (model : ByteModel := .le64) : Sem ValueId := do
  -- Validate ordering
  if !isValidLoadOrdering ordering then
    Sem.throwTypeError "AtomicLoad: invalid load ordering"
  -- Delegate to regular load logic
  let ptrVal ← Sem.lookupValue ptrId
  Sem.rejectPartial ptrVal "AtomicLoad"
  let (ptrAddr, ptrAlloc) ← Sem.expectPointer "AtomicLoad" ptrVal
  let byteSize ← match (ty.byteSizeFor model) with
    | some s => pure s
    | none   => Sem.throwUnsupported .layout "AtomicLoad: type has no byte size"
  -- An atomic access is a strict access at the type's natural alignment
  -- through the operand's provenance (interpret.rs `eval_load(.., None, strict)`).
  let alignment ← Sem.accessAlign "AtomicLoad" ty none model
  let addr ← Sem.checkedAccess "AtomicLoad" ptrAddr ptrAlloc byteSize alignment model
  let s ← Sem.getState
  let bytes ← match s.memory.readBytes addr byteSize with
    | some bs => pure bs
    | none    => Sem.throwUB "AtomicLoad: reading uninitialized memory"
  match decode s.memory bytes with
  | .ok v    => Sem.bindFresh v
  | .error e => throw e

def semAtomicLoad (ty : Ty) (ptrId : ValueId) (ordering : MemOrdering)
    (model : ByteModel := .le64) : Sem ValueId :=
  semAtomicLoadUsing (fun mem bytes => decodeMemoryAt model mem ty bytes) ty ptrId ordering model

-- =================================================================
-- AtomicStore
-- =================================================================

/-- Evaluate an AtomicStore instruction.
    Under SC, this is identical to a regular Store plus ordering
    validation.

    Mirrors Rust `Inst::AtomicStore`. -/
def semAtomicStoreUsing (encode : Value → Except SemError (List UInt8))
    (ty : Ty) (ptrId valueId : ValueId) (ordering : MemOrdering)
    (model : ByteModel := .le64) : Sem Unit := do
  -- Validate ordering
  if !isValidStoreOrdering ordering then
    Sem.throwTypeError "AtomicStore: invalid store ordering"
  -- Delegate to regular store logic
  let ptrVal ← Sem.lookupValue ptrId
  Sem.rejectPartial ptrVal "AtomicStore"
  let (ptrAddr, ptrAlloc) ← Sem.expectPointer "AtomicStore" ptrVal
  let byteSize ← match (ty.byteSizeFor model) with
    | some s => pure s
    | none   => Sem.throwUnsupported .layout "AtomicStore: type has no byte size"
  -- An atomic access is a strict access at the type's natural alignment
  -- through the operand's provenance (interpret.rs `eval_load(.., None, strict)`).
  let alignment ← Sem.accessAlign "AtomicStore" ty none model
  let addr ← Sem.checkedAccess "AtomicStore" ptrAddr ptrAlloc byteSize alignment model
  let s ← Sem.getState
  let val ← Sem.lookupValue valueId
  -- An atomic store is STRICT: storing poison (`.partial` / `.undef`) is UB,
  -- mirroring interpret.rs `eval_store` with `strict = true` (roadmap WS2.10).
  Sem.rejectPartial val "AtomicStore"
  let encoded ← match encode val with
    | .ok bs   => pure bs
    | .error e => throw e
  if encoded.length != byteSize then
    Sem.throwTypeError "AtomicStore: encoded size does not match type size"
  let mem' := s.memory.writeBytes addr encoded
  Sem.modifyState fun st => { st with memory := mem' }

def semAtomicStore (ty : Ty) (ptrId valueId : ValueId) (ordering : MemOrdering)
    (model : ByteModel := .le64) : Sem Unit :=
  semAtomicStoreUsing (encodeMemoryAt model ty) ty ptrId valueId ordering model

-- =================================================================
-- AtomicRMW helper: apply the RMW operation
-- =================================================================

/-- Apply an atomic read-modify-write operation to two integer values.
    Returns the new value to be written back.

    `Max` / `Min` order the two values SIGNED (`toSigned`, the interpreter's
    `as_signed`), `UMax` / `UMin` unsigned. Both operands are residues (one
    integer representation, `Value.intAt`), and the result is one of them, so
    it is a residue too. Until 2026-09-30 `Max` / `Min` ordered the raw `Int`s,
    which on residues is the unsigned order: `atomicrmw max i32 p, -1` over a
    stored 5 wrote 4294967295 where the interpreter keeps 5 (168 of the 1680
    `AtomicRMW` runs of `negative_literal_constants_agree_across_engines`). -/
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
  | .Max  => if toSigned old width >= toSigned new_ width then old else new_
  | .Min  => if toSigned old width <= toSigned new_ width then old else new_
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
def semAtomicRMWUsing (decode : Memory → List UInt8 → Except SemError Value)
    (encode : Value → Except SemError (List UInt8))
    (op : AtomicRMWOp) (ty : Ty) (ptrId valueId : ValueId)
    (_ordering : MemOrdering) (model : ByteModel := .le64) : Sem ValueId := do
  -- Read the old value from memory
  let ptrVal ← Sem.lookupValue ptrId
  Sem.rejectPartial ptrVal "AtomicRMW"
  let (ptrAddr, ptrAlloc) ← Sem.expectPointer "AtomicRMW" ptrVal
  let byteSize ← match (ty.byteSizeFor model) with
    | some s => pure s
    | none   => Sem.throwUnsupported .layout "AtomicRMW: type has no byte size"
  -- An atomic access is a strict access at the type's natural alignment
  -- through the operand's provenance (interpret.rs `eval_load(.., None, strict)`).
  let alignment ← Sem.accessAlign "AtomicRMW" ty none model
  let addr ← Sem.checkedAccess "AtomicRMW" ptrAddr ptrAlloc byteSize alignment model
  let s ← Sem.getState
  -- Read old value
  let bytes ← match s.memory.readBytes addr byteSize with
    | some bs => pure bs
    | none    => Sem.throwUB "AtomicRMW: reading uninitialized memory"
  let oldVal ← match decode s.memory bytes with
    | .ok v    => pure v
    | .error e => throw e
  -- Get the operand value
  let operandVal ← Sem.lookupValue valueId
  -- The RMW operator inspects its operand: a poison operand is UB (WS2.10).
  Sem.rejectPartial operandVal "AtomicRMW"
  -- Apply the RMW operation
  let newVal ← match oldVal, operandVal with
    | .int w oldInt, .int _ operandInt =>
      let result := applyAtomicRMWOp op w oldInt operandInt
      pure (.int w result)
    | _, _ => Sem.throwTypeError "AtomicRMW: expected integer operands"
  -- Write back the new value
  let newEncoded ← match encode newVal with
    | .ok bs   => pure bs
    | .error e => throw e
  let s' ← Sem.getState
  let mem' := s'.memory.writeBytes addr newEncoded
  Sem.modifyState fun st => { st with memory := mem' }
  -- Return the OLD value
  Sem.bindFresh oldVal

def semAtomicRMW (op : AtomicRMWOp) (ty : Ty) (ptrId valueId : ValueId)
    (ordering : MemOrdering) (model : ByteModel := .le64) : Sem ValueId :=
  semAtomicRMWUsing (fun mem bytes => decodeMemoryAt model mem ty bytes) (encodeMemoryAt model ty)
    op ty ptrId valueId ordering model

-- =================================================================
-- CmpXchg
-- =================================================================

/-- Evaluate a CmpXchg (compare-and-exchange) instruction.
    Atomically compares the value at `ptr` with `expected`:
    - If equal: writes `desired` and returns `(old, true)`
    - If not equal: leaves memory unchanged and returns `(old, false)`

    `semCmpXchgExchange` is the memory half: it performs the compare and the
    conditional write and returns the pair `(old value, success flag)` as
    plain values; `semCmpXchg` then binds them.

    Mirrors Rust `Inst::CmpXchg`. -/
def semCmpXchgExchangeUsing (decode : Memory → List UInt8 → Except SemError Value)
    (encode : Value → Except SemError (List UInt8))
    (ty : Ty) (ptrId expectedId desiredId : ValueId) (model : ByteModel := .le64) :
    Sem (Value × Bool) := do
  -- Read the current value from memory
  let ptrVal ← Sem.lookupValue ptrId
  Sem.rejectPartial ptrVal "CmpXchg"
  let (ptrAddr, ptrAlloc) ← Sem.expectPointer "CmpXchg" ptrVal
  let byteSize ← match (ty.byteSizeFor model) with
    | some s => pure s
    | none   => Sem.throwUnsupported .layout "CmpXchg: type has no byte size"
  -- An atomic access is a strict access at the type's natural alignment
  -- through the operand's provenance (interpret.rs `eval_load(.., None, strict)`).
  let alignment ← Sem.accessAlign "CmpXchg" ty none model
  let addr ← Sem.checkedAccess "CmpXchg" ptrAddr ptrAlloc byteSize alignment model
  let s ← Sem.getState
  -- Read current value
  let bytes ← match s.memory.readBytes addr byteSize with
    | some bs => pure bs
    | none    => Sem.throwUB "CmpXchg: reading uninitialized memory"
  let currentVal ← match decode s.memory bytes with
    | .ok v    => pure v
    | .error e => throw e
  -- Compare with expected
  let expectedVal ← Sem.lookupValue expectedId
  -- The comparison INSPECTS `expected`: a poison `expected` is UB, never a
  -- silent "unequal" (mirror interpret.rs `Inst::CmpXchg`, WS2.10 review).
  Sem.rejectPartial expectedVal "CmpXchg expected"
  -- The comparison is BITWISE (LLVM `cmpxchg`, the interpreter's value
  -- equality over `FloatBits`): a float compares its IEEE pattern at `ty`,
  -- so `+0.0` and `-0.0` differ. A NaN refuses (`floatToBitsAt`): its payload
  -- is unobservable in Lean 4.8.0, so neither answer can be vouched for.
  -- (Before WS2.23 a float never compared equal, so an F32/F64 `cmpxchg`
  -- whose expected value matched memory reported failure and skipped the
  -- write.)
  let isEqual ← match currentVal, expectedVal with
    | .float a, .float b =>
      match floatToBitsAt ty a, floatToBitsAt ty b with
      | .ok x, .ok y => pure (x == y)
      | .error e, _ => throw e
      | _, .error e => throw e
    | .int _ a, .int _ b => pure (a == b)
    | .bool a,  .bool b  => pure (a == b)
    | .ptr a p, .ptr b q => pure (a == b && p == q)
    | .fnDef a f, .fnDef b g => pure (a == b && f == g)
    | .nullPtr, .nullPtr => pure true
    | _, _               => pure false
  -- If equal, write desired; otherwise leave memory unchanged
  if isEqual then do
    let desiredVal ← Sem.lookupValue desiredId
    -- The successful exchange is a STRICT store: poison `desired` is UB.
    Sem.rejectPartial desiredVal "CmpXchg"
    let desiredEncoded ← match encode desiredVal with
      | .ok bs   => pure bs
      | .error e => throw e
    let s' ← Sem.getState
    let mem' := s'.memory.writeBytes addr desiredEncoded
    Sem.modifyState fun st => { st with memory := mem' }
  pure (currentVal, isEqual)

def semCmpXchgExchange (ty : Ty) (ptrId expectedId desiredId : ValueId)
    (model : ByteModel := .le64) : Sem (Value × Bool) :=
  semCmpXchgExchangeUsing (fun mem bytes => decodeMemoryAt model mem ty bytes) (encodeMemoryAt model ty)
    ty ptrId expectedId desiredId model

/-- Evaluate a CmpXchg instruction: run the exchange, then bind TWO fresh SSA
    values, in order — the old (loaded) value, then the success flag — and
    return their ids `(old, success)`. This is the Rust two-result shape
    (interpret.rs `bind_results(.., [current, success])`); there is no packed
    aggregate form (WS2.24). -/
def semCmpXchg (ty : Ty) (ptrId expectedId desiredId : ValueId)
    (_success _failure : MemOrdering) (model : ByteModel := .le64) : Sem (ValueId × ValueId) := do
  let exchanged ← semCmpXchgExchange ty ptrId expectedId desiredId model
  Sem.bindFreshPair exchanged.1 (.bool exchanged.2)

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
