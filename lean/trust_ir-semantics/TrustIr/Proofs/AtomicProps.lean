-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Atomic operation properties: ordering validation, RMW operation
-- correctness, and SC equivalence to regular loads/stores.
-- Phase 4 proofs from the formalization roadmap.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 6 Phase 4
-- Reference: Batty et al., "Mathematizing C++ concurrency", POPL 2011

import TrustIr.Semantics.Atomic

namespace TrustIr

/-!
# Atomic Properties

These theorems establish key correctness properties of TrustIr's atomic
operation semantics under sequential consistency.

## Proved properties

1. Ordering validation is correct (valid/invalid load/store orderings)
2. Xchg always produces the operand value
3. Fence is a no-op under SC

4. AtomicRMW And commutativity (via local Int.land_comm)
5. AtomicRMW Or commutativity (via local Int.lor_comm)
6. AtomicRMW Xor commutativity (via local Int.xor_comm)

## Design note

These proofs operate on the pure helpers (applyAtomicRMWOp,
isValidLoadOrdering, isValidStoreOrdering) rather than the monadic
wrappers (semAtomicLoad, etc.).  This keeps the proofs clean and
composable.
-/

-- =================================================================
-- Ordering validation properties
-- =================================================================

/-- Relaxed is a valid load ordering. -/
theorem relaxed_valid_load :
    isValidLoadOrdering .Relaxed = true := by
  simp [isValidLoadOrdering]

/-- Acquire is a valid load ordering. -/
theorem acquire_valid_load :
    isValidLoadOrdering .Acquire = true := by
  simp [isValidLoadOrdering]

/-- SeqCst is a valid load ordering. -/
theorem seqcst_valid_load :
    isValidLoadOrdering .SeqCst = true := by
  simp [isValidLoadOrdering]

/-- Release is NOT a valid load ordering. -/
theorem release_invalid_load :
    isValidLoadOrdering .Release = false := by
  simp [isValidLoadOrdering]

/-- AcqRel is NOT a valid load ordering. -/
theorem acqrel_invalid_load :
    isValidLoadOrdering .AcqRel = false := by
  simp [isValidLoadOrdering]

/-- Relaxed is a valid store ordering. -/
theorem relaxed_valid_store :
    isValidStoreOrdering .Relaxed = true := by
  simp [isValidStoreOrdering]

/-- Release is a valid store ordering. -/
theorem release_valid_store :
    isValidStoreOrdering .Release = true := by
  simp [isValidStoreOrdering]

/-- SeqCst is a valid store ordering. -/
theorem seqcst_valid_store :
    isValidStoreOrdering .SeqCst = true := by
  simp [isValidStoreOrdering]

/-- Acquire is NOT a valid store ordering. -/
theorem acquire_invalid_store :
    isValidStoreOrdering .Acquire = false := by
  simp [isValidStoreOrdering]

/-- AcqRel is NOT a valid store ordering. -/
theorem acqrel_invalid_store :
    isValidStoreOrdering .AcqRel = false := by
  simp [isValidStoreOrdering]

-- =================================================================
-- AtomicRMW operation properties
-- =================================================================

/-- Xchg always produces the new value, ignoring the old value. -/
theorem xchg_produces_new (width : Nat) (old new_ : Int) :
    applyAtomicRMWOp .Xchg width old new_ = new_ := by
  simp [applyAtomicRMWOp]

/-- AtomicRMW Add is commutative (modular arithmetic). -/
theorem atomic_add_comm (width : Nat) (a b : Int) :
    applyAtomicRMWOp .Add width a b = applyAtomicRMWOp .Add width b a := by
  simp [applyAtomicRMWOp, Int.add_comm]

/-- AtomicRMW And is commutative.
    Uses Int.land commutativity. -/
theorem atomic_and_comm (width : Nat) (a b : Int) :
    applyAtomicRMWOp .And width a b = applyAtomicRMWOp .And width b a := by
  simp [applyAtomicRMWOp, Int.land_comm]

/-- AtomicRMW Or is commutative.
    Uses Int.lor commutativity. -/
theorem atomic_or_comm (width : Nat) (a b : Int) :
    applyAtomicRMWOp .Or width a b = applyAtomicRMWOp .Or width b a := by
  simp [applyAtomicRMWOp, Int.lor_comm]

/-- AtomicRMW Xor is commutative.
    Uses Int.xor commutativity. -/
theorem atomic_xor_comm (width : Nat) (a b : Int) :
    applyAtomicRMWOp .Xor width a b = applyAtomicRMWOp .Xor width b a := by
  simp [applyAtomicRMWOp, Int.xor_comm]

-- =================================================================
-- Fence properties
-- =================================================================

/-- Fence is a no-op: it returns unit without modifying state.
    This is the key SC property -- fences have no observable effect
    in a totally-ordered execution model. -/
theorem fence_is_noop (ord : MemOrdering) (s : MachineState) :
    Sem.run (semFence ord) s = .ok ((), s) := by
  simp [semFence, Sem.run, StateT.run, pure, StateT.pure, Except.pure]

-- =================================================================
-- Xchg predicate
-- =================================================================

/-- The xchgWritesOperand predicate holds for all inputs. -/
theorem xchg_writes_operand_holds (width : Nat) (old new_ : Int) :
    xchgWritesOperand width old new_ := by
  simp [xchgWritesOperand, applyAtomicRMWOp]

-- =================================================================
-- Future work stubs (Phase 4 completeness claims)
-- =================================================================

/-
## Theorems to prove in subsequent iterations

1. **SC equivalence:**
   Under SC, semAtomicLoad with any valid ordering produces the same
   result as semLoad.  Formally:
     semAtomicLoad ty ptr ord s = semLoad ty ptr s
   for all valid load orderings ord.

2. **CmpXchg linearizability:**
   CmpXchg is linearizable: the compare and swap happen atomically
   with no intervening modification.  In SC this is trivially true
   since there is only one thread.

3. **AtomicRMW Add associativity:**
   applyAtomicRMWOp .Add w (applyAtomicRMWOp .Add w a b) c =
   applyAtomicRMWOp .Add w a (applyAtomicRMWOp .Add w b c)
   Under modular arithmetic.

4. **Ordering strength:**
   For valid orderings o1 and o2, if o1 is stronger than o2
   (e.g., SeqCst > AcqRel > Acquire/Release > Relaxed), then
   an atomic operation with o1 provides all guarantees of o2.
-/

end TrustIr
