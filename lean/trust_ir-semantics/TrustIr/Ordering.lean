-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Memory ordering and atomic RMW operation enums.
-- Mirrors: crates/trust_ir/src/inst.rs (Ordering, AtomicRMWOp)

namespace TrustIr

/-!
# Memory Ordering

Mirrors the C11 memory model orderings used by TrustIr's atomic instructions.
See: Batty et al., "Mathematizing C++ concurrency", POPL 2011.

## AtomicRMWOp
Atomic read-modify-write operations (10 variants).
-/

/-- Memory ordering for atomic operations.
    Mirrors Rust `trust_ir::Ordering` (5 variants). -/
inductive MemOrdering where
  | Relaxed : MemOrdering
  | Acquire : MemOrdering
  | Release : MemOrdering
  | AcqRel  : MemOrdering
  | SeqCst  : MemOrdering
  deriving DecidableEq, Repr

/-- Atomic read-modify-write operation.
    Mirrors Rust `trust_ir::AtomicRMWOp` (10 variants). -/
inductive AtomicRMWOp where
  | Xchg : AtomicRMWOp
  | Add  : AtomicRMWOp
  | Sub  : AtomicRMWOp
  | And  : AtomicRMWOp
  | Or   : AtomicRMWOp
  | Xor  : AtomicRMWOp
  | Max  : AtomicRMWOp
  | Min  : AtomicRMWOp
  | UMax : AtomicRMWOp
  | UMin : AtomicRMWOp
  deriving DecidableEq, Repr

end TrustIr
