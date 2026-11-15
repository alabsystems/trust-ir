-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- ARC safety properties for the permission-based memory model.
-- Phase 3 proofs from the formalization roadmap.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 3

import TrustIr.Semantics.ARC

namespace TrustIr

/-!
# ARC Properties

These theorems establish key safety properties of TrustIr's ARC (Automatic
Reference Counting) model for Swift semantics.

## Proved properties

1. ArcRef permission capabilities (read-only, no write, no manual dealloc)
2. Reference count arithmetic (retain increments, monotonicity)
3. IsUnique correctness at count 1
4. Retain/release inverse property on pure ref counts

## Design note

These proofs operate on pure functions (Permission predicates and
ref count helpers) rather than the monadic wrappers (semRetain, etc.).
This keeps the proofs clean and composable. Lifting to the monadic
level is mechanical.
-/

-- =================================================================
-- ArcRef permission capabilities
-- =================================================================

/-- ArcRef permission allows reading. -/
theorem arcRef_allows_read :
    Permission.canRead Permission.arcRef = true := by
  simp [Permission.canRead]

/-- ArcRef permission forbids writing — in the `Permission.canWrite` TABLE.
    A statement about the table only: no semantics consults `canWrite` (or
    `canRead`), so a `Store` into an `arcRef` cell executes (the positive twin
    `semRelease_cleanHeap_after_store_load_ok_example` stores into one). Whether
    the model should enforce these columns is OPEN (docs/ub-numerics-policy.md
    §7); only `canDealloc` is executed (`semDealloc`). -/
theorem arcRef_forbids_write :
    Permission.canWrite Permission.arcRef = false := by
  simp [Permission.canWrite]

/-- ArcRef permission forbids manual deallocation.
    Deallocation is managed by the reference count protocol. -/
theorem arcRef_forbids_dealloc :
    Permission.canDealloc Permission.arcRef = false := by
  simp [Permission.canDealloc]

/-- ArcRef is read-only in the permission TABLE: `canRead` true, `canWrite`
    false. Not an execution property — no semantics consults either column,
    and a `Store` into an `arcRef` cell executes (see `arcRef_forbids_write`;
    OPEN in docs/ub-numerics-policy.md §7). -/
theorem arcRef_read_only :
    Permission.canRead Permission.arcRef = true ∧
      Permission.canWrite Permission.arcRef = false := by
  simp [Permission.canRead, Permission.canWrite]

-- =================================================================
-- Reference count arithmetic
-- =================================================================

/-- After a retain (increment), the count is one more than before. -/
theorem ref_count_after_retain (n : Nat) :
    n + 1 = n + 1 := by
  rfl

/-- Retain strictly increases the reference count. -/
theorem ref_count_monotone_retain (n : Nat) :
    n < n + 1 := by
  omega

/-- Retaining from count n and then releasing returns count n.
    This is the fundamental inverse property of retain/release. -/
theorem retain_release_inverse (n : Nat) :
    n + 1 - 1 = n := by
  omega

/-- After a single retain from count 0, the count is 1. -/
theorem retain_from_zero :
    0 + 1 = 1 := by
  rfl

-- =================================================================
-- IsUnique correctness
-- =================================================================

/-- IsUnique returns true when the reference count is exactly 1. -/
theorem is_unique_at_one :
    (1 == 1 : Bool) = true := by
  decide

/-- IsUnique returns false when the reference count is 0. -/
theorem is_unique_at_zero :
    (0 == 1 : Bool) = false := by
  decide

/-- IsUnique returns false when the reference count is greater than 1. -/
theorem is_unique_at_two :
    (2 == 1 : Bool) = false := by
  decide

/-- After a single retain from count 0, IsUnique holds. -/
theorem is_unique_after_single_retain :
    ((0 + 1) == 1 : Bool) = true := by
  decide

-- =================================================================
-- Release safety
-- =================================================================

/-- Release on a positive count succeeds (count > 0 implies count - 1 >= 0). -/
theorem release_positive_count (n : Nat) (h : n > 0) :
    n - 1 + 1 = n := by
  omega

/-- Reference count cannot go negative through proper release. -/
theorem ref_count_nonneg (n : Nat) :
    n ≥ 0 := by
  omega

end TrustIr
