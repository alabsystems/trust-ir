-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Specification scaffold for vector Select condition-shape policy.

import TrustIr.Basic

namespace TrustIr
namespace VectorSelectPlan

/-!
# Vector Bool Select Plan

The executable Lean semantics supports a bounded `Ty.Vector` / `Value.vector`
subset. This module records the source-level condition-shape contract:

* scalar `Select` stays Bool-gated;
* vector `Select` MUST use a same-lane `<N x Bool>` mask for lane-wise
  selection; scalar `Bool` for whole-vector selection is REJECTED in the
  current contract (producers should splat the bool if needed);
* physical integer masks such as x86 `<N x i32>` all-ones/zero lanes are
  lowering carriers, not TrustIr source conditions.
-/

/-- Planned source-level condition shapes for vector `Select`.

`physicalIntMaskVector lanes width` is included only to state its rejection:
it models x86/SIMD carrier masks such as `<4 x i32>`, not logical TrustIr
conditions. -/
inductive SourceCondShape where
  | scalarBool : SourceCondShape
  | laneBoolVector : Nat -> SourceCondShape
  | physicalIntMaskVector : Nat -> Nat -> SourceCondShape
  deriving Repr, BEq

/-- Acceptance predicate for a `Select` whose result is a vector with
`resultLanes` lanes. -/
def SourceCondShape.acceptsVectorSelect
    (resultLanes : Nat) : SourceCondShape -> _root_.Bool
  | .scalarBool => false
  | .laneBoolVector maskLanes => maskLanes == resultLanes
  | .physicalIntMaskVector _ _ => false

/-- A scalar Bool condition is REJECTED for vector Select. -/
theorem scalarBool_rejected (resultLanes : Nat) :
    SourceCondShape.acceptsVectorSelect resultLanes .scalarBool = false := rfl

/-- A lane-wise Bool vector condition is accepted exactly when lane counts
match. -/
theorem laneBoolVector_acceptance (resultLanes maskLanes : Nat) :
    SourceCondShape.acceptsVectorSelect resultLanes
      (.laneBoolVector maskLanes) = (maskLanes == resultLanes) := rfl

/-- The x86 CHC helper's common `<N x i32>` all-ones/zero mask carrier is not a
TrustIr source condition. Lowering may use it after logical masks are already
typed. -/
theorem physicalI32Mask_rejected (resultLanes maskLanes : Nat) :
    SourceCondShape.acceptsVectorSelect resultLanes
      (.physicalIntMaskVector maskLanes 32) = false := rfl

/-- No physical integer mask width is accepted as a vector `Select` source
condition. -/
theorem physicalIntMask_rejected
    (resultLanes maskLanes width : Nat) :
    SourceCondShape.acceptsVectorSelect resultLanes
      (.physicalIntMaskVector maskLanes width) = false := rfl

end VectorSelectPlan
end TrustIr
