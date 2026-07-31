-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Coroutine suspend semantics: CoroSuspend (state-machine lowering).
-- Mirrors: crates/trust-ir/src/inst.rs Inst::CoroSuspend and the reference
-- interpreter (crates/trust-ir/src/interpret.rs).

import TrustIr.Inst
import TrustIr.Semantics.Monad
import TrustIr.Semantics.Control
import TrustIr.Semantics.Memory

namespace TrustIr

/-!
# Coroutine Suspend Semantics

`CoroSuspend` is the single coroutine-specific primitive: a TERMINATOR that
models one `yield`. Operationally it is exactly the macro-expansion backends
lower it to (inst.rs "Backends lower `CoroSuspend` by macro-expanding it"):

    store i64 `nextState` into `frame[stateSlot]`   -- the frame's state index
    return `value`

`semCoroSuspend` is DEFINED as that composition of the already-modelled
semantic functions — a fresh `i64` slot index, `semGEP` to the state field,
a fresh `i64` next-state value, `semStore`, then `semReturn` — so its
correctness reduces to the per-instruction semantics it composes, exactly as
the backend lowering's correctness reduces to the per-instruction lowering
proofs. The fresh binds mirror the `Const` instructions the macro-expansion
materializes for the two immediates.

The matched `resume` entry is NOT a new primitive: it is an ordinary
`Load` + `Switch` dispatch on `frame[stateSlot]`, already covered by the
memory and control-flow semantics.
-/

/-- Evaluate a CoroSuspend terminator: record the resume state index in the
    coroutine frame, then return the yielded value to the resumer. -/
def semCoroSuspend (frameId : ValueId) (stateSlot : Nat) (nextState : Int)
    (valueId : ValueId) : Sem StepResult := do
  let slotIdx ← Sem.bindFresh (.int 64 stateSlot)
  let slotAddr ← semGEP .I64 frameId [slotIdx]
  let next ← Sem.bindFresh (.int 64 nextState)
  semStore .I64 slotAddr next
  semReturn [valueId]

/-- Definition-shape lock: a DEFINITIONAL equality pinning `semCoroSuspend`
    to the composition above, so any future edit that diverges from the
    expansion breaks this lemma rather than silently changing the semantics.

    Honest scope: this is `rfl` against the definition — it does NOT relate
    `semCoroSuspend` to `stepInst`-executed `Const`/`GEP`/`Store`/`Return`
    instructions. The gap is small but real: `semGEP`/`semStore`/`semReturn`
    ARE the `stepInst` implementations of those instructions, and `stepInst`'s
    `Const .I64 (.int k)` case binds `Value.int 64 k` exactly as the
    `Sem.bindFresh` here does (Step.lean, width from `Ty.bitWidth`), but the
    `InstrResult` plumbing and the static-vs-extracted operand ids of a real
    instruction sequence are not modelled by this lemma. The end-to-end
    behavior is pinned by the `coro_suspend_stores_state_and_yields_stable`
    fixture (ExecutableFixtures.lean); a full `stepInst`-sequence equivalence
    theorem is a candidate deepening (B3 depth ledger). -/
theorem semCoroSuspend_is_macro_expansion (frameId : ValueId) (stateSlot : Nat)
    (nextState : Int) (valueId : ValueId) :
    semCoroSuspend frameId stateSlot nextState valueId
      = (do
          let slotIdx ← Sem.bindFresh (.int 64 stateSlot)
          let slotAddr ← semGEP .I64 frameId [slotIdx]
          let next ← Sem.bindFresh (.int 64 nextState)
          semStore .I64 slotAddr next
          semReturn [valueId]) := rfl

end TrustIr
