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

The intrinsic operates on held values, as the reference interpreter does.
It does not manufacture SSA bindings for the lowering's temporary values.
A real expansion has explicit source destinations and a freshly inferred type
context; its relation to this intrinsic is proved separately at the real call
frame boundary, rather than by equating private register maps.

The matched `resume` entry is NOT a new primitive: it is an ordinary
`Load` + `Switch` dispatch on `frame[stateSlot]`, already covered by the
memory and control-flow semantics. That the two compose into a correct
state machine is proved, not assumed: `CoroGen.coro_two_state_roundtrip`
(`Proofs/CoroutineProps.lean`, WS2.25) drives a `load; switch {0, 1}` resume
entry twice over the real evaluator and gets the yielded value, then the
final value, for every state whose frame slot is a live zero-initialised
`i64` cell; the `next + 1` mutant is refuted alongside it.
-/

/-- Record the state index, then look up and return the yield operand.
    GEP and Store use shared value-level operations and publish no temporary
    SSA values. The error order matches the reference interpreter. -/
def semCoroSuspend (frameId : ValueId) (stateSlot : Nat) (nextState : Int)
    (valueId : ValueId) (model : ByteModel := .le64) : Sem StepResult := do
  let frame ← Sem.lookupValue frameId
  let slot ← semGEPValuesUsing (scalarMemoryLayout model)
    (fun (_ : Unit) value => typedIntegerValue model .I64 value)
    .I64 frame [((), Value.intAt 64 stateSlot)] model
  semStoreValueUsing (scalarMemoryLayout model) (encodeMemoryAt model .I64)
    .I64 slot (Value.intAt 64 nextState) false none model
  -- The reference interpreter looks up yield after the store. The intrinsic
  -- never publishes the lowering's private SSA temporaries.
  semReturn [valueId]

/-- The intrinsic performs the two immediate operations on held values.
    Actual SSA expansion correctness is a separate source-graph theorem; an
    untyped instruction stream with private aliases is not this semantics. -/
theorem semCoroSuspend_is_value_composition (frameId : ValueId) (stateSlot : Nat)
    (nextState : Int) (valueId : ValueId) (model : ByteModel := .le64) :
    semCoroSuspend frameId stateSlot nextState valueId model = (do
      let frame ← Sem.lookupValue frameId
      let slot ← semGEPValuesUsing (scalarMemoryLayout model)
        (fun (_ : Unit) value => typedIntegerValue model .I64 value)
        .I64 frame [((), Value.intAt 64 stateSlot)] model
      semStoreValueUsing (scalarMemoryLayout model) (encodeMemoryAt model .I64)
        .I64 slot (Value.intAt 64 nextState) false none model
      semReturn [valueId]) := rfl

end TrustIr
