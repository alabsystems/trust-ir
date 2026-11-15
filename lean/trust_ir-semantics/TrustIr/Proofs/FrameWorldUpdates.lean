-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.FrameActionExits

namespace TrustIr.FrameLifetime

/-- Resolve a snapshot read to the exact current state before a later
snapshot-based update. The observation itself changes no state. -/
theorem frame_get_bind_exit {α : Type} (post : Nat → α → Prop)
    (next : MachineState → Sem α) (state : MachineState)
    (tail : FrameActionExit post state (Sem.run (next state) state)) :
    FrameActionExit post state (Sem.run (do let observed ← Sem.getState; next observed) state) := tail

/-- Carry an already minted value through an actual action's monotone
history, including values with recursively nested frame identities. -/
theorem frame_carry_value_exit {α : Type} (before : MachineState) (result : Except SemError (α × MachineState))
    (value : Value) (incoming : MintedValue before.nextFrameLineage value)
    (safe : FrameActionExit (fun _ _ => True) before result) :
    FrameActionExit (fun bound _ => MintedValue bound value) before result := by
  cases result with
  | ok pair => exact ⟨safe.1,incoming.mono safe.2.2.monotone,safe.2.2⟩
  | error error => cases error <;> exact safe

/-- A checked read-only prefix retains the exact snapshot used by a later
world update. Both its normal observation and its error exits are checked. -/
theorem frame_readonly_bind_exit {α β : Type} (post : Nat → β → Prop)
    (action : Sem α) (next : α → Sem β) (state : MachineState)
    (readonly : CallCheckReadOnly action) (safe : CallCheckNoUnwind action)
    (tail : ∀ value, FrameActionExit post state (Sem.run (next value) state)) :
    FrameActionExit post state (Sem.run (action >>= next) state) := by
  rw [Sem.run_bind]
  cases executed : Sem.run action state with
  | error error =>
    cases error <;> first
      | exact True.intro
      | exact False.elim (safe state _ _ executed)
  | ok pair =>
    have same := readonly state pair executed
    obtain ⟨value, after⟩ := pair
    change after = state at same
    subst after
    exact tail value

end TrustIr.FrameLifetime
