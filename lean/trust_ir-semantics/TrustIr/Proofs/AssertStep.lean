-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Semantics.Step

namespace TrustIr

theorem sem_run_bind_eq {a b : Type} (ma : Sem a) (f : a -> Sem b)
    (s : MachineState) :
    Sem.run (ma >>= f) s = match Sem.run ma s with
      | .ok (a, s') => Sem.run (f a) s'
      | .error e => .error e := by
  simp [Sem.run, StateT.run, bind, StateT.bind, Except.bind]
  cases (ma s) with
  | ok val => rfl
  | error e => rfl

/-- A failed assert never succeeds, whatever its kind and site: it computes
    its panic message (reading the kind's operands), resolves its site's
    location (amendment P), and then panics (plan item P). -/
theorem semAssertFail_run_not_ok {α : Type} (k : AssertKind) (site : Option PanicSite)
    (s : MachineState) (r : α × MachineState) :
    Sem.run (semAssertFail k site : Sem α) s ≠ .ok r := by
  intro h
  unfold semAssertFail at h
  rw [sem_run_bind_eq] at h
  cases hm : Sem.run (assertFailMessage k) s with
  | error e => rw [hm] at h; cases h
  | ok v =>
    rw [hm] at h
    obtain ⟨msg, s1⟩ := v
    cases site with
    | none => cases h
    | some st =>
      dsimp only at h
      rw [sem_run_bind_eq] at h
      cases hl : Sem.run (resolvePanicLocation st.location) s1 with
      | error e => rw [hl] at h; cases h
      | ok w => rw [hl] at h; cases h

/-- The continuation condition of a canonical Bool assertion is a conjunction,
not an assumption. No panic label or annotation establishes its condition. -/
theorem assert_step_wp_iff (cond : ValueId) (kind : AssertKind) (site : Option PanicSite)
    (model : ByteModel) (state : MachineState) (value : Bool)
    (lookup : state.lookupValue cond = some (.bool value)) (post : MachineState → Prop) :
    (∃ result after, Sem.run (stepInst (.Assert cond kind site) model) state =
      .ok (result, after) ∧ post after) ↔ value = true ∧ post state := by
  have execute : Sem.run (stepInst (.Assert cond kind site) model) state =
      if value then .ok (.value none, state) else Sem.run (semAssertFail kind site) state := by
    cases value <;>
      simp [stepInst, Sem.lookupValue, Sem.getState, Sem.run, StateT.run,
        bind, StateT.bind, StateT.get, Except.bind, Except.pure, pure, StateT.pure, lookup, Sem.rejectPartial]
  rw [execute]
  cases value with
  | false =>
    simp only [Bool.false_eq_true, if_false, false_and, iff_false]
    rintro ⟨result, after, run, _⟩
    exact semAssertFail_run_not_ok kind site state (result, after) run
  | true =>
    constructor
    · rintro ⟨result, after, run, holds⟩
      simp only [if_pos rfl] at run
      cases run
      exact ⟨rfl, holds⟩
    · rintro ⟨_, holds⟩
      exact ⟨.value none, state, rfl, holds⟩

end TrustIr
