-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Semantics.Arith

namespace TrustIr

theorem Sem.run_nextFloatZeroChoice (state : MachineState) :
    Sem.run Sem.nextFloatZeroChoice state =
      .ok (state.floatZeroChoices.choose state.floatZeroChoiceCursor,
        { state with floatZeroChoiceCursor := state.floatZeroChoiceCursor + 1 }) := rfl

theorem eraseFloatZeroChoices_with (state : MachineState) (choices : FloatZeroChoiceTape) :
    (state.withFloatZeroChoices choices).eraseFloatZeroChoices = state.eraseFloatZeroChoices := rfl

theorem eraseFloatZeroChoices_advance (state : MachineState) :
    ({ state with floatZeroChoiceCursor := state.floatZeroChoiceCursor + 1 }).eraseFloatZeroChoices =
      state.eraseFloatZeroChoices := rfl

theorem semFloatMinMaxAt_run (op : BinOp) (ty : Ty) (left right : Float)
    (state : MachineState) :
    Sem.run (semFloatMinMaxAt op ty left right) state =
      match floatMinMaxCandidates op ty left right with
      | .error error => .error error
      | .ok [value] => .ok (value, state)
      | .ok [a, b] => .ok
          (if state.floatZeroChoices.choose state.floatZeroChoiceCursor then a else b,
           { state with floatZeroChoiceCursor := state.floatZeroChoiceCursor + 1 })
      | .ok _ => .error (.typeError "invalid min/max candidate shape") := by
  unfold semFloatMinMaxAt
  cases candidates : floatMinMaxCandidates op ty left right with
  | error error => rfl
  | ok values =>
    cases values with
    | nil => rfl
    | cons a tail =>
      cases tail with
      | nil => rfl
      | cons b rest =>
        cases rest with
        | nil => rfl
        | cons c rest => rfl

/-- Every successful execution returns a permitted candidate and changes only
    ghost choice consumption. This ranges over all explicit choice inputs. -/
theorem semFloatMinMaxAt_permitted {op : BinOp} {ty : Ty} {left right value : Float}
    {before after : MachineState}
    (run : Sem.run (semFloatMinMaxAt op ty left right) before = .ok (value, after)) :
    ∃ candidates, floatMinMaxCandidates op ty left right = .ok candidates ∧
      value ∈ candidates ∧ after.eraseFloatZeroChoices = before.eraseFloatZeroChoices := by
  rw [semFloatMinMaxAt_run] at run
  cases result : floatMinMaxCandidates op ty left right with
  | error error => simp [result] at run
  | ok values =>
    cases values with
    | nil => simp [result] at run
    | cons a tail =>
      cases tail with
      | nil =>
        simp only [result, Except.ok.injEq, Prod.mk.injEq] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨[a], rfl, by simp, rfl⟩
      | cons b rest =>
        cases rest with
        | nil =>
          simp only [result, Except.ok.injEq, Prod.mk.injEq] at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨[a, b], rfl, ?_, rfl⟩
          split <;> simp
        | cons c rest => simp [result] at run

/-- Both tie alternatives are reachable, with the same program state after
    erasing ghost input. The tape is not fixed by a target or opcode. -/
theorem semFloatMinMaxAt_both_choices {op : BinOp} {ty : Ty} {left right a b : Float}
    (candidates : floatMinMaxCandidates op ty left right = .ok [a, b])
    (state : MachineState) :
    (∃ final, Sem.run (semFloatMinMaxAt op ty left right)
        (state.withFloatZeroChoices ⟨fun _ => true⟩) = .ok (a, final) ∧
      final.eraseFloatZeroChoices = state.eraseFloatZeroChoices) ∧
    (∃ final, Sem.run (semFloatMinMaxAt op ty left right)
        (state.withFloatZeroChoices ⟨fun _ => false⟩) = .ok (b, final) ∧
      final.eraseFloatZeroChoices = state.eraseFloatZeroChoices) := by
  constructor
  · let initial := state.withFloatZeroChoices ⟨fun _ => true⟩
    refine ⟨{ initial with floatZeroChoiceCursor := initial.floatZeroChoiceCursor + 1 }, ?_, rfl⟩
    rw [semFloatMinMaxAt_run, candidates]
    rfl
  · let initial := state.withFloatZeroChoices ⟨fun _ => false⟩
    refine ⟨{ initial with floatZeroChoiceCursor := initial.floatZeroChoiceCursor + 1 }, ?_, rfl⟩
    rw [semFloatMinMaxAt_run, candidates]
    rfl

end TrustIr
