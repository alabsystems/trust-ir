-- Copyright 2026 Andrew Yates
-- SPDX-License-Identifier: Apache-2.0
import TrustIr.Proofs.AYFreshGates
import Init.Data.Array.Lemmas

namespace TrustIr.AYGateCNF

@[macro_inline] def bufferEnv (store : Array Bool) (fallback : Assignment) : Assignment :=
  fun id => if h : id < store.size then store[id] else fallback id

theorem bufferEnv_push (store : Array Bool) (fallback : Assignment) (value : Bool) :
    bufferEnv (store.push value) fallback =
      (fun id => if id = store.size then value else bufferEnv store fallback id) := by
  funext id
  by_cases before : id < store.size
  · have within : id < store.size + 1 := by omega
    trustIrCompilerProof {
      simp [bufferEnv, before, within,
        Array.get_push_lt, show id ≠ store.size by omega]
    } {
      simp [bufferEnv, before, within,
        Array.getElem_push_lt, show id ≠ store.size by omega]
    }
  · by_cases same : id = store.size
    · subst id
      simp [bufferEnv]
    · have later : ¬ id < store.size + 1 := by omega
      simp [bufferEnv, before, same, later]

def bufferGates (gates : List Gate) (store : Array Bool) (fallback : Assignment) : Array Bool :=
  gates.foldl (fun current gate => current.push (gate.eval (bufferEnv current fallback))) store

theorem Valid.bufferGates_eq (gates : List Gate) (store : Array Bool) (fallback : Assignment)
    (valid : Valid store.size gates) :
    bufferEnv (bufferGates gates store fallback) fallback = run gates (bufferEnv store fallback) := by
  induction gates generalizing store with
  | nil => rfl
  | cons gate tail ih =>
    cases valid with
    | cons output _inputs rest =>
      have tailValid : Valid (store.push (gate.eval (bufferEnv store fallback))).size tail := by
        simpa using rest
      change bufferEnv (bufferGates tail (store.push (gate.eval (bufferEnv store fallback))) fallback) fallback = _
      rw [ih _ tailValid, bufferEnv_push]
      change run tail (fun id => if id = store.size then gate.eval (bufferEnv store fallback)
        else bufferEnv store fallback id) = run tail (gate.apply (bufferEnv store fallback))
      apply congrArg (run tail)
      funext id
      change (if id = store.size then gate.eval (bufferEnv store fallback) else bufferEnv store fallback id) =
        (if id = gate.output then gate.eval (bufferEnv store fallback) else bufferEnv store fallback id)
      rw [output]

theorem bufferEnv_initial (next : Nat) (env : Assignment) :
    bufferEnv (Array.ofFn (fun i : Fin next => env i.val)) env = env := by
  funext id
  by_cases before : id < next
  · simp [bufferEnv, before]
  · simp [bufferEnv, before]

/-- Finite fresh execution with constant-depth variable lookup. -/
@[macro_inline] def runBuffered (next : Nat) (gates : List Gate) (env : Assignment) : Assignment :=
  let store := bufferGates gates (Array.ofFn (fun i : Fin next => env i.val)) env
  bufferEnv store env

theorem runBuffered_eq_run (next : Nat) (gates : List Gate)
    (checked : checkProgram next gates = true) (env : Assignment) :
    runBuffered next gates env = run gates env := by
  have valid : Valid (Array.ofFn (fun i : Fin next => env i.val)).size gates := by
    simpa using (checkProgram_iff next gates).mp checked
  rw [runBuffered, Valid.bufferGates_eq _ _ _ valid, bufferEnv_initial]

theorem bufferGates_size (gates : List Gate) (store : Array Bool) (fallback : Assignment) :
    (bufferGates gates store fallback).size = store.size + gates.length := by
  induction gates generalizing store with
  | nil => rfl
  | cons gate tail ih =>
    change (bufferGates tail (store.push (gate.eval (bufferEnv store fallback))) fallback).size = _
    rw [ih, Array.size_push, List.length_cons]
    omega

/-- Buffered execution preserves all original values and constructs every
encoded gate equation. It does not assume a satisfying model. -/
theorem runBuffered_correct (next : Nat) (gates : List Gate)
    (checked : checkProgram next gates = true) (env : Assignment) :
    (∀ id, id < next → runBuffered next gates env id = env id) ∧
      CNF.eval (runBuffered next gates env) (encode gates) = true := by
  rw [runBuffered_eq_run next gates checked]
  have result := ((checkProgram_iff next gates).mp checked).run_correct env
  exact ⟨result.1, (encode_correct _ _).mpr result.2⟩

end TrustIr.AYGateCNF

#trustIrAxiomsPinned TrustIr.AYGateCNF.bufferEnv_push == [Quot.sound, propext, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.Valid.bufferGates_eq == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.bufferEnv_initial == [propext, Quot.sound, Classical.choice]

#trustIrAxiomsExact TrustIr.AYGateCNF.runBuffered_eq_run == [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.bufferGates_size == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsExact TrustIr.AYGateCNF.runBuffered_correct == [propext, Classical.choice, Quot.sound]
