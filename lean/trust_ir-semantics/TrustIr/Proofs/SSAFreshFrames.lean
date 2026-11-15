-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import TrustIr.Semantics.Eval
import TrustIr.Proofs.MemorySafety

namespace TrustIr.SSAFreshFrames

def FreshState (state : MachineState) : Prop :=
  ∀ id, state.nextValueId ≤ id.index → state.lookupValue id = none

theorem cleared_fresh (state : MachineState) :
    FreshState { state with locals := ValueMap.empty, nextValueId := 0 } := by
  intro id _
  rfl

theorem set_fresh (state : MachineState) (dest : ValueId) (value : Value) (next : Nat)
    (fresh : FreshState state) (oldBound : state.nextValueId ≤ next)
    (destBound : dest.index + 1 ≤ next) :
    FreshState { state with locals := state.locals.set dest value, nextValueId := next } := by
  intro id bound
  have different : id ≠ dest := by
    intro same
    subst id
    have impossible := Nat.le_trans destBound bound
    exact Nat.not_succ_le_self dest.index impossible
  simp only [MachineState.lookupValue, ValueMap.get, ValueMap.set]
  simp only [show (id == dest) = false from by simpa using different, Bool.false_eq_true, if_false]
  exact fresh id (Nat.le_trans oldBound bound)

theorem publish_fresh (state : MachineState) (dest : ValueId) (value : Value)
    (fresh : FreshState state) :
    FreshState { state with locals := state.locals.set dest value, nextValueId := max (state.nextValueId + 1) (dest.index + 1) } :=
  set_fresh state dest value _ fresh
    (Nat.le_trans (Nat.le_succ _) (Nat.le_max_left _ _)) (Nat.le_max_right _ _)

private theorem retire_new (state : MachineState) (value : Value) (dest : ValueId)
    (fresh : FreshState state) :
    (if (ValueId.mk state.nextValueId) != dest then
      (fun id => if id == ValueId.mk state.nextValueId then none
        else (state.locals.set (ValueId.mk state.nextValueId) value).set dest value id)
    else (state.locals.set (ValueId.mk state.nextValueId) value).set dest value)
      = state.locals.set dest value := by
  have absent := fresh (ValueId.mk state.nextValueId) (Nat.le_refl _)
  change state.locals (ValueId.mk state.nextValueId) = none at absent
  funext id
  by_cases same : ValueId.mk state.nextValueId = dest
  · by_cases atDest : id = dest <;> simp [same, atDest, ValueMap.set]
  · by_cases atTemporary : id = ValueId.mk state.nextValueId
    · subst id
      simp [same, ValueMap.set, absent]
    · simp [same, atTemporary, ValueMap.set]

theorem bindFresh_publish_run (state : MachineState) (value : Value) (dest : ValueId)
    (fresh : FreshState state) :
    Sem.run (do
      let temporary ← Sem.bindFresh value
      bindInstrResultDests (.value (some temporary)) [dest]) state =
      .ok ((), { state with locals := state.locals.set dest value, nextValueId := max (state.nextValueId + 1) (dest.index + 1) }) := by
  have looked : (state.bindValue value).snd.lookupValue (state.bindValue value).fst = some value := by
    simp [MachineState.bindValue, MachineState.lookupValue, ValueMap.get, ValueMap.set]
  simp only [Sem.run, sr_bind, sr_bindFresh, Except.bind]
  simp only [bindInstrResultDests, sr_bind, sr_lookup, looked, Except.bind]
  simp only [bindResultDests, List.length_cons, List.length_nil, beq_self_eq_true,
    Bool.false_eq_true, bne_self_eq_false, if_false, sr_bind, sr_get, List.zip_cons_cons,
    List.zip_nil_left, List.foldl_cons, List.foldl_nil, sr_set, Except.bind,
    MachineState.bindValue]
  have law := retire_new state value dest fresh
  by_cases different : ((ValueId.mk state.nextValueId) != dest) = true
  · simp only [different, if_true, sr_bind, sr_get, sr_set, Except.bind]
    simp only [different, if_true] at law
    change Except.ok ((), { state with locals := _, nextValueId := max (state.nextValueId + 1) (dest.index + 1) }) = _
    rw [law]
  · simp only [different, Bool.false_eq_true, if_false, sr_pure]
    simp only [different, Bool.false_eq_true, if_false] at law
    change Except.ok ((), { state with locals := _, nextValueId := max (state.nextValueId + 1) (dest.index + 1) }) = _
    rw [law]

private theorem params_fold_fresh (params : List (ValueId × Ty)) (args : List Value)
    (state : MachineState) (fresh : FreshState state) (arity : params.length = args.length) :
    FreshState { state with
      locals := (params.zip args).foldl (fun locals binding => locals.set binding.fst.fst binding.snd) state.locals
      nextValueId := params.foldl (fun next param => max next (param.fst.index + 1)) state.nextValueId } := by
  induction params generalizing args state with
  | nil => simpa only [List.zip_nil_left, List.foldl_nil] using fresh
  | cons param params ih =>
    cases args with
    | nil => simp at arity
    | cons value values =>
      let mid : MachineState := { state with locals := state.locals.set param.fst value, nextValueId := max state.nextValueId (param.fst.index + 1) }
      have middleFresh : FreshState mid :=
        set_fresh state param.fst value _ fresh (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      simpa only [List.zip_cons_cons, List.foldl_cons] using
        ih values mid middleFresh (Nat.succ.inj arity)

theorem bindBlockParams_preserves_fresh (params : List (ValueId × Ty)) (args : List Value)
    (state finalState : MachineState) (fresh : FreshState state)
    (run : Sem.run (bindBlockParams params args) state = .ok ((), finalState)) :
    FreshState finalState := by
  by_cases arity : params.length = args.length
  · simp only [bindBlockParams, arity, bne_self_eq_false, if_false,
      Sem.run, sr_bind, sr_get, sr_set, Except.bind] at run
    have finalEq := congrArg Prod.snd (Except.ok.inj run)
    change { state with
      locals := (params.zip args).foldl (fun locals binding => locals.set binding.fst.fst binding.snd) state.locals
      nextValueId := params.foldl (fun next param => max next (param.fst.index + 1)) state.nextValueId } = finalState at finalEq
    rw [← finalEq]
    exact params_fold_fresh params args state fresh arity
  · have mismatch : (params.length != args.length) = true := by simpa using arity
    simp only [bindBlockParams, mismatch, if_true, Sem.run, sr_throwTE] at run <;> cases run

theorem bindBlockParamsChecked_preserves_fresh (params : List (ValueId × Ty)) (args : List Value)
    (state finalState : MachineState) (fresh : FreshState state)
    (run : Sem.run (bindBlockParamsChecked params args) state = .ok ((), finalState)) :
    FreshState finalState := by
  unfold bindBlockParamsChecked at run
  split at run
  · exact bindBlockParams_preserves_fresh params args state finalState fresh run
  · cases checked : checkSSACharValues (params.map Prod.snd) args with
    | error error => simp only [checked, Sem.run, sr_throw] at run <;> cases run
    | ok unit =>
      cases unit
      simp only [checked] at run
      exact bindBlockParams_preserves_fresh params args state finalState fresh run

end TrustIr.SSAFreshFrames
