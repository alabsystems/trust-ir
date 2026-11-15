-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.GenericCoroPrefixInvokeFrame
import TrustIr.Proofs.SSAFreshStep

namespace TrustIr.GenericCoroAllBlocksInvoke
open GenericCoro GenericCoro.Prefix SSAFreshFrames SSAFreshStep

/-- The actual saved caller frame is restored after return checking or
    from the caught exception's EMBEDDED throw state. The catch computation
    remains opaque. Callee and checker errors are retained exactly. -/
theorem invokeFrameWith_run {α : Type} (strategy : PanicStrategy)
    (check : List Value → Sem Unit) (callee : Sem (List Value))
    (normal : List Value → Sem α) (unwind : Addr → Sem α) (caller : MachineState) :
    Sem.run (invokeFrameWith strategy check callee normal unwind) caller =
      match Sem.run (invokeCatch strategy callee) (callerWorld caller) with
      | .error error => .error error
      | .ok (.inl values, state) =>
        match Sem.run (check values) state with
        | .error error => .error error
        | .ok ((), checked) =>
          Sem.run (normal values) (restoreFrame checked (saveFrame caller none) [])
      | .ok (.inr (exception, thrown), _) =>
        Sem.run (unwind exception) (restoreFrame thrown (saveFrame caller none) []) := by
  change Sem.run (finishInvokeWith strategy check (saveFrame caller none) callee normal unwind)
    (callerWorld caller) = _
  simp only [finishInvokeWith, Sem.run_bind]
  cases caught : Sem.run (invokeCatch strategy callee) (callerWorld caller) with
  | error error => simp only [caught, Except.bind]
  | ok result =>
    rcases result with ⟨outcome, state⟩
    simp only [caught, Except.bind]
    cases outcome with
    | inl values =>
      simp only [finishInvokeReturnWith, Sem.run_bind]
      cases checked : Sem.run (check values) state with
      | error error => simp only [checked, Except.bind]
      | ok result =>
        rcases result with ⟨unit, checkedState⟩
        cases unit
        simp only [checked, Except.bind]
        rfl
    | inr thrown => cases thrown; rfl

/-- Continuations need agree only at fresh states, because BOTH selected
    continuations run after restoring the actual fresh caller frame. Callee
    and checker may return arbitrary SSA maps, fail, or unwind. -/
theorem invokeFrameWith_congr_on_fresh {α : Type} (strategy : PanicStrategy)
    (check : List Value → Sem Unit) (callee : Sem (List Value))
    (sourceNormal targetNormal : List Value → Sem α) (sourceUnwind targetUnwind : Addr → Sem α)
    (normal : ∀ values state, FreshState state →
      Sem.run (sourceNormal values) state = Sem.run (targetNormal values) state)
    (unwind : ∀ exception state, FreshState state →
      Sem.run (sourceUnwind exception) state = Sem.run (targetUnwind exception) state)
    (caller : MachineState) (fresh : FreshState caller) :
    Sem.run (invokeFrameWith strategy check callee sourceNormal sourceUnwind) caller =
      Sem.run (invokeFrameWith strategy check callee targetNormal targetUnwind) caller := by
  rw [invokeFrameWith_run, invokeFrameWith_run]
  cases caught : Sem.run (invokeCatch strategy callee) (callerWorld caller) with
  | error error => rfl
  | ok result =>
    rcases result with ⟨outcome, state⟩
    cases outcome with
    | inl values =>
      dsimp only
      cases checked : Sem.run (check values) state with
      | error error => simp only [checked]
      | ok result =>
        simp only [checked]
        rcases result with ⟨unit, checkedState⟩
        cases unit
        exact normal values _ (restore_empty_fresh checkedState caller none fresh)
    | inr thrown =>
      rcases thrown with ⟨exception, thrownState⟩
      exact unwind exception _ (restore_empty_fresh thrownState caller none fresh)

/-- The paired-CFG induction may retain different private SSA maps in
    continuation results. Equal returned values and complete non-SSA worlds
    suffice; all errors, including embedded unwind states, remain exact. -/
theorem invokeFrameWith_effect_on_fresh (strategy : PanicStrategy)
    (check : List Value → Sem Unit) (callee : Sem (List Value))
    (sourceNormal targetNormal : List Value → Sem (List Value))
    (sourceUnwind targetUnwind : Addr → Sem (List Value))
    (normal : ∀ values state, FreshState state →
      EffectRelation (Sem.run (sourceNormal values) state) (Sem.run (targetNormal values) state))
    (unwind : ∀ exception state, FreshState state →
      EffectRelation (Sem.run (sourceUnwind exception) state) (Sem.run (targetUnwind exception) state))
    (caller : MachineState) (fresh : FreshState caller) :
    EffectRelation
      (Sem.run (invokeFrameWith strategy check callee sourceNormal sourceUnwind) caller)
      (Sem.run (invokeFrameWith strategy check callee targetNormal targetUnwind) caller) := by
  rw [invokeFrameWith_run, invokeFrameWith_run]
  cases caught : Sem.run (invokeCatch strategy callee) (callerWorld caller) with
  | error error => exact .error error
  | ok result =>
    rcases result with ⟨outcome, state⟩
    cases outcome with
    | inl values =>
      dsimp only
      cases checked : Sem.run (check values) state with
      | error error => simp only [checked]; exact .error error
      | ok result =>
        simp only [checked]
        rcases result with ⟨unit, checkedState⟩
        cases unit
        exact normal values _ (restore_empty_fresh checkedState caller none fresh)
    | inr thrown =>
      rcases thrown with ⟨exception, thrownState⟩
      exact unwind exception _ (restore_empty_fresh thrownState caller none fresh)

/-- Successful Invoke preserves freshness when its normal and unwind
    continuations do. Neither the callee nor return checker needs preserve
    freshness: restoration discards their SSA projections before continuing.
    No condition is added to errors, including embedded unwind states. -/
theorem invokeFrameWith_keepsFresh {α : Type} (strategy : PanicStrategy)
    (check : List Value → Sem Unit) (callee : Sem (List Value))
    (normal : List Value → Sem α) (unwind : Addr → Sem α)
    (normalFresh : ∀ values, KeepsFresh (normal values))
    (unwindFresh : ∀ exception, KeepsFresh (unwind exception)) :
    KeepsFresh (invokeFrameWith strategy check callee normal unwind) := by
  trustIrCompilerProof {
    intro caller result fresh run
    rw [invokeFrameWith_run] at run
    cases caught : Sem.run (invokeCatch strategy callee) (callerWorld caller) with
    | error error => simp only [caught] at run
    | ok returned =>
      rcases returned with ⟨outcome, state⟩
      cases outcome with
      | inl values =>
        cases checked : Sem.run (check values) state with
        | error error => simp only [caught, checked] at run
        | ok checkedResult =>
          rcases checkedResult with ⟨unit, checkedState⟩
          cases unit
          apply normalFresh values _ result (restore_empty_fresh checkedState caller none fresh)
          simpa only [caught, checked] using run
      | inr thrown =>
        rcases thrown with ⟨exception, thrownState⟩
        apply unwindFresh exception _ result (restore_empty_fresh thrownState caller none fresh)
        simpa only [caught] using run
  } {
    intro caller result fresh run
    rw [invokeFrameWith_run] at run
    cases caught : Sem.run (invokeCatch strategy callee) (callerWorld caller) with
    | error error =>
      simp only [caught] at run
      cases run
    | ok returned =>
      rcases returned with ⟨outcome, state⟩
      cases outcome with
      | inl values =>
        cases checked : Sem.run (check values) state with
        | error error =>
          simp only [caught, checked] at run
          cases run
        | ok checkedResult =>
          rcases checkedResult with ⟨unit, checkedState⟩
          cases unit
          apply normalFresh values _ result (restore_empty_fresh checkedState caller none fresh)
          simpa only [caught, checked] using run
      | inr thrown =>
        rcases thrown with ⟨exception, thrownState⟩
        apply unwindFresh exception _ result (restore_empty_fresh thrownState caller none fresh)
        simpa only [caught] using run
  }

namespace Controls

/-- Manual Sem controls exercise the general callback contract. The custom
    checker deliberately accepts poison; this is not the production Invoke
    return checker or a validator/native admission claim. -/
def caller : MachineState :=
  { MachineState.empty with
    locals := ValueMap.empty.set ⟨42⟩ (.int 64 99)
    nextValueId := 43
    floatZeroChoiceCursor := 3 }

theorem caller_fresh : FreshState caller := by
  have initial : FreshState MachineState.empty := cleared_fresh MachineState.empty
  have published := set_fresh MachineState.empty ⟨42⟩ (.int 64 99) 43 initial
    (by decide) (by decide)
  exact sameSSA_fresh _ caller published rfl rfl

def corrupt : MachineState :=
  { MachineState.empty with
    locals := ValueMap.empty.set ⟨0⟩ .nullPtr
    nextValueId := 0
    floatZeroChoiceCursor := 17 }

def checkedCorrupt : MachineState := { corrupt with floatZeroChoiceCursor := 23 }

theorem corrupt_is_not_fresh : ¬ FreshState corrupt := by
  intro fresh
  have impossible := fresh ⟨0⟩ (Nat.le_refl _)
  cases impossible

def returning : Sem (List Value) := do
  Sem.setState corrupt
  pure [.undef .I64]

def checker (_values : List Value) : Sem Unit := Sem.setState checkedCorrupt

def normal (values : List Value) : Sem (List Value) := pure values

def unwind (exception : Addr) : Sem (List Value) := pure [.int 64 (Int.ofNat exception)]

theorem poison_return_nonfresh_check_restores_complete_caller_frame :
    Sem.run (invokeFrameWith .unwind checker returning normal unwind) caller =
      .ok ([.undef .I64], { checkedCorrupt with locals := caller.locals, nextValueId := caller.nextValueId }) := by
  rw [invokeFrameWith_run, invokeCatch_run]
  rfl

theorem caught_unwind_restores_from_embedded_throw_world :
    Sem.run (invokeFrameWith .unwind checker
      (throw (.unwinding 9 corrupt)) normal unwind) caller =
      .ok ([.int 64 9], { corrupt with locals := caller.locals, nextValueId := caller.nextValueId }) := by
  rw [invokeFrameWith_run, invokeCatch_run]
  rfl

theorem abort_keeps_exact_unwind_error_state :
    Sem.run (invokeFrameWith .abort checker
      (throw (.unwinding 9 corrupt)) normal unwind) caller = .error (.unwinding 9 corrupt) := by
  rw [invokeFrameWith_run, invokeCatch_run]
  rfl

theorem checker_unwind_is_not_caught_as_callee_unwind :
    Sem.run (invokeFrameWith .unwind (fun _ => throw (.unwinding 11 checkedCorrupt))
      returning normal unwind) caller = .error (.unwinding 11 checkedCorrupt) := by
  rw [invokeFrameWith_run, invokeCatch_run]
  rfl

theorem callee_resource_error_is_exact :
    Sem.run (invokeFrameWith .unwind checker
      (throw .outOfFuel) normal unwind) caller = .error .outOfFuel := by
  rw [invokeFrameWith_run, invokeCatch_run]
  rfl

theorem nonfresh_callee_and_checker_still_keep_fresh :
    KeepsFresh (invokeFrameWith .unwind checker returning normal unwind) :=
  invokeFrameWith_keepsFresh _ _ _ _ _ (fun _ => pure_fresh _) (fun _ => pure_fresh _)

def privateResult (values : List Value) : Sem (List Value) := do
  let _ ← Sem.bindFresh .nullPtr
  pure values

theorem privateResult_effect (values : List Value) (state : MachineState) :
    EffectRelation (Sem.run (pure values : Sem (List Value)) state)
      (Sem.run (privateResult values) state) :=
  .returned values state (state.bindValue .nullPtr).snd rfl

/-- The actual consumer uses the effect law, retaining a target-only SSA
    binding while preserving returned values and every non-SSA world field. -/
theorem continuation_private_result_effect :
    EffectRelation
      (Sem.run (invokeFrameWith .unwind checker returning normal unwind) caller)
      (Sem.run (invokeFrameWith .unwind checker returning privateResult
        (fun exception => privateResult [.int 64 (Int.ofNat exception)])) caller) :=
  invokeFrameWith_effect_on_fresh .unwind checker returning _ _ _ _
    (fun values state _ => privateResult_effect values state)
    (fun exception state _ => privateResult_effect [.int 64 (Int.ofNat exception)] state)
    caller caller_fresh

end Controls

end TrustIr.GenericCoroAllBlocksInvoke
