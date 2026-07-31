-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Phase 5 transformation correctness framework: definitions and theorems
-- for proving that compiler transformations preserve TrustIr semantics.
-- TrustCg instantiates these frameworks for specific optimization passes.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 6 Phase 5
-- Reference: Leroy, "A formally verified compiler back-end", J. Automated Reasoning, 2009

import TrustIr.Semantics.Eval
import TrustIr.Proofs.CallProps

namespace TrustIr

/-!
# Transformation Correctness Framework (Phase 5)

This module defines FRAMEWORKS for proving that compiler transformations
preserve TrustIr semantics. These are not proofs about specific optimizations;
they are the reusable infrastructure that TrustCg instantiates.

## Key definitions

1. **semantics_preserving**: Strong preservation -- same fuel, same result.
2. **semantics_preserving_weak**: Weak preservation -- may need different fuel.
3. **inst_equiv**: Two instructions produce the same result on all states.
4. **instructions_commute**: Two instructions can be reordered.
5. **state_equiv_except_locals**: States agree except for SSA bindings.

## Framework theorems

1. Constant folding correctness (inst_equiv for BinOp vs Const)
2. Dead code elimination (pure instructions preserve non-local state)
3. Instruction reordering (pure non-aliasing instructions commute)
4. Block-level transform lifting (instruction transforms lift to blocks)
5. Inlining correctness, frame-discipline form (a Call succeeds iff the
   callee body run inline on a fresh frame succeeds with the same values)

## Design note

These frameworks follow the CompCert/Vellvm pattern: define semantic
equivalence abstractly, then instantiate for specific passes. TrustCg
provides the pass-specific details; TrustIr provides the semantic framework.
-/

-- =================================================================
-- Semantic equivalence definitions
-- =================================================================

/-- Strong semantic preservation: a CFG transform preserves the
    exact result for every initial state, fuel, entry point, and args.

    This is the strongest form of correctness. It implies the
    transformed program has exactly the same observable behavior. -/
def semantics_preserving (transform : CFG -> CFG) : Prop :=
  forall cfg pc args s fuel result,
    Sem.run (stepN fuel cfg pc args) s = .ok result ->
    Sem.run (stepN fuel (transform cfg) pc args) s = .ok result

/-- Weak semantic preservation: the transformed program produces the
    same result, but may need different fuel.

    This is appropriate for optimizations that change the number of
    basic blocks or loop structure (e.g., loop unrolling). -/
def semantics_preserving_weak (transform : CFG -> CFG) : Prop :=
  forall cfg pc args s result,
    (exists fuel, Sem.run (stepN fuel cfg pc args) s = .ok result) ->
    (exists fuel', Sem.run (stepN fuel' (transform cfg) pc args) s = .ok result)

/-- Two instructions are equivalent if they produce the same result
    on every machine state. -/
def inst_equiv (i1 i2 : Inst) : Prop :=
  forall s, Sem.run (stepInst i1) s = Sem.run (stepInst i2) s

/-- Instruction equivalence is reflexive. -/
theorem inst_equiv_refl (i : Inst) : inst_equiv i i := by
  intro s; rfl

/-- Instruction equivalence is symmetric. -/
theorem inst_equiv_symm (i1 i2 : Inst) (h : inst_equiv i1 i2) :
    inst_equiv i2 i1 := by
  intro s; exact (h s).symm

/-- Instruction equivalence is transitive. -/
theorem inst_equiv_trans (i1 i2 i3 : Inst)
    (h12 : inst_equiv i1 i2) (h23 : inst_equiv i2 i3) :
    inst_equiv i1 i3 := by
  intro s; exact (h12 s).trans (h23 s)

-- =================================================================
-- Constant folding framework
-- =================================================================

/-- Constant folding: if an instruction is equivalent to a Const
    instruction for all states, then replacing it with the Const
    is semantics-preserving at the instruction level.

    TrustCg instantiates this by:
    1. Evaluating the BinOp on known constant inputs
    2. Checking the result matches a Const instruction
    3. Applying this theorem to justify the replacement -/
theorem constant_fold_sound (i1 : Inst) (ty : Ty) (result : Constant)
    (hEquiv : inst_equiv i1 (.Const ty result)) :
    forall s, Sem.run (stepInst i1) s = Sem.run (stepInst (.Const ty result)) s :=
  hEquiv

/-- Framework for proving a BinOp on constants folds to a Const.
    If we can show the BinOp produces the same result as the Const
    on all states, the fold is justified. -/
theorem constant_fold_binop (op : BinOp) (ty : Ty) (lhs rhs : ValueId)
    (constResult : Constant)
    (hFold : inst_equiv (.BinOp op ty lhs rhs) (.Const ty constResult)) :
    inst_equiv (.BinOp op ty lhs rhs) (.Const ty constResult) :=
  hFold

-- =================================================================
-- Dead code elimination framework
-- =================================================================

/-- Two states are equivalent except for local SSA bindings.
    Memory, permissions, and refcounts are identical. -/
def state_equiv_except_locals (s1 s2 : MachineState) : Prop :=
  s1.memory = s2.memory /\
  s1.permissions = s2.permissions /\
  s1.refCounts = s2.refCounts

/-- state_equiv_except_locals is reflexive. -/
theorem state_equiv_except_locals_refl (s : MachineState) :
    state_equiv_except_locals s s := by
  exact And.intro rfl (And.intro rfl rfl)

/-- state_equiv_except_locals is symmetric. -/
theorem state_equiv_except_locals_symm (s1 s2 : MachineState)
    (h : state_equiv_except_locals s1 s2) :
    state_equiv_except_locals s2 s1 := by
  obtain ⟨hMem, hPerm, hRef⟩ := h
  exact ⟨hMem.symm, hPerm.symm, hRef.symm⟩

/-- state_equiv_except_locals is transitive. -/
theorem state_equiv_except_locals_trans (s1 s2 s3 : MachineState)
    (h12 : state_equiv_except_locals s1 s2)
    (h23 : state_equiv_except_locals s2 s3) :
    state_equiv_except_locals s1 s3 := by
  obtain ⟨hMem12, hPerm12, hRef12⟩ := h12
  obtain ⟨hMem23, hPerm23, hRef23⟩ := h23
  exact ⟨hMem12.trans hMem23, hPerm12.trans hPerm23, hRef12.trans hRef23⟩

/-- Sem.bindFresh preserves nonlocal state: the output state has the
    same memory, permissions, and refCounts as the input state. -/
theorem bindFresh_nonlocal_eq (v : Value) (s : MachineState)
    (r : ValueId × MachineState)
    (h : Sem.run (Sem.bindFresh v) s = .ok r) :
    state_equiv_except_locals s r.snd := by
  simp only [Sem.bindFresh, Sem.run, StateT.run, Sem.getState, Sem.setState,
             StateT.get, StateT.set, MachineState.bindValue,
             bind, StateT.bind, Except.bind,
             pure, StateT.pure, Except.ok.injEq] at h
  constructor
  · cases h; rfl
  constructor
  · cases h; rfl
  · cases h; rfl

/-- Dead code elimination for pure instructions: if an instruction has
    no side effects and is not a terminator, executing it only changes
    local SSA bindings (via bindFresh). Memory, permissions, and refcounts
    are preserved.

    This justifies removing the instruction if its result is unused.

    The proof uses a compositional approach: define "preserves nonlocal
    state" (pnl) and show that the monadic primitives (lookupValue,
    bindFresh, getState, pure, throw) all preserve it, and that bind
    preserves the property transitively. Then each pure instruction's
    semantics is decomposed into these primitives. -/

-- Compositional framework for proving nonlocal state preservation.
-- A Sem computation "preserves nonlocal" if, whenever it succeeds,
-- the result state has the same memory, permissions, and refCounts.
private def pnl {a : Type} (m : Sem a) : Prop :=
  forall s result, Sem.run m s = .ok result ->
    result.snd.memory = s.memory /\
    result.snd.permissions = s.permissions /\
    result.snd.refCounts = s.refCounts

-- Monadic bind preserves nonlocal state: if ma and f both preserve it,
-- then (ma >>= f) does too. The transitivity of field equalities
-- chains through the intermediate state.
private theorem bind_pnl {a b : Type} (ma : Sem a) (f : a -> Sem b)
    (hma : pnl ma) (hf : forall x, pnl (f x)) : pnl (ma >>= f) := by
  intro s result hRun
  simp only [Sem.run, StateT.run, bind, StateT.bind, Except.bind] at hRun
  cases hma_run : (ma s) with
  | error e => simp [hma_run] at hRun
  | ok val =>
    simp only [hma_run] at hRun; obtain ⟨a_val, s'⟩ := val; simp only [] at hRun
    have h1 := hma s (a_val, s') (by simp [Sem.run, StateT.run, hma_run])
    simp only [] at h1
    have h2 := hf a_val s' result (by simp [Sem.run, StateT.run]; exact hRun)
    exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

-- lookupValue: reads locals but never modifies any state field.
private theorem lv_pnl (id : ValueId) : pnl (Sem.lookupValue id) := by
  intro s result hRun
  simp only [Sem.run, Sem.lookupValue, Sem.getState, StateT.run, StateT.get,
        MachineState.lookupValue, bind, StateT.bind, Except.bind, pure, Except.pure] at hRun
  cases h : s.locals.get id with
  | none => exfalso; revert hRun; simp only [h]; exact nofun
  | some v => revert hRun; simp only [h]; intro hRun
              change Except.ok (v, s) = _ at hRun
              rw [<- Except.ok.inj hRun]; exact ⟨rfl, rfl, rfl⟩

-- bindFresh: modifies only locals and nextValueId.
private theorem bf_pnl (v : Value) : pnl (Sem.bindFresh v) := by
  intro s result hRun
  simp only [Sem.run, Sem.bindFresh, Sem.getState, Sem.setState,
        StateT.run, StateT.get, StateT.set, MachineState.bindValue,
        bind, StateT.bind, Except.bind, pure, Except.pure] at hRun
  have h := Except.ok.inj hRun; subst h; exact ⟨rfl, rfl, rfl⟩

-- pure: returns value without modifying state.
private theorem p_pnl {α : Type} (x : α) : pnl (pure x : Sem α) := by
  intro s result hRun
  simp only [Sem.run, StateT.run, pure, Except.pure] at hRun
  have h := Except.ok.inj hRun; subst h; exact ⟨rfl, rfl, rfl⟩

-- throw: always errors, so preserves nonlocal vacuously.
private theorem t_pnl {α : Type} (e : SemError) : pnl (throw e : Sem α) := by
  intro s result hRun
  have : (throw e : Sem α) s = Except.error e := rfl
  simp [Sem.run, StateT.run, this] at hRun

-- getState: reads state without modification.
private theorem gs_pnl : pnl (Sem.getState : Sem MachineState) := by
  intro s result hRun
  simp only [Sem.run, Sem.getState, StateT.run, StateT.get, pure, Except.pure] at hRun
  have h := Except.ok.inj hRun; subst h; exact ⟨rfl, rfl, rfl⟩

-- if-then-else preserves pnl when both branches do.
-- Handles the join-point pattern in do-notation where if/match
-- duplicates the continuation into both branches.
private theorem ite_pnl {α : Type} {c : Prop} [Decidable c] {t e : Sem α}
    (ht : pnl t) (he : pnl e) : pnl (if c then t else e) := by
  intro s result hRun
  cases Decidable.em c with
  | inl h => simp [h] at hRun; exact ht s result hRun
  | inr h => simp [h] at hRun; exact he s result hRun

-- Bool-indexed if-then-else preserves pnl when both branches do.
-- Lean's do-notation "if b then X" with no else elaborates to
-- if b then X else pure () where b is Bool. This requires a Bool ite
-- lemma, not the Prop/Decidable one above.
private theorem bool_ite_pnl {α : Type} (b : Bool) {t e : Sem α}
    (ht : pnl t) (he : pnl e) : pnl (if b then t else e) := by
  cases b with
  | true  => simp; exact ht
  | false => simp; exact he

-- Helper for stepInst cases that call a semantic function then wrap in InstrResult.
private theorem sem_value_pnl {f : Sem ValueId} (hf : pnl f) :
    pnl (do let vid ← f; pure (InstrResult.value (some vid))) :=
  bind_pnl f _ hf (fun _ => p_pnl _)

-- Helper for stepInst cases that call a Sem Unit then wrap in InstrResult.
private theorem sem_unit_pnl {f : Sem Unit} (hf : pnl f) :
    pnl (do f; pure (InstrResult.value none)) :=
  bind_pnl f _ hf (fun _ => p_pnl _)

-- Bridge from pnl to state_equiv_except_locals for stepInst proofs.
private theorem pnl_to_sel {m : Sem InstrResult} (hpnl : pnl m)
    (s : MachineState) (result : InstrResult × MachineState)
    (hOk : Sem.run m s = .ok result) :
    state_equiv_except_locals s result.snd := by
  have ⟨hMem, hPerm, hRef⟩ := hpnl s result hOk
  exact ⟨hMem.symm, hPerm.symm, hRef.symm⟩

-- match on Except result: if .ok, continue; if .error, contradiction
private theorem except_ok_bind {α β : Type} {e : Except SemError α}
    {f : α → Except SemError β} {r : β}
    (h : Except.bind e f = .ok r) :
    ∃ a, e = .ok a ∧ f a = .ok r := by
  cases e with
  | ok a => exact ⟨a, rfl, h⟩
  | error err => exact absurd h nofun

-- Sem computation from an Except result: pure on ok, throw on error.
-- This pattern occurs frequently in semantic functions where a pure
-- computation (e.g., semIntBinOp) returns Except and the result is
-- fed into bindFresh or throw.
private theorem except_lift_pnl {α : Type} (e : Except SemError α)
    (onOk : α → Sem ValueId) (hOnOk : forall x, pnl (onOk x)) :
    pnl (match e with
      | .ok v => onOk v
      | .error err => throw err) := by
  cases e with
  | ok v => exact hOnOk v
  | error err => exact t_pnl err

-- throw applied to a state reduces to Except.error.
-- Used as a simp lemma for Sem.run-level proofs where throw
-- appears after partial evaluation of the monadic computation.
@[simp] private theorem throw_sem_apply {α : Type} (e : SemError) (s : MachineState) :
    (throw e : Sem α) s = Except.error e := rfl

-- StateT.pure applied to a state reduces to Except.ok.
@[simp] private theorem stateT_pure_apply {α : Type} (x : α) (s : MachineState) :
    (StateT.pure x : Sem α) s = Except.ok (x, s) := rfl

-- StateT.bind with throw on the left reduces to Except.error.
-- This handles the common pattern where throw appears inside a bind chain.
@[simp] private theorem stateT_bind_throw {α β : Type}
    (e : SemError) (f : α -> Sem β) (s : MachineState) :
    StateT.bind (throw e : Sem α) f s = Except.error e := rfl

-- StateT.bind with pure on the left reduces by applying f to the value.
@[simp] private theorem stateT_bind_pure {α β : Type}
    (x : α) (f : α -> Sem β) (s : MachineState) :
    StateT.bind (StateT.pure x : Sem α) f s = f x s := rfl

-- StateT.get.bind f s reduces to f s s.
@[simp] private theorem stateT_get_bind {β : Type}
    (f : MachineState -> Sem β) (s : MachineState) :
    StateT.get.bind f s = f s s := rfl

-- Convenience accessors for each throw helper as a pnl fact.
-- Used to discharge error branches uniformly regardless of which
-- throwing helper (throwUB / throwTypeError / throwPanic) is invoked.
private theorem throwUB_pnl {α : Type} (msg : String) : pnl (Sem.throwUB msg : Sem α) := by
  unfold Sem.throwUB; exact t_pnl _

private theorem throwTypeError_pnl {α : Type} (msg : String) : pnl (Sem.throwTypeError msg : Sem α) := by
  unfold Sem.throwTypeError; exact t_pnl _

private theorem throwUnsupported_pnl {α : Type}
    (feature : UnsupportedFeature) (msg : String) :
    pnl (Sem.throwUnsupported feature msg : Sem α) := by
  unfold Sem.throwUnsupported; exact t_pnl _

private theorem throwPanic_pnl {α : Type} (msg : String) : pnl (Sem.throwPanic msg : Sem α) := by
  unfold Sem.throwPanic; exact t_pnl _

-- The copy-propagates-poison guard preserves nonlocal state: it either throws
-- (poison operand) or is a pure no-op, both of which leave memory / permissions
-- / refCounts untouched.
private theorem rejectPartial_pnl (v : Value) (op : String) :
    pnl (Sem.rejectPartial v op) := by
  cases v <;>
    first
      | exact throwUB_pnl _
      | exact p_pnl _

-- pnl for match e with  .ok v => Sem.bindFresh (f v)  .error err => throw err.
-- This is the dominant shape after integer/float dispatch in arithmetic/overflow ops.
private theorem except_bindFresh_pnl {α : Type}
    (e : Except SemError α) (f : α -> Value) :
    pnl (match e with
          | .ok v     => Sem.bindFresh (f v)
          | .error err => throw err) := by
  cases e with
  | ok v     => exact bf_pnl (f v)
  | error err => exact t_pnl err

-- pnl for if c then throw else m, used in width-mismatch checks.
private theorem ite_throw_pnl {α : Type} {c : Prop} [Decidable c]
    (msg : String) {m : Sem α} (hm : pnl m) :
    pnl (if c then Sem.throwTypeError msg else m) := by
  cases Decidable.em c with
  | inl h => simp [h]; exact throwTypeError_pnl _
  | inr h => simp [h]; exact hm

private theorem vectorBinOpDispatch_pnl (op : BinOp) (ty : Ty)
    (lhs rhs : List Value) :
    pnl (match ty.executableIntVectorWidth? with
      | some (lanes, width) =>
        if lhs.length != lanes || rhs.length != lanes then
          Sem.throwTypeError "Vector BinOp: lane count does not match type"
        else
          match semVectorIntBinOp op width lhs rhs with
          | .ok result => Sem.bindFresh (.vector result)
          | .error e   => throw e
      | none => Sem.throwUnsupported .vectorType
          s!"Vector BinOp: unsupported vector type {repr ty}") := by
  cases ty.executableIntVectorWidth? with
  | none => exact throwUnsupported_pnl _ _
  | some p =>
    obtain ⟨lanes, width⟩ := p
    refine ite_throw_pnl _ ?_
    cases semVectorIntBinOp op width lhs rhs with
    | ok result => exact bf_pnl _
    | error e => exact t_pnl e

private theorem vectorICmpDispatch_pnl (op : ICmpOp) (ty : Ty)
    (lhs rhs : List Value) :
    pnl (match ty.executableIntVectorWidth? with
      | some (lanes, width) =>
        if lhs.length != lanes || rhs.length != lanes then
          Sem.throwTypeError "Vector ICmp: lane count does not match type"
        else
          match semVectorICmp op width lhs rhs with
          | .ok result => Sem.bindFresh (.vector result)
          | .error e   => throw e
      | none => Sem.throwUnsupported .vectorType
          s!"Vector ICmp: unsupported vector type {repr ty}") := by
  cases ty.executableIntVectorWidth? with
  | none => exact throwUnsupported_pnl _ _
  | some p =>
    obtain ⟨lanes, width⟩ := p
    refine ite_throw_pnl _ ?_
    cases semVectorICmp op width lhs rhs with
    | ok result => exact bf_pnl _
    | error e => exact t_pnl e

private theorem vectorSelectValue_pnl (ty : Ty) (mask : List Value)
    (thenVal elseVal : ValueId) :
    pnl (match ty.executableVectorLanes? with
      | some lanes =>
        if mask.length != lanes then
          Sem.throwTypeError "Vector Select: mask lane count does not match type"
        else do
          let thenV ← Sem.lookupValue thenVal
          let elseV ← Sem.lookupValue elseVal
          match thenV, elseV with
          | .vector thenLanes, .vector elseLanes =>
            let thenOk := ty.executableVectorPayloadMatches thenLanes
            let elseOk := ty.executableVectorPayloadMatches elseLanes
            if thenOk && elseOk then
              match semVectorSelectLanes mask thenLanes elseLanes with
              | .ok result => pure (Value.vector result)
              | .error e   => throw e
            else
              Sem.throwTypeError "Vector Select: value lanes do not match vector type"
          | _, _ => Sem.throwTypeError "Vector Select: vector mask with non-vector values"
      | none => Sem.throwUnsupported .vectorType
          s!"Vector Select: unsupported vector type {repr ty}") := by
  cases ty.executableVectorLanes? with
  | none => exact throwUnsupported_pnl _ _
  | some lanes =>
    refine ite_throw_pnl _ ?_
    refine bind_pnl _ _ (lv_pnl thenVal) ?_; intro thenV
    refine bind_pnl _ _ (lv_pnl elseVal) ?_; intro elseV
    cases thenV <;> cases elseV <;> simp only [] <;>
      first
        | (refine ite_pnl ?_ ?_
           · cases semVectorSelectLanes mask _ _ with
             | ok result => exact p_pnl (Value.vector result)
             | error e => exact t_pnl e
           · exact throwTypeError_pnl _)
        | exact throwTypeError_pnl _

private theorem stepSelect_pnl (ty : Ty) (cond thenVal elseVal : ValueId) :
    pnl (stepInst (.Select ty cond thenVal elseVal)) := by
  unfold stepInst
  refine bind_pnl _ _ (lv_pnl cond) ?_; intro condV
  refine bind_pnl _ _ (rejectPartial_pnl condV "Select") ?_; intro _
  have tail : forall chosen, pnl (do
      let vid ← Sem.bindFresh chosen
      pure (InstrResult.value (some vid))) := by
    intro chosen
    exact bind_pnl _ _ (bf_pnl _) (fun _ => p_pnl _)
  cases condV with
  | bool b =>
    cases b with
    | true => exact bind_pnl _ _ (lv_pnl thenVal) tail
    | false => exact bind_pnl _ _ (lv_pnl elseVal) tail
  | vector mask =>
    cases ty.executableVectorLanes? with
    | none =>
      exact bind_pnl _ _ (throwUnsupported_pnl _ _) tail
    | some lanes =>
      refine ite_pnl ?_ ?_
      · exact bind_pnl _ _ (throwTypeError_pnl _) tail
      · refine bind_pnl _ _ (lv_pnl thenVal) ?_; intro thenV
        refine bind_pnl _ _ (lv_pnl elseVal) ?_; intro elseV
        cases thenV <;> cases elseV <;> simp only [] <;>
          first
            | (refine ite_pnl ?_ ?_
               · cases semVectorSelectLanes mask _ _ with
                 | ok result => exact bind_pnl _ _ (p_pnl (Value.vector result)) tail
                 | error e => exact bind_pnl _ _ (t_pnl e) tail
               · exact bind_pnl _ _ (throwTypeError_pnl _) tail)
            | exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | nullPtr =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | int w v =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | float f =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | ptr a =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | aggregate fields =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | frame f =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | set xs =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | sequence xs =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | record fs =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | closure f caps =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | fatPtr d m =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | «partial» img =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | undef t =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail

-- pnl for semBindSlot: lookupValue, lookupValue, match bindSlot, throw or bindFresh.
-- Success branch uses bf_pnl; both error branches are throw which is pnl vacuously.
private theorem semBindSlot_pnl (frameId : ValueId) (slot : Nat) (valueId : ValueId) :
    pnl (semBindSlot frameId slot valueId) := by
  unfold semBindSlot
  exact bind_pnl _ _ (lv_pnl frameId) fun frameVal =>
    bind_pnl _ _ (lv_pnl valueId) fun newVal => by
      cases h : bindSlot frameVal slot newVal with
      | some v => simp [h]; exact bf_pnl v
      | none =>
        simp [h]
        cases frameVal <;>
          first
            | (unfold Sem.throwUB; exact t_pnl _)
            | (unfold Sem.throwTypeError; exact t_pnl _)

-- pnl for semLoadSlot lookup value match loadSlot throw bindFresh.
private theorem semLoadSlot_pnl (frameId : ValueId) (slot : Nat) (ty : Ty) :
    pnl (semLoadSlot frameId slot ty) := by
  unfold semLoadSlot
  exact bind_pnl _ _ (lv_pnl frameId) fun frameVal => by
    cases h : loadSlot frameVal slot with
    | some v => simp [h]; exact bf_pnl v
    | none =>
      simp [h]
      cases frameVal <;>
        first
          | (unfold Sem.throwUB; exact t_pnl _)
          | (unfold Sem.throwTypeError; exact t_pnl _)

-- =================================================================
-- pnl lemmas for pure non-terminator instructions (Phase 5)
-- =================================================================

-- Arithmetic: BinOp follows lookupValue, lookupValue, match types, bindFresh.
private theorem semBinOp_pnl (op : BinOp) (ty : Ty) (lhsId rhsId : ValueId) :
    pnl (semBinOp op ty lhsId rhsId) := by
  unfold semBinOp
  exact bind_pnl _ _ (lv_pnl lhsId) fun lhsVal =>
    bind_pnl _ _ (lv_pnl rhsId) fun rhsVal =>
    bind_pnl _ _ (rejectPartial_pnl lhsVal "BinOp") fun _ =>
    bind_pnl _ _ (rejectPartial_pnl rhsVal "BinOp") fun _ => by
      cases lhsVal <;> cases rhsVal <;> simp only [] <;>
        first
          | exact vectorBinOpDispatch_pnl op ty _ _
          | exact throwTypeError_pnl _
          | (refine ite_throw_pnl _ ?_
             cases semIntBinOp op _ _ _ with
             | ok result  => exact bf_pnl _
             | error e    => exact t_pnl e)
          | (cases semFloatBinOp op _ _ with
              | ok result  => exact bf_pnl _
              | error e    => exact t_pnl e)

private theorem semUnOp_pnl (op : UnOp) (ty : Ty) (operandId : ValueId) :
    pnl (semUnOp op ty operandId) := by
  unfold semUnOp
  exact bind_pnl _ _ (lv_pnl operandId) fun operand =>
    bind_pnl _ _ (rejectPartial_pnl operand "UnOp") fun _ => by
    cases operand <;> simp only [] <;>
      first
        | exact throwTypeError_pnl _
        | (cases semIntUnOp op _ _ with
            | ok result  => exact bf_pnl _
            | error e    => exact t_pnl e)
        | (cases semFloatUnOp op _ with
            | ok result  => exact bf_pnl _
            | error e    => exact t_pnl e)

private theorem semOverflow_pnl (op : OverflowOp) (ty : Ty) (lhsId rhsId : ValueId) :
    pnl (semOverflow op ty lhsId rhsId) := by
  unfold semOverflow
  exact bind_pnl _ _ (lv_pnl lhsId) fun lhsVal =>
    bind_pnl _ _ (lv_pnl rhsId) fun rhsVal =>
    bind_pnl _ _ (rejectPartial_pnl lhsVal "OverflowOp") fun _ =>
    bind_pnl _ _ (rejectPartial_pnl rhsVal "OverflowOp") fun _ => by
      cases lhsVal <;> cases rhsVal <;> simp only [] <;>
        first
          | exact throwTypeError_pnl _
          | (refine ite_throw_pnl _ ?_
             cases h : semOverflowOp op _ _ _ _ with
             | ok p       => obtain ⟨result, flag⟩ := p; simp only []; exact bf_pnl _
             | error e    => exact t_pnl e)

-- Comparisons: ICmpInst, FCmpInst
-- Shape: lookupValue then lookupValue then match operand types then bindFresh or throw.

private theorem semICmpInst_pnl (op : ICmpOp) (ty : Ty) (lhsId rhsId : ValueId) :
    pnl (semICmpInst op ty lhsId rhsId) := by
  unfold semICmpInst
  exact bind_pnl _ _ (lv_pnl lhsId) fun lhsVal =>
    bind_pnl _ _ (lv_pnl rhsId) fun rhsVal =>
    bind_pnl _ _ (rejectPartial_pnl lhsVal "ICmp") fun _ =>
    bind_pnl _ _ (rejectPartial_pnl rhsVal "ICmp") fun _ => by
      cases lhsVal <;> cases rhsVal <;> simp only [] <;>
        first
          | exact vectorICmpDispatch_pnl op ty _ _
          | exact throwTypeError_pnl _
          | (refine ite_throw_pnl _ ?_; exact bf_pnl _)

private theorem semFCmpInst_pnl (op : FCmpOp) (ty : Ty) (lhsId rhsId : ValueId) :
    pnl (semFCmpInst op ty lhsId rhsId) := by
  unfold semFCmpInst
  exact bind_pnl _ _ (lv_pnl lhsId) fun lhsVal =>
    bind_pnl _ _ (lv_pnl rhsId) fun rhsVal =>
    bind_pnl _ _ (rejectPartial_pnl lhsVal "FCmp") fun _ =>
    bind_pnl _ _ (rejectPartial_pnl rhsVal "FCmp") fun _ => by
      cases lhsVal <;> cases rhsVal <;> simp only [] <;>
        first
          | exact throwTypeError_pnl _
          | exact bf_pnl _

-- Cast: lookupValue, then per-op match on operand, optional getTyWidth, bindFresh/throw.
-- The 12 cast variants each follow: either
--   (a) typeError on wrong operand type,
--   (b) bindFresh directly (FPTrunc, FPExt, UIToFP, SIToFP, IntToPtr),
--   (c) match getTyWidth with ok then bindFresh / error then throw,
--   (d) Bitcast: nested if dstTy Ptr branch.
-- Helper: an Except SemError Nat matching block that lands in bindFresh (f v)
-- on the ok branch. Used by most getTyWidth-threading variants.
private theorem match_width_bindFresh_pnl
    (e : Except SemError Nat) (f : Nat -> Value) :
    pnl (match e with
          | .ok w => Sem.bindFresh (f w)
          | .error err => throw err) := by
  cases e with
  | ok w => exact bf_pnl (f w)
  | error err => exact t_pnl err

-- Helper: like `match_width_bindFresh_pnl` but the ok-branch is GUARDED by a
-- boolean UB check (`if cond w then throwUB else bindFresh (f w)`). Used by the
-- FPToUI/FPToSI casts, whose NaN/out-of-range inputs trap as UB (matching the
-- Rust reference interpreter and docs/ub-numerics-policy.md §2). Both the throw
-- and the bindFresh preserve nonlocal state, so the whole shape is pnl.
private theorem match_width_guarded_pnl
    (e : Except SemError Nat) (cond : Nat -> Bool) (msg : String) (f : Nat -> Value) :
    pnl (match e with
          | .ok w => if cond w then Sem.throwUB msg else Sem.bindFresh (f w)
          | .error err => throw err) := by
  cases e with
  | ok w => exact bool_ite_pnl (cond w) (throwUB_pnl msg) (bf_pnl (f w))
  | error err => exact t_pnl err

-- Helper: pnl for the Bitcast int-to-dst branch: ite on (dstTy == .Ptr).
private theorem bitcast_int_pnl (_w : Nat) (v : Int) (dstTy : Ty) :
    pnl (if dstTy == .Ptr then Sem.bindFresh (.ptr v.toNat)
         else match getTyWidth dstTy with
              | .ok dstW  => Sem.bindFresh (.int dstW v)
              | .error e  => throw e) := by
  exact ite_pnl (bf_pnl _) (match_width_bindFresh_pnl _ _)

-- Integer truncation has one representation-changing scalar boundary:
-- destination Bool materializes the low bit as Value.bool.  Keep that branch
-- explicit so adding a new scalar destination cannot silently inherit it.
private theorem trunc_int_pnl (v : Int) (dstTy : Ty) :
    pnl (if dstTy == .Bool then
           Sem.bindFresh (.bool (truncateUnsigned v 1 == 1))
         else
           match getTyWidth dstTy with
           | .ok dstW => Sem.bindFresh (.int dstW (truncateUnsigned v dstW))
           | .error e => throw e) := by
  exact bool_ite_pnl _ (bf_pnl _) (match_width_bindFresh_pnl _ _)

-- Bool is the one-bit integer source for zero extension.  Prove false and
-- true separately: this makes the 0/1 encoding visible at the proof boundary.
private theorem zext_bool_pnl (b : Bool) (dstTy : Ty) :
    pnl (match getTyWidth dstTy with
         | .ok dstW => Sem.bindFresh (.int dstW (if b then 1 else 0))
         | .error e => throw e) := by
  cases b with
  | false => exact match_width_bindFresh_pnl _ _
  | true => exact match_width_bindFresh_pnl _ _

-- Bool is also a signed one-bit source.  In particular, the explicit true
-- branch proves that its sign extension is -1 modulo the destination width
-- (all destination bits set), rather than the zero-extension value 1.
private theorem sext_bool_pnl (b : Bool) (dstTy : Ty) :
    pnl (match getTyWidth dstTy with
         | .ok dstW =>
           let signed : Int := if b then -1 else 0
           let modulus := (2 : Int) ^ dstW
           let wrapped := ((signed % modulus) + modulus) % modulus
           Sem.bindFresh (.int dstW wrapped)
         | .error e => throw e) := by
  cases b with
  | false => exact match_width_bindFresh_pnl _ _
  | true => exact match_width_bindFresh_pnl _ _

-- All cast cases terminate in bindFresh or throw (both pnl).  We case on op
-- to select the branch, then case on operand inside each branch.
-- The Bitcast.int branch has a nested ite that needs explicit handling.
private theorem semCast_pnl (op : CastOp) (srcTy dstTy : Ty) (operandId : ValueId) :
    pnl (semCast op srcTy dstTy operandId) := by
  unfold semCast
  refine bind_pnl _ _ (lv_pnl operandId) ?_; intro operand
  -- Poison guard (copy-propagates-poison): a Cast that would inspect a
  -- `.partial` operand faults as UB before the per-op dispatch. After the
  -- guard the operand is non-partial, so the uniform `cases op <;> cases
  -- operand` dispatch below discharges every cast arm.
  refine bind_pnl _ _ (rejectPartial_pnl operand "Cast") ?_; intro _
  cases op <;>
    (cases operand <;>
      first
        | (unfold Sem.throwTypeError; exact t_pnl _)
        | (unfold Sem.throwUnsupported; exact t_pnl _)
        | exact bf_pnl _
        | exact match_width_bindFresh_pnl _ _
        | exact match_width_guarded_pnl _ _ _ _
        | (refine ite_pnl (bf_pnl _) ?_; exact match_width_bindFresh_pnl _ _))

private theorem semPtrData_pnl (ptrTy : Ty) (ptrId : ValueId) :
    pnl (semPtrData ptrTy ptrId) := by
  unfold semPtrData
  -- Outer match on ptrTy: FatPtr arm, then the thin default arm.
  split
  · refine bind_pnl _ _ (lv_pnl ptrId) ?_; intro ptrVal
    refine bool_ite_pnl _ (throwTypeError_pnl _) ?_
    cases fatPtrDataValue ptrVal with
    | some v => exact bf_pnl v
    | none => exact throwTypeError_pnl _
  · refine bool_ite_pnl _ ?_ (throwTypeError_pnl _)
    refine bind_pnl _ _ (lv_pnl ptrId) ?_; intro ptrVal
    cases ptrVal <;>
      first
        | exact bf_pnl _
        | (unfold Sem.throwTypeError; exact t_pnl _)

private theorem semPtrMetadata_pnl (ptrTy metadataTy : Ty) (ptrId : ValueId) :
    pnl (semPtrMetadata ptrTy metadataTy ptrId) := by
  unfold semPtrMetadata
  split
  · refine bool_ite_pnl _ (throwTypeError_pnl _) ?_
    refine bind_pnl _ _ (lv_pnl ptrId) ?_; intro ptrVal
    refine bool_ite_pnl _ (throwTypeError_pnl _) ?_
    cases fatPtrMetadataValue ptrVal with
    | some m => exact bf_pnl m
    | none => exact throwTypeError_pnl _
  · refine bool_ite_pnl _ ?_ (throwTypeError_pnl _)
    refine bind_pnl _ _ (lv_pnl ptrId) ?_; intro ptrVal
    cases ptrVal <;>
      first
        | exact bool_ite_pnl _ (bf_pnl _) (throwTypeError_pnl _)
        | (unfold Sem.throwTypeError; exact t_pnl _)

private theorem semPtrFromParts_pnl (ptrTy metadataTy : Ty)
    (dataId metadataId : ValueId) :
    pnl (semPtrFromParts ptrTy metadataTy dataId metadataId) := by
  unfold semPtrFromParts
  split
  · refine bool_ite_pnl _ (throwTypeError_pnl _) ?_
    refine bind_pnl _ _ (lv_pnl metadataId) ?_; intro metaVal
    refine bool_ite_pnl _ (throwTypeError_pnl _) ?_
    refine bind_pnl _ _ (lv_pnl dataId) ?_; intro dataVal
    cases fatPtrFromPartsValue dataVal metaVal with
    | some v => exact bf_pnl v
    | none => exact throwTypeError_pnl _
  · refine bool_ite_pnl _ ?_ (throwTypeError_pnl _)
    refine bool_ite_pnl _ (throwTypeError_pnl _) ?_
    refine bind_pnl _ _ (lv_pnl metadataId) ?_; intro metaVal
    -- match metaVal with | .aggregate [] => (lookup data; match data) | _ => throw
    split
    · refine bind_pnl _ _ (lv_pnl dataId) ?_; intro dataVal
      split <;>
        first
          | exact bf_pnl _
          | (unfold Sem.throwTypeError; exact t_pnl _)
    · unfold Sem.throwTypeError; exact t_pnl _

-- Aggregates: same shape as semBindSlot (match on Option of pure-computed value;
-- some => bindFresh; none => cases on operand into throwUB/throwTypeError).

private theorem semExtractField_pnl (ty : Ty) (aggregateId : ValueId) (field : Nat) :
    pnl (semExtractField ty aggregateId field) := by
  unfold semExtractField
  exact bind_pnl _ _ (lv_pnl aggregateId) fun aggVal =>
    bind_pnl _ _ (rejectPartial_pnl aggVal "ExtractField") fun _ => by
    cases h : getField aggVal field with
    | some v => simp [h]; exact bf_pnl v
    | none =>
      simp [h]
      cases aggVal <;>
        first
          | (unfold Sem.throwUB; exact t_pnl _)
          | (unfold Sem.throwTypeError; exact t_pnl _)

private theorem semInsertField_pnl (ty : Ty) (aggregateId : ValueId) (field : Nat)
    (valueId : ValueId) :
    pnl (semInsertField ty aggregateId field valueId) := by
  unfold semInsertField
  exact bind_pnl _ _ (lv_pnl aggregateId) fun aggVal =>
    bind_pnl _ _ (lv_pnl valueId) fun newVal =>
    bind_pnl _ _ (rejectPartial_pnl aggVal "InsertField") fun _ =>
    bind_pnl _ _ (rejectPartial_pnl newVal "InsertField") fun _ => by
      cases h : setField aggVal field newVal with
      | some v => simp [h]; exact bf_pnl v
      | none =>
        simp [h]
        cases aggVal <;>
          first
            | (unfold Sem.throwUB; exact t_pnl _)
            | (unfold Sem.throwTypeError; exact t_pnl _)

-- ExtractElement/InsertElement: similar but with an extra ValueId lookup for index,
-- and a do-let binding of idx (via match on idxVal with ite for negativity check).
-- The index binding is: do let idx <- match idxVal with | .int _ n => if n<0 then throwUB else pure n.toNat | _ => throwTypeError
-- which desugars to bind of (match .. with ...) into the rest. We handle it compositionally.

-- Helper: pnl for extracting an index from an integer Value with a negativity check.
-- Used by ExtractElement/InsertElement.
private theorem match_idx_pnl (idxVal : Value) (ubMsg tyMsg : String) :
    pnl (match idxVal with
          | .int _ n =>
            if n < 0 then Sem.throwUB ubMsg
            else pure n.toNat
          | _ => Sem.throwTypeError tyMsg) := by
  cases idxVal <;> simp only [] <;>
    first
      | (unfold Sem.throwTypeError; exact t_pnl _)
      | (refine ite_pnl ?_ ?_
         · exact throwUB_pnl _
         · exact p_pnl _)

-- Helper: pnl for matching on Option Value (getElement/setElement result) with
-- bindFresh on some, or a case-split on the original aggregate for the none branch.
private theorem match_option_agg_pnl (ov : Option Value) (aggVal : Value)
    (ubMsg tyMsg : String) :
    pnl (match ov with
          | some v => Sem.bindFresh v
          | none =>
            match aggVal with
            | .aggregate _fields => Sem.throwUB ubMsg
            | _ => Sem.throwTypeError tyMsg) := by
  cases ov with
  | some v => exact bf_pnl v
  | none =>
    cases aggVal <;>
      first
        | (unfold Sem.throwUB; exact t_pnl _)
        | (unfold Sem.throwTypeError; exact t_pnl _)

-- Tail helper: after binding idx, the remaining computation is a match on getElement
-- with bindFresh on some, cases on arrVal for the none branch.
private theorem semExtractElement_tail_pnl (ty : Ty) (arrVal : Value) (idx : Nat) :
    pnl (match arrVal with
          | .vector _ =>
            match getVectorElement ty arrVal idx with
            | .ok v => Sem.bindFresh v
            | .error e => throw e
          | _ =>
            match getElement arrVal idx with
            | some v => Sem.bindFresh v
            | none =>
              match arrVal with
              | .aggregate _ => Sem.throwUB "ExtractElement: index out of bounds"
              | _ => Sem.throwTypeError "ExtractElement: operand is not an aggregate or vector") := by
  cases arrVal with
  | int w n =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | float f =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | bool b =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | ptr a =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | aggregate fields =>
    cases h : getElement (Value.aggregate fields) idx with
    | some v => simpa [h] using bf_pnl v
    | none =>
      simpa [h, Sem.throwUB] using
        (t_pnl (SemError.ub "ExtractElement: index out of bounds"))
  | vector lanes =>
    cases h : getVectorElement ty (Value.vector lanes) idx with
    | ok v => simpa [h] using bf_pnl v
    | error e => simpa [h] using t_pnl e
  | frame f =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | set xs =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | sequence xs =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | record fs =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | closure f caps =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | fatPtr d m =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | «partial» img =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | undef t =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | nullPtr =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))

private theorem semExtractElement_pnl (ty : Ty) (arrayId indexId : ValueId) :
    pnl (semExtractElement ty arrayId indexId) := by
  unfold semExtractElement
  refine bind_pnl _ _ (lv_pnl arrayId) ?_; intro arrVal
  refine bind_pnl _ _ (lv_pnl indexId) ?_; intro idxVal
  -- The index binding   let idx <- match idxVal with | .int _ n => if n<0 then ... else pure n.toNat | _ => throw
  -- compiles by pushing the tail (semExtractElement_tail_pnl arrVal) into each branch.
  cases idxVal with
  | int w n =>
    -- Inner if n<0 then throwUB else pure n.toNat compiles with the
    -- tail already pushed into each branch as let y from prod then jp y.
    refine ite_pnl (c := n < 0) ?_ ?_
    · exact bind_pnl _ _ (throwUB_pnl _) (fun idx => semExtractElement_tail_pnl ty arrVal idx)
    · exact bind_pnl _ _ (p_pnl _) (fun idx => semExtractElement_tail_pnl ty arrVal idx)
  | nullPtr =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semExtractElement_tail_pnl ty arrVal idx)
  | float f =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semExtractElement_tail_pnl ty arrVal idx)
  | bool b =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semExtractElement_tail_pnl ty arrVal idx)
  | ptr a =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semExtractElement_tail_pnl ty arrVal idx)
  | aggregate fields =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semExtractElement_tail_pnl ty arrVal idx)
  | vector lanes =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semExtractElement_tail_pnl ty arrVal idx)
  | frame f =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semExtractElement_tail_pnl ty arrVal idx)
  | set xs =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semExtractElement_tail_pnl ty arrVal idx)
  | sequence xs =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semExtractElement_tail_pnl ty arrVal idx)
  | record fs =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semExtractElement_tail_pnl ty arrVal idx)
  | closure f caps =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semExtractElement_tail_pnl ty arrVal idx)
  | fatPtr d m =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semExtractElement_tail_pnl ty arrVal idx)
  | «partial» img =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semExtractElement_tail_pnl ty arrVal idx)
  | undef t =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semExtractElement_tail_pnl ty arrVal idx)

private theorem semInsertElement_tail_pnl (ty : Ty) (arrVal newVal : Value) (idx : Nat) :
    pnl (match arrVal with
          | .vector _ =>
            match setVectorElement ty arrVal idx newVal with
            | .ok v => Sem.bindFresh v
            | .error e => throw e
          | _ =>
            match setElement arrVal idx newVal with
            | some v => Sem.bindFresh v
            | none =>
              match arrVal with
              | .aggregate _ => Sem.throwUB "InsertElement: index out of bounds"
              | _ => Sem.throwTypeError "InsertElement: operand is not an aggregate or vector") := by
  cases arrVal with
  | int w n =>
    simpa [setElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "InsertElement: operand is not an aggregate or vector"))
  | float f =>
    simpa [setElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "InsertElement: operand is not an aggregate or vector"))
  | bool b =>
    simpa [setElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "InsertElement: operand is not an aggregate or vector"))
  | ptr a =>
    simpa [setElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "InsertElement: operand is not an aggregate or vector"))
  | aggregate fields =>
    cases h : setElement (Value.aggregate fields) idx newVal with
    | some v => simpa [h] using bf_pnl v
    | none =>
      simpa [h, Sem.throwUB] using
        (t_pnl (SemError.ub "InsertElement: index out of bounds"))
  | vector lanes =>
    cases h : setVectorElement ty (Value.vector lanes) idx newVal with
    | ok v => simpa [h] using bf_pnl v
    | error e => simpa [h] using t_pnl e
  | frame f =>
    simpa [setElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "InsertElement: operand is not an aggregate or vector"))
  | set xs =>
    simpa [setElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "InsertElement: operand is not an aggregate or vector"))
  | sequence xs =>
    simpa [setElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "InsertElement: operand is not an aggregate or vector"))
  | record fs =>
    simpa [setElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "InsertElement: operand is not an aggregate or vector"))
  | closure f caps =>
    simpa [setElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "InsertElement: operand is not an aggregate or vector"))
  | fatPtr d m =>
    simpa [setElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "InsertElement: operand is not an aggregate or vector"))
  | «partial» img =>
    simpa [setElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "InsertElement: operand is not an aggregate or vector"))
  | undef t =>
    simpa [setElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "InsertElement: operand is not an aggregate or vector"))
  | nullPtr =>
    simpa [setElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "InsertElement: operand is not an aggregate or vector"))

private theorem semInsertElement_pnl (ty : Ty) (arrayId indexId valueId : ValueId) :
    pnl (semInsertElement ty arrayId indexId valueId) := by
  unfold semInsertElement
  refine bind_pnl _ _ (lv_pnl arrayId) ?_; intro arrVal
  refine bind_pnl _ _ (lv_pnl indexId) ?_; intro idxVal
  refine bind_pnl _ _ (lv_pnl valueId) ?_; intro newVal
  cases idxVal with
  | int w n =>
    refine ite_pnl (c := n < 0) ?_ ?_
    · exact bind_pnl _ _ (throwUB_pnl _) (fun idx => semInsertElement_tail_pnl ty arrVal newVal idx)
    · exact bind_pnl _ _ (p_pnl _) (fun idx => semInsertElement_tail_pnl ty arrVal newVal idx)
  | nullPtr =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semInsertElement_tail_pnl ty arrVal newVal idx)
  | float f =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semInsertElement_tail_pnl ty arrVal newVal idx)
  | bool b =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semInsertElement_tail_pnl ty arrVal newVal idx)
  | ptr a =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semInsertElement_tail_pnl ty arrVal newVal idx)
  | aggregate fields =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semInsertElement_tail_pnl ty arrVal newVal idx)
  | vector lanes =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semInsertElement_tail_pnl ty arrVal newVal idx)
  | frame f =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semInsertElement_tail_pnl ty arrVal newVal idx)
  | set xs =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semInsertElement_tail_pnl ty arrVal newVal idx)
  | sequence xs =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semInsertElement_tail_pnl ty arrVal newVal idx)
  | record fs =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semInsertElement_tail_pnl ty arrVal newVal idx)
  | closure f caps =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semInsertElement_tail_pnl ty arrVal newVal idx)
  | fatPtr d m =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semInsertElement_tail_pnl ty arrVal newVal idx)
  | «partial» img =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semInsertElement_tail_pnl ty arrVal newVal idx)
  | undef t =>
    exact bind_pnl _ _ (throwTypeError_pnl _) (fun idx => semInsertElement_tail_pnl ty arrVal newVal idx)

-- Memory reads: semLoad.  The do-block  let addr := match ptrVal ...
-- compiles by pushing the continuation k into each match branch, so we must
-- prove the whole match is pnl, not just extract an address.  We split into
-- a tail lemma (the post-addr computation, pnl for any addr) and a case split
-- on ptrVal where each branch delivers an addr (or throws).
-- Step 3: after we know byteSize and s, handle the in-bounds check + readBytes + decode.
private theorem semLoad_tail3_pnl (ty : Ty) (addr byteSize : Nat) (strict : Bool)
    (align : Option Nat) (s : MachineState) : pnl (do
    if !s.memory.isInBounds addr byteSize then
      Sem.throwUB "Load: access is out of bounds"
    if isMisaligned align addr then
      Sem.throwUB "Load: unaligned access (address not aligned to declared alignment)"
    match s.memory.readBytes addr byteSize with
    | some bytes =>
      match decodeValue ty bytes with
      | some v => Sem.bindFresh v
      | none   => Sem.throwTypeError "Load: failed to decode bytes"
    | none =>
      if !strict && isPartialLoadTy ty then
        Sem.bindFresh (.partial (s.memory.readBytesMaybeUninit addr byteSize))
      else
        Sem.throwUB "Load: reading uninitialized memory") := by
  -- The read + decode tail (after we have passed in-bounds). A fully-initialized
  -- read decodes; an uninitialized read either transports a `.partial` value
  -- (non-strict scalar) or is UB — both `pnl`.
  have tail_read : pnl (match s.memory.readBytes addr byteSize with
      | some bytes =>
        match decodeValue ty bytes with
        | some v => Sem.bindFresh v
        | none   => Sem.throwTypeError "Load: failed to decode bytes"
      | none =>
        if !strict && isPartialLoadTy ty then
          Sem.bindFresh (.partial (s.memory.readBytesMaybeUninit addr byteSize))
        else
          Sem.throwUB "Load: reading uninitialized memory") := by
    cases h : s.memory.readBytes addr byteSize with
    | some bs =>
      simp only [h]
      cases decodeValue ty bs with
      | some v => exact bf_pnl v
      | none   => unfold Sem.throwTypeError; exact t_pnl _
    | none =>
      simp only [h]
      exact ite_pnl (bf_pnl _) (throwUB_pnl _)
  -- The alignment gate wraps the read tail; UB or a no-op, both `pnl`.
  have tail_afterBounds : pnl (do
      if isMisaligned align addr then
        Sem.throwUB "Load: unaligned access (address not aligned to declared alignment)"
      match s.memory.readBytes addr byteSize with
      | some bytes =>
        match decodeValue ty bytes with
        | some v => Sem.bindFresh v
        | none   => Sem.throwTypeError "Load: failed to decode bytes"
      | none =>
        if !strict && isPartialLoadTy ty then
          Sem.bindFresh (.partial (s.memory.readBytesMaybeUninit addr byteSize))
        else
          Sem.throwUB "Load: reading uninitialized memory") := by
    refine ite_pnl (c := (isMisaligned align addr) = true) ?_ ?_
    · exact bind_pnl _ _ (throwUB_pnl _) (fun _ => tail_read)
    · exact bind_pnl _ _ (p_pnl _) (fun _ => tail_read)
  -- Now apply ite_pnl to the outer "if !isInBounds then throwUB".
  refine ite_pnl (c := (!s.memory.isInBounds addr byteSize) = true) ?_ ?_
  · exact bind_pnl _ _ (throwUB_pnl _) (fun _ => tail_afterBounds)
  · exact bind_pnl _ _ (p_pnl _) (fun _ => tail_afterBounds)

-- Step 2: after we know byteSize, bind getState and call tail3.
private theorem semLoad_tail2_pnl (ty : Ty) (addr byteSize : Nat) (strict : Bool)
    (align : Option Nat) : pnl (do
    let s <- Sem.getState
    if !s.memory.isInBounds addr byteSize then
      Sem.throwUB "Load: access is out of bounds"
    if isMisaligned align addr then
      Sem.throwUB "Load: unaligned access (address not aligned to declared alignment)"
    match s.memory.readBytes addr byteSize with
    | some bytes =>
      match decodeValue ty bytes with
      | some v => Sem.bindFresh v
      | none   => Sem.throwTypeError "Load: failed to decode bytes"
    | none =>
      if !strict && isPartialLoadTy ty then
        Sem.bindFresh (.partial (s.memory.readBytesMaybeUninit addr byteSize))
      else
        Sem.throwUB "Load: reading uninitialized memory") := by
  exact bind_pnl _ _ gs_pnl (fun s => semLoad_tail3_pnl ty addr byteSize strict align s)

private theorem semLoad_tail_pnl (ty : Ty) (addr : Nat) (strict : Bool)
    (align : Option Nat) : pnl (do
    if addr == 0 then Sem.throwUB "Load: null pointer dereference"
    let byteSize <- match ty.byteSize with
      | some s => pure s
      | none   => Sem.throwTypeError "Load: type has no byte size"
    let s <- Sem.getState
    if !s.memory.isInBounds addr byteSize then
      Sem.throwUB "Load: access is out of bounds"
    if isMisaligned align addr then
      Sem.throwUB "Load: unaligned access (address not aligned to declared alignment)"
    match s.memory.readBytes addr byteSize with
    | some bytes =>
      match decodeValue ty bytes with
      | some v => Sem.bindFresh v
      | none   => Sem.throwTypeError "Load: failed to decode bytes"
    | none =>
      if !strict && isPartialLoadTy ty then
        Sem.bindFresh (.partial (s.memory.readBytesMaybeUninit addr byteSize))
      else
        Sem.throwUB "Load: reading uninitialized memory") := by
  have after_null : pnl (do
      let byteSize <- match ty.byteSize with
        | some s => pure s
        | none   => Sem.throwTypeError "Load: type has no byte size"
      let s <- Sem.getState
      if !s.memory.isInBounds addr byteSize then
        Sem.throwUB "Load: access is out of bounds"
      if isMisaligned align addr then
        Sem.throwUB "Load: unaligned access (address not aligned to declared alignment)"
      match s.memory.readBytes addr byteSize with
      | some bytes =>
        match decodeValue ty bytes with
        | some v => Sem.bindFresh v
        | none   => Sem.throwTypeError "Load: failed to decode bytes"
      | none =>
        if !strict && isPartialLoadTy ty then
          Sem.bindFresh (.partial (s.memory.readBytesMaybeUninit addr byteSize))
        else
          Sem.throwUB "Load: reading uninitialized memory") := by
    cases ty.byteSize with
    | some bs =>
      exact bind_pnl _ _ (p_pnl bs) (fun bsz => semLoad_tail2_pnl ty addr bsz strict align)
    | none    =>
      exact bind_pnl _ _ (throwTypeError_pnl _) (fun bsz => semLoad_tail2_pnl ty addr bsz strict align)
  refine ite_pnl (c := (addr == 0) = true) ?_ ?_
  · exact bind_pnl _ _ (throwUB_pnl _) (fun _ => after_null)
  · exact bind_pnl _ _ (p_pnl _) (fun _ => after_null)

private theorem semLoad_pnl (ty : Ty) (ptrId : ValueId) (strict : Bool)
    (align : Option Nat) :
    pnl (semLoad ty ptrId strict align) := by
  unfold semLoad
  refine bind_pnl _ _ (lv_pnl ptrId) ?_; intro ptrVal
  cases ptrVal with
  | ptr a =>
    refine bind_pnl _ _ (p_pnl a) ?_; intro addr; exact semLoad_tail_pnl ty addr strict align
  | nullPtr =>
    refine bind_pnl _ _ (throwUB_pnl _) ?_; intro addr; exact semLoad_tail_pnl ty addr strict align
  | int w v =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro addr; exact semLoad_tail_pnl ty addr strict align
  | float f =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro addr; exact semLoad_tail_pnl ty addr strict align
  | bool b =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro addr; exact semLoad_tail_pnl ty addr strict align
  | aggregate fields =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro addr; exact semLoad_tail_pnl ty addr strict align
  | vector lanes =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro addr; exact semLoad_tail_pnl ty addr strict align
  | frame f =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro addr; exact semLoad_tail_pnl ty addr strict align
  | set xs =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro addr; exact semLoad_tail_pnl ty addr strict align
  | sequence xs =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro addr; exact semLoad_tail_pnl ty addr strict align
  | record fs =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro addr; exact semLoad_tail_pnl ty addr strict align
  | closure f caps =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro addr; exact semLoad_tail_pnl ty addr strict align
  | fatPtr d m =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro addr; exact semLoad_tail_pnl ty addr strict align
  | «partial» img =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro addr; exact semLoad_tail_pnl ty addr strict align
  | undef t =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro addr; exact semLoad_tail_pnl ty addr strict align

-- AtomicLoad: same structure as Load with an ordering-validity prefix.
private theorem semAtomicLoad_tail3_pnl (ty : Ty) (addr byteSize : Nat) (s : MachineState) : pnl (do
    if !s.memory.isInBounds addr byteSize then
      Sem.throwUB "AtomicLoad: access is out of bounds"
    let bytes <- match s.memory.readBytes addr byteSize with
      | some bs => pure bs
      | none    => Sem.throwUB "AtomicLoad: reading uninitialized memory"
    match decodeValue ty bytes with
    | some v => Sem.bindFresh v
    | none   => Sem.throwTypeError "AtomicLoad: failed to decode bytes") := by
  have tail_decode : forall bytes, pnl (match decodeValue ty bytes with
    | some v => Sem.bindFresh v
    | none   => Sem.throwTypeError "AtomicLoad: failed to decode bytes") := by
    intro bytes
    cases decodeValue ty bytes with
    | some v => exact bf_pnl v
    | none   => unfold Sem.throwTypeError; exact t_pnl _
  have tail_read : pnl (do
      let bytes <- match s.memory.readBytes addr byteSize with
        | some bs => pure bs
        | none    => Sem.throwUB "AtomicLoad: reading uninitialized memory"
      match decodeValue ty bytes with
      | some v => Sem.bindFresh v
      | none   => Sem.throwTypeError "AtomicLoad: failed to decode bytes") := by
    cases h : s.memory.readBytes addr byteSize with
    | some bs => simp [h]; exact bind_pnl _ _ (p_pnl bs) tail_decode
    | none    => simp [h]; exact bind_pnl _ _ (throwUB_pnl _) tail_decode
  refine ite_pnl (c := (!s.memory.isInBounds addr byteSize) = true) ?_ ?_
  · exact bind_pnl _ _ (throwUB_pnl _) (fun _ => tail_read)
  · exact bind_pnl _ _ (p_pnl _) (fun _ => tail_read)

private theorem semAtomicLoad_tail2_pnl (ty : Ty) (addr byteSize : Nat) : pnl (do
    let s <- Sem.getState
    if !s.memory.isInBounds addr byteSize then
      Sem.throwUB "AtomicLoad: access is out of bounds"
    let bytes <- match s.memory.readBytes addr byteSize with
      | some bs => pure bs
      | none    => Sem.throwUB "AtomicLoad: reading uninitialized memory"
    match decodeValue ty bytes with
    | some v => Sem.bindFresh v
    | none   => Sem.throwTypeError "AtomicLoad: failed to decode bytes") := by
  exact bind_pnl _ _ gs_pnl (fun s => semAtomicLoad_tail3_pnl ty addr byteSize s)

private theorem semAtomicLoad_tail_pnl (ty : Ty) (addr : Nat) : pnl (do
    if addr == 0 then Sem.throwUB "AtomicLoad: null pointer dereference"
    let byteSize <- match ty.byteSize with
      | some s => pure s
      | none   => Sem.throwTypeError "AtomicLoad: type has no byte size"
    let s <- Sem.getState
    if !s.memory.isInBounds addr byteSize then
      Sem.throwUB "AtomicLoad: access is out of bounds"
    let bytes <- match s.memory.readBytes addr byteSize with
      | some bs => pure bs
      | none    => Sem.throwUB "AtomicLoad: reading uninitialized memory"
    match decodeValue ty bytes with
    | some v => Sem.bindFresh v
    | none   => Sem.throwTypeError "AtomicLoad: failed to decode bytes") := by
  have after_null : pnl (do
      let byteSize <- match ty.byteSize with
        | some s => pure s
        | none   => Sem.throwTypeError "AtomicLoad: type has no byte size"
      let s <- Sem.getState
      if !s.memory.isInBounds addr byteSize then
        Sem.throwUB "AtomicLoad: access is out of bounds"
      let bytes <- match s.memory.readBytes addr byteSize with
        | some bs => pure bs
        | none    => Sem.throwUB "AtomicLoad: reading uninitialized memory"
      match decodeValue ty bytes with
      | some v => Sem.bindFresh v
      | none   => Sem.throwTypeError "AtomicLoad: failed to decode bytes") := by
    cases ty.byteSize with
    | some bs =>
      exact bind_pnl _ _ (p_pnl bs) (fun bsz => semAtomicLoad_tail2_pnl ty addr bsz)
    | none    =>
      exact bind_pnl _ _ (throwTypeError_pnl _) (fun bsz => semAtomicLoad_tail2_pnl ty addr bsz)
  refine ite_pnl (c := (addr == 0) = true) ?_ ?_
  · exact bind_pnl _ _ (throwUB_pnl _) (fun _ => after_null)
  · exact bind_pnl _ _ (p_pnl _) (fun _ => after_null)

private theorem semAtomicLoad_pnl (ty : Ty) (ptrId : ValueId) (ordering : MemOrdering) :
    pnl (semAtomicLoad ty ptrId ordering) := by
  unfold semAtomicLoad
  -- The body after the ordering check is the whole Load-like pipeline.
  have body_pnl : pnl (do
      let ptrVal ← Sem.lookupValue ptrId
      let addr ← match ptrVal with
        | .ptr a    => pure a
        | .nullPtr  => Sem.throwUB "AtomicLoad: null pointer dereference"
        | _         => Sem.throwTypeError "AtomicLoad: operand is not a pointer"
      if addr == 0 then Sem.throwUB "AtomicLoad: null pointer dereference"
      let byteSize ← match ty.byteSize with
        | some s => pure s
        | none   => Sem.throwTypeError "AtomicLoad: type has no byte size"
      let s ← Sem.getState
      if !s.memory.isInBounds addr byteSize then
        Sem.throwUB "AtomicLoad: access is out of bounds"
      let bytes ← match s.memory.readBytes addr byteSize with
        | some bs => pure bs
        | none    => Sem.throwUB "AtomicLoad: reading uninitialized memory"
      match decodeValue ty bytes with
      | some v => Sem.bindFresh v
      | none   => Sem.throwTypeError "AtomicLoad: failed to decode bytes") := by
    refine bind_pnl _ _ (lv_pnl ptrId) ?_; intro ptrVal
    cases ptrVal with
    | ptr a =>
      exact bind_pnl _ _ (p_pnl a) (fun addr => semAtomicLoad_tail_pnl ty addr)
    | nullPtr =>
      exact bind_pnl _ _ (throwUB_pnl _) (fun addr => semAtomicLoad_tail_pnl ty addr)
    | int w v =>
      exact bind_pnl _ _ (throwTypeError_pnl _) (fun addr => semAtomicLoad_tail_pnl ty addr)
    | float f =>
      exact bind_pnl _ _ (throwTypeError_pnl _) (fun addr => semAtomicLoad_tail_pnl ty addr)
    | bool b =>
      exact bind_pnl _ _ (throwTypeError_pnl _) (fun addr => semAtomicLoad_tail_pnl ty addr)
    | aggregate fields =>
      exact bind_pnl _ _ (throwTypeError_pnl _) (fun addr => semAtomicLoad_tail_pnl ty addr)
    | vector lanes =>
      exact bind_pnl _ _ (throwTypeError_pnl _) (fun addr => semAtomicLoad_tail_pnl ty addr)
    | frame f =>
      exact bind_pnl _ _ (throwTypeError_pnl _) (fun addr => semAtomicLoad_tail_pnl ty addr)
    | set xs =>
      exact bind_pnl _ _ (throwTypeError_pnl _) (fun addr => semAtomicLoad_tail_pnl ty addr)
    | sequence xs =>
      exact bind_pnl _ _ (throwTypeError_pnl _) (fun addr => semAtomicLoad_tail_pnl ty addr)
    | record fs =>
      exact bind_pnl _ _ (throwTypeError_pnl _) (fun addr => semAtomicLoad_tail_pnl ty addr)
    | closure f caps =>
      exact bind_pnl _ _ (throwTypeError_pnl _) (fun addr => semAtomicLoad_tail_pnl ty addr)
    | fatPtr d m =>
      exact bind_pnl _ _ (throwTypeError_pnl _) (fun addr => semAtomicLoad_tail_pnl ty addr)
    | «partial» img =>
      exact bind_pnl _ _ (throwTypeError_pnl _) (fun addr => semAtomicLoad_tail_pnl ty addr)
    | undef t =>
      exact bind_pnl _ _ (throwTypeError_pnl _) (fun addr => semAtomicLoad_tail_pnl ty addr)
  refine ite_pnl (c := (!isValidLoadOrdering ordering) = true) ?_ ?_
  · exact bind_pnl _ _ (throwTypeError_pnl _) (fun _ => body_pnl)
  · exact bind_pnl _ _ (p_pnl _) (fun _ => body_pnl)

-- GEP: lookupValue base; match baseVal for addr binding; then a for-loop accumulator
-- (mutable local in Lean's do-notation, which desugars to a forIn with state).
-- The body of the for loop only does lookupValue + pure match or throw on getElement offset.
-- The accumulator does NOT touch machine state (it is a local Lean Nat). After the loop,
-- bindFresh the result pointer.
-- Since the whole for-loop desugar operates via forIn on the Sem monad where only
-- lookupValue and throw are invoked per iteration, the loop preserves nonlocal state.
-- We prove this via a forIn_pnl lemma.

-- Helper: forIn on a list preserves pnl when the body does.
-- Signature matches List.forIn with a ForInStep-returning body.
private theorem forIn_list_pnl {α β : Type}
    (xs : List α) (acc : β) (body : α -> β -> Sem (ForInStep β))
    (hBody : forall x a, pnl (body x a)) :
    pnl (forIn xs acc body) := by
  induction xs generalizing acc with
  | nil =>
    simp [forIn, List.forIn]
    exact p_pnl _
  | cons x xs ih =>
    simp only [forIn, List.forIn, List.forIn.loop]
    exact bind_pnl _ _ (hBody x acc) fun step => by
      cases step with
      | yield b => exact ih b
      | done b => exact p_pnl _

-- Helper: pnl for GEP body: a single step of the for loop. Given idxVal and
-- the current accumulator, the body either throws or returns yield (acc + off).
private theorem gep_body_step_pnl (pointeeTy : Ty) (idxVal : Value) (totalOffset : Nat) :
    pnl (match idxVal with
          | .int _ idx =>
            match gepByteOffset pointeeTy idx with
            | .ok off => do
              pure PUnit.unit
              pure (ForInStep.yield (totalOffset + off))
            | .error e => do
              throw e
              pure (ForInStep.yield totalOffset)
          | _ => do
            Sem.throwTypeError "GEP: index is not an integer"
            pure (ForInStep.yield totalOffset)) := by
  cases idxVal <;> simp only [] <;>
    first
      | (cases gepByteOffset pointeeTy _ with
          | ok off   => exact bind_pnl _ _ (p_pnl _) fun _ => p_pnl _
          | error e  => exact bind_pnl _ _ (t_pnl e) fun _ => p_pnl _)
      | (exact bind_pnl _ _ (throwTypeError_pnl _) fun _ => p_pnl _)

-- Tail for GEP after addr is bound: the forIn loop plus final bindFresh.
-- All loop iterations only lookupValue and throw or pure-yield, so the whole
-- tail preserves nonlocal state.
private theorem semGEP_tail_pnl (pointeeTy : Ty) (baseAddr : Nat) (indexIds : List ValueId) :
    pnl (do
      let totalOffset <- forIn indexIds (0 : Nat)
        (fun idxId totalOffset => do
          let idxVal <- Sem.lookupValue idxId
          match idxVal with
          | .int _ idx =>
            match gepByteOffset pointeeTy idx with
            | .ok off => do
              pure PUnit.unit
              pure (ForInStep.yield (totalOffset + off))
            | .error e => do
              throw e
              pure (ForInStep.yield totalOffset)
          | _ => do
            Sem.throwTypeError "GEP: index is not an integer"
            pure (ForInStep.yield totalOffset))
      Sem.bindFresh (.ptr (baseAddr + totalOffset))) := by
  refine bind_pnl _ _ ?_ ?_
  · exact forIn_list_pnl indexIds 0 _
      (fun idxId totalOffset =>
        bind_pnl _ _ (lv_pnl idxId) fun idxVal =>
          gep_body_step_pnl pointeeTy idxVal totalOffset)
  intro totalOffset
  exact bf_pnl _

private theorem semGEP_pnl (pointeeTy : Ty) (baseId : ValueId) (indexIds : List ValueId) :
    pnl (semGEP pointeeTy baseId indexIds) := by
  unfold semGEP
  refine bind_pnl _ _ (lv_pnl baseId) ?_; intro baseVal
  -- Compiled form: match baseVal with | ptr a => do let y := pure a; __do_jp y | ... | _ => throw
  cases baseVal with
  | ptr a =>
    refine bind_pnl _ _ (p_pnl a) ?_; intro baseAddr
    exact semGEP_tail_pnl pointeeTy baseAddr indexIds
  | nullPtr =>
    refine bind_pnl _ _ (throwUB_pnl _) ?_; intro baseAddr
    exact semGEP_tail_pnl pointeeTy baseAddr indexIds
  | int w v =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro baseAddr
    exact semGEP_tail_pnl pointeeTy baseAddr indexIds
  | float f =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro baseAddr
    exact semGEP_tail_pnl pointeeTy baseAddr indexIds
  | bool b =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro baseAddr
    exact semGEP_tail_pnl pointeeTy baseAddr indexIds
  | aggregate fields =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro baseAddr
    exact semGEP_tail_pnl pointeeTy baseAddr indexIds
  | vector lanes =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro baseAddr
    exact semGEP_tail_pnl pointeeTy baseAddr indexIds
  | frame f =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro baseAddr
    exact semGEP_tail_pnl pointeeTy baseAddr indexIds
  | set xs =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro baseAddr
    exact semGEP_tail_pnl pointeeTy baseAddr indexIds
  | sequence xs =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro baseAddr
    exact semGEP_tail_pnl pointeeTy baseAddr indexIds
  | record fs =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro baseAddr
    exact semGEP_tail_pnl pointeeTy baseAddr indexIds
  | closure f caps =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro baseAddr
    exact semGEP_tail_pnl pointeeTy baseAddr indexIds
  | fatPtr d m =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro baseAddr
    exact semGEP_tail_pnl pointeeTy baseAddr indexIds
  | «partial» img =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro baseAddr
    exact semGEP_tail_pnl pointeeTy baseAddr indexIds
  | undef t =>
    refine bind_pnl _ _ (throwTypeError_pnl _) ?_; intro baseAddr
    exact semGEP_tail_pnl pointeeTy baseAddr indexIds

-- IsUnique: lookupValue ptr, then getAllocIdFromPtrARC (reads state only),
-- then requireArcRef (reads state only), then getState, then pure arithmetic, bindFresh.
-- Both getAllocIdFromPtrARC and requireArcRef only read state via getState + match + throw.

-- Helper: pnl for matching on Option Allocation with pure on some / throwUB on none.
-- The allocations.find? call produces an Option Allocation; we don't care about the
-- concrete predicate inside find?.
private theorem match_option_alloc_pnl (oAlloc : Option Allocation) (msg : String) :
    pnl (match oAlloc with
          | some alloc => pure alloc.id
          | none => Sem.throwUB msg) := by
  cases oAlloc with
  | some alloc => exact p_pnl _
  | none       => unfold Sem.throwUB; exact t_pnl _

private theorem getAllocIdFromPtrARC_pnl (ptrVal : Value) : pnl (getAllocIdFromPtrARC ptrVal) := by
  unfold getAllocIdFromPtrARC
  refine bind_pnl _ _ gs_pnl ?_; intro s
  cases ptrVal <;> simp only [] <;>
    first
      | exact match_option_alloc_pnl _ _
      | (unfold Sem.throwUB; exact t_pnl _)
      | (unfold Sem.throwTypeError; exact t_pnl _)

private theorem requireArcRef_pnl (allocId : AllocId) : pnl (requireArcRef allocId) := by
  unfold requireArcRef
  refine bind_pnl _ _ gs_pnl ?_; intro s
  cases s.permissions.get allocId with
  | none => exact throwUB_pnl _
  | some perm =>
    cases perm <;>
      first
        | exact p_pnl _
        | exact throwUB_pnl _

private theorem semIsUnique_pnl (ptrId : ValueId) : pnl (semIsUnique ptrId) := by
  unfold semIsUnique
  exact bind_pnl _ _ (lv_pnl ptrId) fun ptrVal =>
    bind_pnl _ _ (getAllocIdFromPtrARC_pnl ptrVal) fun allocId =>
      bind_pnl _ _ (requireArcRef_pnl allocId) fun _ =>
        bind_pnl _ _ gs_pnl fun s => bf_pnl _

private theorem semSeqMapAddK_pnl (ty : Ty) (seqId : ValueId) (k : Nat) :
    pnl (semSeqMapAddK ty seqId k) := by
  unfold semSeqMapAddK
  refine bind_pnl _ _ (lv_pnl seqId) ?_; intro seqVal
  cases seqVal with
  | sequence elems =>
    cases h : seqMapAddKList k elems with
    | ok mapped => simp [h]; exact bf_pnl _
    | error e => simp [h]; exact t_pnl _
  | _ => first
      | (unfold Sem.throwTypeError; exact t_pnl _)

private theorem semSeqMapNot_pnl (ty : Ty) (seqId : ValueId) :
    pnl (semSeqMapNot ty seqId) := by
  unfold semSeqMapNot
  refine bind_pnl _ _ (lv_pnl seqId) ?_; intro seqVal
  cases seqVal with
  | sequence elems =>
    cases h : seqMapNotList elems with
    | ok mapped => simp [h]; exact bf_pnl _
    | error e => simp [h]; exact t_pnl _
  | _ => first
      | (unfold Sem.throwTypeError; exact t_pnl _)

theorem dce_pure_inst (inst : Inst) (s : MachineState)
    (hPure : inst.hasSideEffects = false)
    (hNotTerminator : inst.isTerminator = false)
    (result : InstrResult × MachineState)
    (hOk : Sem.run (stepInst inst) s = .ok result) :
    state_equiv_except_locals s result.snd := by
  -- Case analysis on instruction variant.
  -- hPure eliminates all side-effecting instructions (Store, AtomicLoad,
  -- AtomicStore, AtomicRMW, CmpXchg, Fence, Call, CallIndirect, Assert, Borrow,
  -- BorrowMut, EndBorrow, Retain, Release, Alloca). AtomicLoad is observable
  -- (synchronizes-with) and therefore NOT removable, matching Rust.
  -- hNotTerminator eliminates all terminators (Br, CondBr, Switch, Return,
  -- Unreachable).
  -- The remaining pure non-terminator instructions are:
  --   BinOp, UnOp, Overflow, ICmp, FCmp, Cast, Load (non-volatile), GEP,
  --   ExtractField, InsertField, ExtractElement, InsertElement,
  --   Const, NullPtr, Undef, Assume, Copy, Select, IsUnique
  -- Each of these only calls Sem.lookupValue and Sem.bindFresh, which
  -- modify only locals and nextValueId, preserving memory/permissions/refCounts.
  cases inst with
  -- Side-effecting cases: contradiction with hPure
  | Store => simp [Inst.hasSideEffects] at hPure
  | AtomicStore => simp [Inst.hasSideEffects] at hPure
  | AtomicRMW => simp [Inst.hasSideEffects] at hPure
  | CmpXchg => simp [Inst.hasSideEffects] at hPure
  | Fence => simp [Inst.hasSideEffects] at hPure
  -- AtomicLoad is observable (synchronizes-with edge): hasSideEffects = true,
  -- so it is NOT DCE-eligible and this case is discharged by contradiction.
  | AtomicLoad => simp [Inst.hasSideEffects] at hPure
  | Call => simp [Inst.hasSideEffects] at hPure
  | CallIndirect => simp [Inst.hasSideEffects] at hPure
  | Assert => simp [Inst.hasSideEffects] at hPure
  | Borrow => simp [Inst.hasSideEffects] at hPure
  | BorrowMut => simp [Inst.hasSideEffects] at hPure
  | EndBorrow => simp [Inst.hasSideEffects] at hPure
  | Retain => simp [Inst.hasSideEffects] at hPure
  | Release => simp [Inst.hasSideEffects] at hPure
  | Alloca => simp [Inst.hasSideEffects] at hPure
  | HeapAlloc => simp [Inst.hasSideEffects] at hPure
  | GlobalAddr => simp [Inst.hasSideEffects] at hPure
  -- Terminator cases: contradiction with hNotTerminator
  | Br => simp [Inst.hasSideEffects, Inst.isTerminator] at hPure
  | CoroSuspend => simp [Inst.hasSideEffects, Inst.isTerminator] at hPure
  | Invoke => simp [Inst.hasSideEffects, Inst.isTerminator] at hPure
  | Resume => simp [Inst.hasSideEffects, Inst.isTerminator] at hPure
  -- LandingPad is observable (the unwinder's transfer target): hasSideEffects
  -- = true, so it is NOT DCE-eligible and this case is discharged by
  -- contradiction, mirroring Rust has_observable_effects.
  | LandingPad => simp [Inst.hasSideEffects] at hPure
  | CondBr => simp [Inst.hasSideEffects, Inst.isTerminator] at hPure
  | Switch => simp [Inst.hasSideEffects, Inst.isTerminator] at hPure
  | Return => simp [Inst.hasSideEffects, Inst.isTerminator] at hPure
  | Unreachable => simp [Inst.hasSideEffects, Inst.isTerminator] at hPure
  -- Pure non-terminator cases: each preserves nonlocal state
  -- These all follow the pattern: lookupValue* → pure computation → bindFresh
  -- Only locals and nextValueId are modified.
  --
  -- Simple arithmetic/comparison/cast: lookupValue → compute → bindFresh
  | BinOp op ty lhs rhs =>
    have h_pnl : pnl (do let vid ← semBinOp op ty lhs rhs
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semBinOp_pnl op ty lhs rhs)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  | UnOp op ty operand =>
    have h_pnl : pnl (do let vid ← semUnOp op ty operand
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semUnOp_pnl op ty operand)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  | Overflow op ty lhs rhs =>
    have h_pnl : pnl (do let vid ← semOverflow op ty lhs rhs
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semOverflow_pnl op ty lhs rhs)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  | ICmp op ty lhs rhs =>
    have h_pnl : pnl (do let vid ← semICmpInst op ty lhs rhs
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semICmpInst_pnl op ty lhs rhs)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  | FCmp op ty lhs rhs =>
    have h_pnl : pnl (do let vid ← semFCmpInst op ty lhs rhs
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semFCmpInst_pnl op ty lhs rhs)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  | Cast op srcTy dstTy operand =>
    -- semCast: lookupValue → pure cast → bindFresh
    have h_pnl : pnl (do let vid ← semCast op srcTy dstTy operand
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semCast_pnl op srcTy dstTy operand)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  -- Constants: just bindFresh (no reads)
  | Const ty val =>
    -- Const: match val to produce a Value, then bindFresh
    simp only [stepInst, Sem.run, StateT.run, Sem.bindFresh,
               Sem.getState, Sem.setState, StateT.get, StateT.set,
               MachineState.bindValue, bind, StateT.bind, Except.bind,
               pure, StateT.pure, Except.ok.injEq] at hOk
    constructor
    · cases hOk; rfl
    constructor
    · cases hOk; rfl
    · cases hOk; rfl
  | NullPtr =>
    -- NullPtr: stepInst = do let vid <- Sem.bindFresh .nullPtr; pure (.value (some vid))
    -- bindFresh only modifies locals and nextValueId.
    simp only [stepInst, Sem.run, StateT.run, Sem.bindFresh,
               Sem.getState, Sem.setState, StateT.get, StateT.set,
               MachineState.bindValue, bind, StateT.bind, Except.bind,
               pure, StateT.pure, Except.ok.injEq] at hOk
    constructor
    · cases hOk; rfl
    constructor
    · cases hOk; rfl
    · cases hOk; rfl
  | Undef ty =>
    -- Undef: stepInst = do let vid <- Sem.bindFresh (.undef ty); pure (.value (some vid))
    simp only [stepInst, Sem.run, StateT.run, Sem.bindFresh,
               Sem.getState, Sem.setState, StateT.get, StateT.set,
               MachineState.bindValue, bind, StateT.bind, Except.bind,
               pure, StateT.pure, Except.ok.injEq] at hOk
    constructor
    · cases hOk; rfl
    constructor
    · cases hOk; rfl
    · cases hOk; rfl
  -- Pseudo: lookupValue → bindFresh
  | Copy ty operand =>
    -- stepInst (.Copy ty operand) unfolds to:
    -- do let v ← Sem.lookupValue operand; let vid ← Sem.bindFresh v; pure (.value (some vid))
    have h_pnl : pnl (do let v ← Sem.lookupValue operand
                         let vid ← Sem.bindFresh v
                         pure (InstrResult.value (some vid))) :=
      bind_pnl _ _ (lv_pnl operand) fun _ =>
      bind_pnl _ _ (bf_pnl _) fun _ =>
      p_pnl _
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  | Select ty cond thenVal elseVal =>
    have h_pnl : pnl (stepInst (.Select ty cond thenVal elseVal)) :=
      stepSelect_pnl ty cond thenVal elseVal
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  -- Proof: no-op
  | Assume cond =>
    -- Assume: pure (.value none) — state unchanged
    simp only [stepInst, Sem.run, StateT.run, pure, StateT.pure,
               Except.ok.injEq] at hOk
    have := hOk
    constructor
    · cases this; rfl
    constructor
    · cases this; rfl
    · cases this; rfl
  -- Memory reads: lookupValue → read memory (no write) → bindFresh
  | Load ty ptr volatile align =>
    have h_pnl : pnl (do let vid ← semLoad ty ptr volatile align
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semLoad_pnl ty ptr volatile align)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  | GEP pointeeTy base indices =>
    have h_pnl : pnl (do let vid ← semGEP pointeeTy base indices
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semGEP_pnl pointeeTy base indices)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  | PtrData ptrTy ptr =>
    have h_pnl : pnl (do let vid ← semPtrData ptrTy ptr
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semPtrData_pnl ptrTy ptr)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  | PtrMetadata ptrTy metadataTy ptr =>
    have h_pnl : pnl (do let vid ← semPtrMetadata ptrTy metadataTy ptr
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semPtrMetadata_pnl ptrTy metadataTy ptr)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  | PtrFromParts ptrTy metadataTy data metadata =>
    have h_pnl : pnl (do let vid ← semPtrFromParts ptrTy metadataTy data metadata
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semPtrFromParts_pnl ptrTy metadataTy data metadata)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  -- Aggregate operations: lookupValue → pure field/element access → bindFresh
  | ExtractField ty aggregate field =>
    have h_pnl : pnl (do let vid ← semExtractField ty aggregate field
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semExtractField_pnl ty aggregate field)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  | InsertField ty aggregate field value =>
    have h_pnl : pnl (do let vid ← semInsertField ty aggregate field value
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semInsertField_pnl ty aggregate field value)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  | ExtractElement ty array index =>
    have h_pnl : pnl (do let vid ← semExtractElement ty array index
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semExtractElement_pnl ty array index)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  | InsertElement ty array index value =>
    have h_pnl : pnl (do let vid ← semInsertElement ty array index value
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semInsertElement_pnl ty array index value)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  -- Sequence element-op loops: lookupValue → pure element map → bindFresh
  | SeqMapAddK ty seq k =>
    have h_pnl : pnl (do let vid ← semSeqMapAddK ty seq k
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semSeqMapAddK_pnl ty seq k)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  | SeqMapNot ty seq =>
    have h_pnl : pnl (do let vid ← semSeqMapNot ty seq
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semSeqMapNot_pnl ty seq)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  -- ARC read-only: lookupValue → read refCounts (no write) → bindFresh
  | IsUnique ptr =>
    have h_pnl : pnl (do let vid ← semIsUnique ptr
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semIsUnique_pnl ptr)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  -- Binding frames (TrustIr#32): OpenFrame/BindSlot/LoadSlot are pure SSA
  -- register updates; CloseFrame is nominally side-effecting (DCE marker).
  | OpenFrame def_ =>
    -- semOpenFrame: bindFresh (initFrame slots)
    -- Only bindFresh modifies state; follows the NullPtr/Undef pattern.
    simp only [stepInst, semOpenFrame, Sem.run, StateT.run, Sem.bindFresh,
               Sem.getState, Sem.setState, StateT.get, StateT.set,
               MachineState.bindValue, bind, StateT.bind, Except.bind,
               pure, StateT.pure, Except.ok.injEq] at hOk
    constructor
    · cases hOk; rfl
    constructor
    · cases hOk; rfl
    · cases hOk; rfl
  | BindSlot frame slot value =>
    -- semBindSlot: lookupValue frame → lookupValue value → pure bindSlot →
    -- bindFresh. All pure reads + single bindFresh (or throw on failure).
    have h_pnl : pnl (do let vid ← semBindSlot frame slot value
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semBindSlot_pnl frame slot value)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  | LoadSlot frame slot ty =>
    -- semLoadSlot: lookupValue frame → pure loadSlot → bindFresh.
    -- All pure reads + single bindFresh (or throw on failure).
    have h_pnl : pnl (do let vid ← semLoadSlot frame slot ty
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semLoadSlot_pnl frame slot ty)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  | CloseFrame frame =>
    -- CloseFrame is marked hasSideEffects = true (DCE semantics);
    -- this case contradicts hPure.
    simp [Inst.hasSideEffects] at hPure
  -- Dealloc frees an allocation; always side-effecting.
  | Dealloc ptr =>
    simp [Inst.hasSideEffects] at hPure
  -- DialectOp is conservatively side-effecting until lowered (TrustIr#54).
  | DialectOp op =>
    simp [Inst.hasSideEffects] at hPure
  -- SeqMap invokes an arbitrary element function per element (a call in
  -- disguise): conservatively side-effecting, exactly like Call.
  | SeqMap ty seq fwd =>
    simp [Inst.hasSideEffects] at hPure

-- =================================================================
-- Instruction reordering (commutativity)
-- =================================================================

/-- Two instructions commute if executing them in either order produces
    the same final state (we only require the final state to match,
    not intermediate results, since the intermediate SSA values may
    be bound to different ValueIds). -/
def instructions_commute (i1 i2 : Inst) : Prop :=
  forall s, forall r1 : InstrResult × MachineState,
    Sem.run (stepInst i1) s = .ok r1 ->
    forall r2 : InstrResult × MachineState,
      Sem.run (stepInst i2) r1.snd = .ok r2 ->
      exists r1' r2',
        Sem.run (stepInst i2) s = .ok r1' /\
        Sem.run (stepInst i1) r1'.snd = .ok r2' /\
        state_equiv_except_locals r2.snd r2'.snd

/-- Weaker commutativity: any successful execution of two pure
    instructions preserves the original non-local state.

    This is the key theorem for instruction scheduling in TrustCg.
    The original instructions_commute definition requires both
    orderings to succeed, but data dependencies (i2 reads the result
    of i1) prevent the reverse ordering from succeeding. This weaker
    form says: regardless of which order succeeds, the non-local state
    (memory, permissions, refCounts) is the same as the original.

    The proof applies dce_pure_inst twice and composes the
    state_equiv_except_locals results transitively. -/
theorem pure_instructions_commute (i1 i2 : Inst)
    (h1 : i1.hasSideEffects = false)
    (h2 : i2.hasSideEffects = false)
    (h1t : i1.isTerminator = false)
    (h2t : i2.isTerminator = false) :
    forall s r1 r2,
      Sem.run (stepInst i1) s = .ok r1 ->
      Sem.run (stepInst i2) r1.snd = .ok r2 ->
      state_equiv_except_locals r2.snd s := by
  intro s r1 r2 hRun1 hRun2
  -- Apply dce_pure_inst to i1: s is equiv to r1.snd (nonlocal)
  have h_eq1 := dce_pure_inst i1 s h1 h1t r1 hRun1
  -- Apply dce_pure_inst to i2: r1.snd is equiv to r2.snd (nonlocal)
  have h_eq2 := dce_pure_inst i2 r1.snd h2 h2t r2 hRun2
  -- Compose: s equiv r1.snd equiv r2.snd, so r2.snd equiv s
  exact state_equiv_except_locals_symm s r2.snd
    (state_equiv_except_locals_trans s r1.snd r2.snd h_eq1 h_eq2)

-- =================================================================
-- Block-level transformation
-- =================================================================

/-- A block transform is preserving if it produces the same StepResult
    for every valid input. -/
def block_transform_preserving (transform : BasicBlock -> BasicBlock)
    (cfg : CFG) : Prop :=
  forall bid, match cfg bid with
    | none => True
    | some block =>
      forall args s result,
        Sem.run (stepBlock block args) s = .ok result ->
        Sem.run (stepBlock (transform block) args) s = .ok result

/-- Monadic bind decomposition for Sem: the result of running a bind
    is determined by the result of the first computation. -/
private theorem sem_run_bind_eq {a b : Type} (ma : Sem a) (f : a -> Sem b)
    (s : MachineState) :
    Sem.run (ma >>= f) s = match Sem.run ma s with
      | .ok (a, s') => Sem.run (f a) s'
      | .error e => .error e := by
  simp [Sem.run, StateT.run, bind, StateT.bind, Except.bind]
  cases (ma s) with
  | ok val => rfl
  | error e => rfl

/-- Helper: stepN preservation under block transform for a specific CFG.
    If every block in cfg is preserved by transform, then stepN on
    the pointwise-transformed CFG produces the same result.

    The proof proceeds by induction on fuel:
    - Base case: fuel = 0, stepN produces outOfFuel error, vacuously true.
    - Inductive case: fuel = n+1. Unfold stepN, case-split on cfg(pc).
      If none, both sides produce the same type error.
      If some block, the transformed cfg maps pc to some (transform block).
      By hBlock, stepBlock (transform block) produces the same StepResult.
      For Ret/Stuck/Call: both continuations are identical.
      For Continue: apply the inductive hypothesis. -/
private theorem stepN_block_transform_aux
    (transform : BasicBlock -> BasicBlock) (fuel : Nat)
    (cfg : CFG) (pc : BlockId) (args : List Value) (s : MachineState)
    (result : List Value × MachineState)
    (hBlock : block_transform_preserving transform cfg)
    (hOk : Sem.run (stepN fuel cfg pc args) s = .ok result) :
    Sem.run (stepN fuel (fun bid => (cfg bid).map transform) pc args) s
      = .ok result := by
  induction fuel generalizing pc args s with
  | zero =>
    simp only [stepN] at hOk
    exact Except.noConfusion hOk
  | succ n ih =>
    simp only [stepN] at hOk |-
    cases hCfg : cfg pc with
    | none =>
      simp only [hCfg, Option.map] at hOk |-
      exact hOk
    | some block =>
      simp only [hCfg, Option.map] at hOk |-
      rw [sem_run_bind_eq] at hOk |-
      cases hSB : Sem.run (stepBlock block args) s with
      | error e => simp [hSB] at hOk
      | ok val =>
        simp only [hSB] at hOk
        have hBP := hBlock pc
        simp only [hCfg] at hBP
        have hSBT := hBP args s val hSB
        simp only [hSBT]
        obtain ⟨sr, s'⟩ := val
        simp only at hOk |-
        cases sr with
        | Ret values => exact hOk
        | Stuck => exact hOk
        | Continue nextPc nextArgs => exact ih nextPc nextArgs s' hOk
        | CallReq fid callArgs => exact hOk
        | CallIndirectReq addr fid callArgs => exact hOk
        | InvokeReq fid callArgs nd nargs ud => exact hOk
        | SeqMapReq fid elems => exact hOk

/-- Lifting: if a block transform is preserving for all blocks in ALL CFGs,
    then lifting it to a CFG transform is semantics_preserving.

    Note: the hypothesis requires the transform to be preserving for every
    possible CFG, because semantics_preserving quantifies over all CFGs.
    For transforms derived from instruction-level equivalences (constant
    folding, DCE), this universality follows from the instruction-level
    property. For CFG-specific transforms, use stepN_block_transform_aux. -/
theorem block_transform_lifts_to_cfg (transform : BasicBlock -> BasicBlock)
    (_cfg : CFG)
    (hBlock : forall c : CFG, block_transform_preserving transform c) :
    semantics_preserving (fun cfg' bid => (cfg' bid).map transform) := by
  intro cfg' pc args s fuel result hOk
  exact stepN_block_transform_aux transform fuel cfg' pc args s result
    (hBlock cfg') hOk

-- =================================================================
-- Identity transform
-- =================================================================

/-- The identity transform is semantics_preserving. -/
theorem id_transform_preserving :
    semantics_preserving (fun cfg => cfg) := by
  intro cfg pc args s fuel result hOk
  exact hOk

/-- Composing two semantics-preserving transforms yields a
    semantics-preserving transform. -/
theorem compose_preserving (t1 t2 : CFG -> CFG)
    (h1 : semantics_preserving t1)
    (h2 : semantics_preserving t2) :
    semantics_preserving (fun cfg => t2 (t1 cfg)) := by
  intro cfg pc args s fuel result hOk
  -- First apply t1 to the original cfg
  have h1Result := h1 cfg pc args s fuel result hOk
  -- Then apply t2 to t1(cfg)
  exact h2 (t1 cfg) pc args s fuel result h1Result

-- =================================================================
-- Inlining correctness (frame-discipline form, B5)
-- =================================================================

/-- Restoring a caller frame preserves everything except locals: the restored
    state is `state_equiv_except_locals` to the callee end state.  Packages
    the three `restoreFrame_preserves_*` lemmas (`CallProps.lean`) in this
    file's equivalence vocabulary. -/
theorem restoreFrame_state_equiv (s : MachineState) (frame : StackFrame)
    (retVals : List Value) :
    state_equiv_except_locals (restoreFrame s frame retVals) s :=
  ⟨restoreFrame_preserves_memory s frame retVals,
   restoreFrame_preserves_permissions s frame retVals,
   restoreFrame_preserves_refCounts s frame retVals⟩

/-- **Inlining correctness, frame-discipline form.**  Executing a `Call` is
    equivalent to executing the callee's body inline: a Call to a resolved
    callee succeeds with `(retVals, sEnd)` IFF the callee body, run inline
    from the callee's entry block on the caller's heap (with the fresh-frame
    locals reset the call discipline prescribes), succeeds with the SAME
    `retVals` — with matching arities, and with `sEnd` being the inline end
    state with the caller frame restored.  In particular the observables
    transfer exactly: return values verbatim, and memory / permissions /
    refCounts by `restoreFrame_state_equiv`.

    The Call side is stated over `runCallReq`, which IS the evaluator's Call
    handling by the B5 bridge theorems (`stepNWithContext_callReq_eq_runCallReq`,
    `stepNWithContext_bodyCall_eq_runCallReq_bind`, `CallProps.lean`) — so this
    theorem is anchored to `stepNWithContext`, not to a transcription.

    Honest scope: this is inlining correctness UP TO THE FRAME DISCIPLINE —
    the callee body runs in its own SSA id space (fresh empty-locals frame),
    exactly as the operational model prescribes.  The stronger splice form
    (substituting the callee's blocks INTO the caller's CFG so they run in the
    caller's id space) additionally requires an SSA value-id/block-id renaming
    function plus an equivariance lemma for `stepInst` under renaming — per-
    instruction infrastructure that does not exist in this model; it remains
    future work below.  For proof transfer (the B5 use case: what the caller
    may assume about `retVals` and the heap after the call) this form is
    already the load-bearing statement. -/
theorem inlining_preserving
    (ctx : EvalContext) (fuel callDepth : Nat)
    (calleeId : FuncId) (callee : EvalFunction) (callArgs : List Value)
    (s sEnd : MachineState) (retVals : List Value)
    (hFn : ctx.functions calleeId = some callee) :
    Sem.run (runCallReq ctx fuel callDepth calleeId callArgs) s
        = .ok (retVals, sEnd)
      ↔ callArgs.length = callee.body.paramTys.length ∧
        retVals.length = callee.body.returnTys.length ∧
        ∃ sCalleeEnd,
          Sem.run (stepNWithContext ctx fuel callDepth
              callee.cfg callee.entryBlock callArgs)
            { s with locals := ValueMap.empty, nextValueId := 0 }
            = .ok (retVals, sCalleeEnd) ∧
          sEnd = restoreFrame sCalleeEnd (saveFrame s none) [] := by
  constructor
  · exact runCallReq_ok_decomp ctx fuel callDepth calleeId callee callArgs
      s sEnd retVals hFn
  · intro h
    obtain ⟨hArity, hRet, sCalleeEnd, hInline, hEnd⟩ := h
    subst hEnd
    exact runCallReq_ok_of_inline ctx fuel callDepth calleeId callee callArgs
      s sCalleeEnd retVals hFn hArity hRet hInline

-- =================================================================
-- Future work
-- =================================================================

/-
## Frameworks for subsequent phases

1. **Loop invariant code motion:**
   If an instruction in a loop body produces the same value on every
   iteration, it can be hoisted before the loop. Framework: define
   "loop-invariant" predicate on instructions relative to a CFG cycle.

2. **Common subexpression elimination:**
   If two instructions are inst_equiv and have the same operands,
   the second can be replaced with a reference to the first's result.
   Framework: define "available expressions" analysis over the CFG.

3. **Register allocation correctness:**
   Mapping SSA values to physical registers preserves semantics if
   no two simultaneously live values share a register.
   Framework: define "interference graph" and "valid coloring".

4. **Inlining, splice form:**
   `inlining_preserving` above proves the frame-discipline form (Call ≡
   inline execution of the callee body on a fresh frame).  The residual is
   the splice form — rewriting the caller's CFG to contain the callee's
   blocks so they execute in the caller's SSA id space.  That requires a
   value-id/block-id renaming function and a `stepInst`-equivariance lemma
   under renaming (per instruction), which the model does not yet have.
-/

end TrustIr
