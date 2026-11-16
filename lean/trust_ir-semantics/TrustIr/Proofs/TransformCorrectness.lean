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
import TrustIr.Proofs.AssertStep
import TrustIr.Proofs.FloatChoiceProps

namespace TrustIr

/-!
# Transformation Correctness Framework (Phase 5)

This module defines FRAMEWORKS for proving that compiler transformations
preserve TrustIr semantics. These are not proofs about specific optimizations;
they are the reusable infrastructure that TrustCg instantiates.

## Key definitions

1. **behaviour_refines**: THE transform-correctness notion. Every observable
   behaviour of the transformed program (a return, a trap, UB, or divergence)
   is a behaviour of the source, for every UB-free source run.
2. **semantics_preserving**: forward, `.ok`-only, same fuel. Does NOT
   constrain traps or divergence (see `semantics_preserving_not_imp_refines`).
3. **semantics_preserving_weak**: the same `.ok`-only notion, fuel may differ.
4. **inst_equiv**: Two instructions produce the same result on all states.
5. **instructions_commute**: Two instructions can be reordered.
6. **state_equiv_except_locals**: States agree except for SSA bindings.

## Framework theorems

1. Constant folding correctness (inst_equiv for BinOp vs Const)
2. Dead code elimination (pure instructions preserve non-local state)
3. Instruction reordering (pure non-aliasing instructions commute)
4. Block-level transform lifting (instruction transforms lift to blocks)
5. Inlining correctness, frame-discipline form (a Call succeeds iff the
   callee body run inline on a fresh frame succeeds with the same values;
   every trap of the inline run is a trap of the Call)
6. Behaviour refinement: `id_refines`, `compose_refines`,
   `block_transform_lifts_to_cfg_refines`, `constant_fold_refines`, and the
   `unreachableToReturn_refines` (UB is top), and the counter-models that
   separate it from the `.ok`-only notions (`assertElim_not_refines`,
   `loop_not_refines`, `panicToLoop_not_refines`, `divToRet_not_refines`,
   `trapClass_not_refines`, `ub_introduction_not_refines`)

## Design note

These frameworks follow the CompCert/Vellvm pattern: define semantic
equivalence abstractly, then instantiate for specific passes. TrustCg
provides the pass-specific details; TrustIr provides the semantic framework.
-/

-- =================================================================
-- Semantic equivalence definitions
-- =================================================================

/-- Forward, `.ok`-only preservation at equal fuel: whenever the source
    RETURNS, the transformed program returns the same values and state.

    **This notion does not constrain traps or divergence.** It says nothing
    once the source panics, raises a type error, is unsupported, or runs out
    of fuel. A transform that deletes a failing `Assert` (source `panic`,
    target `ok`) satisfies it (`assertElim_semantics_preserving`), and so do
    one that turns a failing `Assert` into a self-loop
    (`panicToLoop_semantics_preserving`) and one that replaces a diverging
    program with a returning one (`divToRet_semantics_preserving`). It is kept for the existing
    theorems stated over it (`block_transform_lifts_to_cfg`,
    `compose_preserving`), but it is NOT a correctness notion for
    transforms: use `behaviour_refines`.
    `semantics_preserving_not_imp_refines` proves the gap. -/
def semantics_preserving (transform : CFG -> CFG) : Prop :=
  forall cfg pc args s fuel result,
    Sem.run (stepN fuel cfg pc args) s = .ok result ->
    Sem.run (stepN fuel (transform cfg) pc args) s = .ok result

/-- Forward, `.ok`-only preservation where fuel may differ: whenever the
    source returns at some fuel, the transformed program returns the same
    result at some (possibly different) fuel. Appropriate for transforms that
    change the number of executed blocks (e.g. loop unrolling, block
    splitting).

    Like `semantics_preserving`, it does not constrain traps or divergence
    (`panicToLoop_semantics_preserving_weak` holds, although `panicToLoop`
    makes a panicking source diverge). -/
def semantics_preserving_weak (transform : CFG -> CFG) : Prop :=
  forall cfg pc args s result,
    (exists fuel, Sem.run (stepN fuel cfg pc args) s = .ok result) ->
    (exists fuel', Sem.run (stepN fuel' (transform cfg) pc args) s = .ok result)

-- =================================================================
-- Behaviour refinement (WS8.15)
-- =================================================================

/-- An observable behaviour of a `stepN` run from fixed inputs
    `(cfg, pc, args, s)`.

    * `returns r`: the run returns `r` (values and final state) at some fuel.
    * `panics msg site`: a defined trap. Under panic=abort (ub-numerics-policy
      §4) a panic is an observable outcome, not undefined behaviour, so a
      transform may neither remove nor add one. It carries the panic's message
      (the rendering of its kind and operand values) and, for a sited check,
      its resolved site (amendment P, wire v54: the entry and location), so a
      transform may not change WHICH panic a run ends in either
      (`siteRewrite_not_refines`).
    * `typeError` / `unsupported f`: the run is refused as ill-formed or
      outside the executable subset. Both are outcomes a transform must keep.
    * `ub`: undefined behaviour. A UB source licenses every target
      behaviour; a UB TARGET behaviour is never licensed by a UB-free source.
    * `diverges`: `outOfFuel` at EVERY fuel. Divergence is observable, so a
      transform may not introduce it into a terminating or trapping source.

    Traps other than a panic are compared by their stable class
    (`SemError.code`), not by their diagnostic message; a panic is compared
    by its whole normative outcome (amendment P). -/
inductive Outcome where
  | returns (result : List Value × MachineState)
  | panics (msg : String) (site : Option PanicOutcomeSite)
  | typeError
  | unsupported (feature : UnsupportedFeature)
  /-- A named model-capacity refusal, never a normal return or UB-top. -/
  | outOfMemory
  | ub
  | diverges
  /-- An unwinding escaped (amendment D, Part 2). Only the contextual
      evaluator under `PanicStrategy.unwind` raises one, and its entry
      (`evalFunctionInContext`) reports an escaping one as the panic its raise
      recorded; the bare `stepN` this classification serves never produces
      one. Kept as its own outcome so `ofRun` stays total and `none` stays
      exactly `outOfFuel`. -/
  | unwinds

/-- The behaviour a single fuel-bounded run exhibits. `outOfFuel` at one fuel
    is not a behaviour; divergence is `outOfFuel` at every fuel (`Behaves`). -/
def Outcome.ofRun : Except SemError (List Value × MachineState) → Option Outcome
  | .ok r => some (.returns r)
  | .error (.ub _) => some .ub
  | .error (.panic msg site) => some (.panics msg site)
  | .error (.typeError _) => some .typeError
  | .error (.unsupported f _) => some (.unsupported f)
  | .error .outOfFuel => none
  | .error (.outOfMemory _) => some .outOfMemory
  | .error (.unwinding _ _) => some .unwinds

/-- `Behaves cfg pc args s o`: `o` is in the behaviour set of the program
    `cfg` entered at `pc` with `args` from state `s`. A terminating outcome
    is exhibited at some fuel; `diverges` requires `outOfFuel` at every fuel.

    `stepN` counts BLOCKS and is deterministic, so for fixed inputs the set
    is determined by the least fuel at which the run stops, and it is never
    empty (`behaves_nonempty`). The non-emptiness is what rules out the
    vacuous refinement a terminating-outcomes-only definition admits: a
    looping target would otherwise have no behaviour to check. -/
def Behaves (cfg : CFG) (pc : BlockId) (args : List Value) (s : MachineState)
    (o : Outcome) : Prop :=
  (∃ fuel, Outcome.ofRun (Sem.run (stepN fuel cfg pc args) s) = some o) ∨
  (o = .diverges ∧ ∀ fuel, Sem.run (stepN fuel cfg pc args) s = .error .outOfFuel)

/-- **Behaviour refinement**, the transform-correctness notion.

    For every program and inputs whose source run is UB-free at every fuel,
    every behaviour of the transformed program is a behaviour of the source:
    `beh (transform P) ⊆ beh P`. Consequences:

    * a source that returns cannot be made to trap, diverge, or hit UB;
    * a source that panics cannot be made to return (`assertElim_not_refines`)
      or diverge (`panicToLoop_not_refines`);
    * a terminating source cannot be made to diverge (`loop_not_refines`);
    * a UB-free source cannot be given UB (`ub_introduction_not_refines`);
    * a source with UB at some fuel constrains nothing (UB is top).

    Unlike `semantics_preserving`, it is fuel-agnostic: a transform may change
    the number of executed blocks.

    Scope: like `semantics_preserving`, it is stated over `stepN`, the
    intraprocedural evaluator, where a call is an `unsupported` behaviour. A
    refinement proved here says nothing about interprocedural runs
    (`stepNWithContext`); the inlining theorems below relate those directly.
    The same notion with calls executed is `behaviour_refines_in`
    (`TransformRefinementCtx.lean`), and `behaviour_refines_not_imp_refines_in`
    there proves this one does not imply it. -/
def behaviour_refines (transform : CFG → CFG) : Prop :=
  ∀ cfg pc args s, ¬ Behaves cfg pc args s .ub →
    ∀ o, Behaves (transform cfg) pc args s o → Behaves cfg pc args s o

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

-- bindFreshPair (the two-result binder, WS2.24): two fresh binds and a pure
-- pair, each touching only locals/nextValueId.
private theorem bfp_pnl (a b : Value) : pnl (Sem.bindFreshPair a b) := by
  unfold Sem.bindFreshPair
  exact bind_pnl _ _ (bf_pnl _) fun _ =>
    bind_pnl _ _ (bf_pnl _) fun _ => p_pnl _

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
    refine bind_pnl _ _ (lv_pnl thenVal) ?_; intro thenV
    refine bind_pnl _ _ (lv_pnl elseVal) ?_; intro elseV
    cases semVectorSelectValues ty mask thenV elseV with
    | ok result => exact bind_pnl _ _ (p_pnl result) tail
    | error error => exact bind_pnl _ _ (t_pnl error) tail
  | nullPtr =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | int w v =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | float f =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | ptr a =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | array _ =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | aggregate fields =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | frame lineage f =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | sourceFrame _ _ _ =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | set xs =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | sequence xs =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | record fs =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | closure f caps =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | fnDef sig f =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | fnItem f =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | typedClosure cid f caps =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | fatPtr d m =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | «partial» img =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | uninit =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail
  | undef t =>
    exact bind_pnl _ _ (throwTypeError_pnl _) tail

-- Frame lifetime state is disjoint from heap memory, permissions and ARC.
private theorem setFrameState_pnl (openLineages : List Nat) (nextLineage : Nat) :
    pnl (Sem.setFrameState openLineages nextLineage) := by
  intro state result run
  change Except.ok ((), { state with openFrameLineages := openLineages, nextFrameLineage := nextLineage }) = .ok result at run
  cases run
  exact ⟨rfl,rfl,rfl⟩

private theorem frameHandle_pnl (frame : ValueId) (op : String) : pnl (Sem.frameHandle frame op) := by
  unfold Sem.frameHandle
  exact bind_pnl _ _ (lv_pnl frame) fun value =>
    bind_pnl _ _ (rejectPartial_pnl value "frame handle use") fun _ => by
      cases value <;> first | exact p_pnl _ | exact throwTypeError_pnl _

private theorem semOpenFrame_pnl (definition : BindingFrameDef) : pnl (semOpenFrame definition) := by
  unfold semOpenFrame
  refine bind_pnl _ _ gs_pnl ?_
  intro state
  apply ite_pnl
  · exact bind_pnl _ _ (setFrameState_pnl _ _) (fun _ => bf_pnl _)
  · exact throwUB_pnl _

private theorem semBindSlot_pnl (frameId : ValueId) (slot : Nat) (valueId : ValueId) :
    pnl (semBindSlot frameId slot valueId) := by
  unfold semBindSlot
  refine bind_pnl _ _ (frameHandle_pnl _ _) ?_
  rintro ⟨lineage,slots⟩
  refine bind_pnl _ _ gs_pnl ?_
  intro state
  apply bool_ite_pnl
  · refine bind_pnl _ _ (lv_pnl valueId) ?_
    intro value
    apply ite_pnl
    · refine bind_pnl _ _ (lv_pnl frameId) ?_
      intro held
      cases updated : bindSlot held slot value with
      | none => simp only [updated]; exact throwUB_pnl _
      | some snapshot => simp only [updated]; exact bf_pnl _
    · exact throwUB_pnl _
  · exact throwUB_pnl _

private theorem semLoadSlot_pnl (frameId : ValueId) (slot : Nat) (ty : Ty) :
    pnl (semLoadSlot frameId slot ty) := by
  unfold semLoadSlot
  refine bind_pnl _ _ (frameHandle_pnl _ _) ?_
  rintro ⟨lineage,slots⟩
  refine bind_pnl _ _ gs_pnl ?_
  intro state
  apply bool_ite_pnl
  · cases found : (trustIrListGet? slots slot) with
    | some value => simp only [found]; exact bf_pnl _
    | none => simp only [found]; exact throwUB_pnl _
  · exact throwUB_pnl _

-- =================================================================
-- pnl lemmas for pure non-terminator instructions (Phase 5)
-- =================================================================

-- Arithmetic: BinOp follows lookupValue, lookupValue, match types, bindFresh.
private theorem semBinOpDeterministic_pnl (op : BinOp) (ty : Ty) (lhsId rhsId : ValueId) :
    pnl (semBinOpDeterministic op ty lhsId rhsId) := by
  unfold semBinOpDeterministic
  exact bind_pnl _ _ (lv_pnl lhsId) fun lhsVal =>
    bind_pnl _ _ (lv_pnl rhsId) fun rhsVal =>
    bind_pnl _ _ (rejectPartial_pnl lhsVal "BinOp") fun _ =>
    bind_pnl _ _ (rejectPartial_pnl rhsVal "BinOp") fun _ => by
      cases semBinOpValues op ty lhsVal rhsVal with
      | ok result => exact bf_pnl result
      | error error => exact t_pnl error

private theorem semFloatMinMaxAt_pnl (op : BinOp) (ty : Ty) (lhs rhs : Float) :
    pnl (semFloatMinMaxAt op ty lhs rhs) := by
  intro before result run
  obtain ⟨candidates, _, _, same⟩ := semFloatMinMaxAt_permitted run
  have memory := congrArg MachineState.memory same
  have permissions := congrArg MachineState.permissions same
  have refCounts := congrArg MachineState.refCounts same
  exact ⟨memory, permissions, refCounts⟩

-- A do-notation guard distributes the continuation into both branches.
private theorem guard_pnl {α : Type} (condition : Bool) (error : SemError)
    {m : Sem α} (hm : pnl m) :
    pnl (if condition then do
      let _ ← (throw error : Sem PUnit)
      m
    else do
      let _ ← (pure PUnit.unit : Sem PUnit)
      m) := by
  cases condition with
  | false => exact hm
  | true => intro before result run; cases run

private theorem semFloatMinMaxScalarValue_pnl (op : BinOp) (ty : Ty) (lhs rhs : Value) :
    pnl (semFloatMinMaxScalarValue op ty lhs rhs) := by
  unfold semFloatMinMaxScalarValue
  refine bind_pnl _ _ (rejectPartial_pnl lhs "BinOp") ?_; intro _
  refine bind_pnl _ _ (rejectPartial_pnl rhs "BinOp") ?_; intro _
  refine guard_pnl (!ty.isFloat) (.typeError "min/max requires a float type") ?_
  cases lhs with
  | float left =>
    cases rhs with
    | float right =>
      exact bind_pnl _ _ (semFloatMinMaxAt_pnl op ty left right) (fun _ => p_pnl _)
    | _ => exact throwTypeError_pnl _
  | _ => exact throwTypeError_pnl _

private theorem semFloatMinMaxLanes_pnl (op : BinOp) (ty : Ty)
    (lhs rhs : List Value) : pnl (semFloatMinMaxLanes op ty lhs rhs) := by
  induction lhs generalizing rhs with
  | nil => cases rhs <;> first | exact p_pnl _ | exact throwTypeError_pnl _
  | cons left lefts ih =>
    cases rhs with
    | nil => exact throwTypeError_pnl _
    | cons right rights =>
      exact bind_pnl _ _ (semFloatMinMaxScalarValue_pnl op ty left right) fun _ =>
        bind_pnl _ _ (ih rights) fun _ => p_pnl _

private theorem semFloatMinMaxValues_pnl (op : BinOp) (ty : Ty) (lhs rhs : Value) :
    pnl (semFloatMinMaxValues op ty lhs rhs) := by
  unfold semFloatMinMaxValues
  refine bind_pnl _ _ (rejectPartial_pnl lhs "BinOp") ?_; intro _
  refine bind_pnl _ _ (rejectPartial_pnl rhs "BinOp") ?_; intro _
  cases ty with
  | Vector count elemTy =>
    refine guard_pnl (count == 0) (.unsupported .vectorShape "zero-lane min/max vector") ?_
    refine guard_pnl (!elemTy.isFloat) (.typeError "min/max requires float vector lanes") ?_
    cases lhs with
    | vector left =>
      cases rhs with
      | vector right =>
        refine guard_pnl (left.length != count || right.length != count)
          (.typeError "min/max vector lane count does not match type") ?_
        exact bind_pnl _ _ (semFloatMinMaxLanes_pnl op elemTy left right) (fun _ => p_pnl _)
      | _ => exact throwTypeError_pnl _
    | _ => exact throwTypeError_pnl _
  | _ => exact semFloatMinMaxScalarValue_pnl op _ lhs rhs

private theorem semFloatMinMax_pnl (op : BinOp) (ty : Ty) (lhsId rhsId : ValueId) :
    pnl (semFloatMinMax op ty lhsId rhsId) := by
  unfold semFloatMinMax
  exact bind_pnl _ _ (lv_pnl lhsId) fun lhs =>
    bind_pnl _ _ (lv_pnl rhsId) fun rhs =>
    bind_pnl _ _ (semFloatMinMaxValues_pnl op ty lhs rhs) fun value => bf_pnl value

private theorem semBinOp_pnl (op : BinOp) (ty : Ty) (lhsId rhsId : ValueId) :
    pnl (semBinOp op ty lhsId rhsId) := by
  exact ite_pnl (semFloatMinMax_pnl op ty lhsId rhsId)
    (semBinOpDeterministic_pnl op ty lhsId rhsId)

private theorem semUnOp_pnl (op : UnOp) (ty : Ty) (operandId : ValueId) :
    pnl (semUnOp op ty operandId) := by
  unfold semUnOp
  exact bind_pnl _ _ (lv_pnl operandId) fun operand =>
    bind_pnl _ _ (rejectPartial_pnl operand "UnOp") fun _ => by
    cases semUnOpValue op ty operand with
    | ok result => exact bf_pnl result
    | error error => exact t_pnl error

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
             | ok p       =>
               obtain ⟨result, flag⟩ := p; simp only []
               -- Two fresh binds (result, then flag) and a pure pair: each
               -- step touches only locals/nextValueId (WS2.24 unpacked form).
               exact bfp_pnl _ _
             | error e    => exact t_pnl e)

-- Comparisons: ICmpInst, FCmpInst
-- Shape: lookupValue then lookupValue then match operand types then bindFresh or throw.

private theorem semICmpInst_pnl (op : ICmpOp) (ty : Ty) (lhsId rhsId : ValueId)
    (model : ByteModel := .le64) :
    pnl (semICmpInst op ty lhsId rhsId model) := by
  unfold semICmpInst
  exact bind_pnl _ _ (lv_pnl lhsId) fun lhsVal =>
    bind_pnl _ _ (lv_pnl rhsId) fun rhsVal =>
    bind_pnl _ _ (rejectPartial_pnl lhsVal "ICmp") fun _ =>
    bind_pnl _ _ (rejectPartial_pnl rhsVal "ICmp") fun _ => by
      cases semICmpValues op ty lhsVal rhsVal model with
      | ok result => exact bf_pnl result
      | error error => exact t_pnl error

private theorem semFCmpInst_pnl (op : FCmpOp) (ty : Ty) (lhsId rhsId : ValueId) :
    pnl (semFCmpInst op ty lhsId rhsId) := by
  unfold semFCmpInst
  exact bind_pnl _ _ (lv_pnl lhsId) fun lhsVal =>
    bind_pnl _ _ (lv_pnl rhsId) fun rhsVal =>
    bind_pnl _ _ (rejectPartial_pnl lhsVal "FCmp") fun _ =>
    bind_pnl _ _ (rejectPartial_pnl rhsVal "FCmp") fun _ => by
      cases semFCmpValues op ty lhsVal rhsVal with
      | ok result => exact bf_pnl result
      | error error => exact t_pnl error

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

/-- Close a `pnl` goal whose leaves are `bindFresh` / `throw` (in any of the
    `Sem.throw*` spellings) under nested `if` / `match` layers — the shape of
    the width-checked float casts (WS2.23), which thread `checkFloatAt` /
    `roundFloatAt` / `roundIntToFloatAt` results through a `match`. -/
-- The integer-to-address conversion: a pure value or UB.
private theorem addrOfInt_pnl (op : String) (w : Nat) (v : Int) : pnl (Sem.addrOfInt op w v) := by
  unfold Sem.addrOfInt
  exact ite_pnl (p_pnl _) (throwUB_pnl _)

private theorem bindPointerInteger_pnl (op : String) (dstTy : Ty) (address : Nat) :
    pnl (Sem.bindPointerInteger op dstTy address .le64) := by
  unfold Sem.bindPointerInteger
  cases getTyWidth dstTy with
  | ok width =>
    simp only [pure_bind]
    exact ite_pnl (bf_pnl _) (throwUB_pnl _)
  | error error =>
    exact bind_pnl _ _ (t_pnl error) (fun _ => ite_pnl (bf_pnl _) (throwUB_pnl _))

private theorem bindPointerIntegerWithProvenance_pnl (op : String) (dstTy : Ty)
    (address : Nat) (provenance : Option AllocId) :
    pnl (Sem.bindPointerIntegerWithProvenance op dstTy address provenance .le64) := by
  cases provenance with
  | some allocation => exact bindPointerInteger_pnl op dstTy address
  | none =>
    unfold Sem.bindPointerIntegerWithProvenance
    cases getTyWidth dstTy with
    | ok width =>
      simp only [pure_bind]
      exact ite_pnl (bf_pnl _) (throwUB_pnl _)
    | error error =>
      exact bind_pnl _ _ (t_pnl error) (fun _ => ite_pnl (bf_pnl _) (throwUB_pnl _))

local macro "pnl_leaves" : tactic =>
  `(tactic| repeat (first
      | exact bf_pnl _
      | exact t_pnl _
      | (unfold Sem.throwTypeError; exact t_pnl _)
      | (unfold Sem.throwUnsupported; exact t_pnl _)
      | exact throwUB_pnl _
      | exact match_width_bindFresh_pnl _ _
      | exact bindPointerInteger_pnl _ _ _
      | exact bindPointerIntegerWithProvenance_pnl _ _ _ _
      | exact match_width_guarded_pnl _ _ _ _
      | (refine bind_pnl _ _ (addrOfInt_pnl _ _ _) ?_; intro _
         refine bind_pnl _ _ gs_pnl ?_; intro _)
      | split))

-- All cast cases terminate in bindFresh or throw (both pnl).  We case on op
-- to select the branch, then case on operand inside each branch.
-- The Bitcast.int branch has a nested ite that needs explicit handling.
set_option maxHeartbeats 2000000 in
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
    (cases operand <;> simp only [] <;>
      first
        | (unfold Sem.throwTypeError; exact t_pnl _)
        | (unfold Sem.throwUnsupported; exact t_pnl _)
        | exact bf_pnl _
        | exact match_width_bindFresh_pnl _ _
        | exact match_width_guarded_pnl _ _ _ _
        | (refine ite_pnl (bf_pnl _) ?_; exact match_width_bindFresh_pnl _ _)
        | (pnl_leaves; done))

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
  refine bind_pnl _ _ (lv_pnl dataId) ?_; intro dataVal
  refine bind_pnl _ _ (lv_pnl metadataId) ?_; intro metaVal
  refine bind_pnl _ _ (rejectPartial_pnl dataVal "PtrFromParts data") ?_; intro _
  refine bind_pnl _ _ (rejectPartial_pnl metaVal "PtrFromParts metadata") ?_; intro _
  split
  · refine bool_ite_pnl _ (throwTypeError_pnl _) ?_
    refine bool_ite_pnl _ (throwTypeError_pnl _) ?_
    cases fatPtrFromPartsValue dataVal metaVal with
    | some v => exact bf_pnl v
    | none => exact throwTypeError_pnl _
  · refine bool_ite_pnl _ ?_ (throwTypeError_pnl _)
    refine bool_ite_pnl _ (throwTypeError_pnl _) ?_
    split
    · split <;>
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
    | some v =>
      simp [h]
      -- Crystal lane (E3b): an unwritten lane faults (UB), every other lane binds.
      exact ite_pnl (throwUB_pnl _) (bf_pnl v)
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
      split
      · unfold Sem.throwUB; exact t_pnl _
      · cases h : setField aggVal field newVal with
        | some v => simp [h]; exact bf_pnl v
        | none =>
          simp [h]
          cases aggVal <;>
            first
              | (unfold Sem.throwUB; exact t_pnl _)
              | (unfold Sem.throwTypeError; exact t_pnl _)

-- MakeAggregate (WS3.5): a structurally recursive lane lookup (lookupValue +
-- rejectPartial per lane, pure at the end), then a match on (ty, variant) whose
-- every arm is a throw or one bindFresh.
private theorem lookupLanes_pnl (ids : List ValueId) : pnl (lookupLanes ids) := by
  induction ids with
  | nil => exact p_pnl _
  | cons id rest ih =>
    unfold lookupLanes
    exact bind_pnl _ _ (lv_pnl id) fun v =>
      bind_pnl _ _ (rejectPartial_pnl v "MakeAggregate") fun _ =>
      bind_pnl _ _ ih fun _ => p_pnl _

private theorem semMakeAggregate_pnl (ty : Ty) (variant : Option Nat)
    (fieldIds : List ValueId) :
    pnl (semMakeAggregate ty variant fieldIds) := by
  unfold semMakeAggregate
  exact bind_pnl _ _ (lookupLanes_pnl fieldIds) fun _ => by
    split <;>
      first
        | exact throwUnsupported_pnl _ _
        | exact throwTypeError_pnl _
        | exact bf_pnl _
        | (split <;> first | exact throwTypeError_pnl _ | exact bf_pnl _)

-- ArraySplat (v50): one lookupValue + rejectPartial, then a match on the type
-- whose arms are one bindFresh or a throw.
private theorem semArraySplat_pnl (ty : Ty) (valueId : ValueId) :
    pnl (semArraySplat ty valueId) := by
  unfold semArraySplat
  exact bind_pnl _ _ (lv_pnl valueId) fun v =>
    bind_pnl _ _ (rejectPartial_pnl v "ArraySplat") fun _ => by
      split <;>
        first
          | exact throwTypeError_pnl _
          | exact bf_pnl _

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
            -- WS3.17: a sequence is an element carrier too, so an
            -- out-of-range index on one is UB, not a type error.
            | .sequence _elems => Sem.throwUB ubMsg
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
              | .array _ | .aggregate _ => Sem.throwUB "ExtractElement: index out of bounds"
              | .sequence _ => Sem.throwUB "ExtractElement: index out of bounds"
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
  | array fields =>
    cases h : getElement (Value.array fields) idx with
    | some v => simpa [h] using bf_pnl v
    | none =>
      simpa [h, Sem.throwUB] using
        (t_pnl (SemError.ub "ExtractElement: index out of bounds"))
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
  | frame lineage f =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | sourceFrame _ _ _ =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | set xs =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | sequence xs =>
    -- WS3.17: `getElement` now reads a sequence, so this case splits exactly
    -- like the aggregate one (bind on success, UB on an out-of-range index).
    cases h : getElement (Value.sequence xs) idx with
    | some v => simpa [h] using bf_pnl v
    | none =>
      simpa [h, Sem.throwUB] using
        (t_pnl (SemError.ub "ExtractElement: index out of bounds"))
  | record fs =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | closure f caps =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | fnDef sig f =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | fnItem f =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | typedClosure cid f caps =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | fatPtr d m =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | «partial» img =>
    simpa [getElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "ExtractElement: operand is not an aggregate or vector"))
  | uninit =>
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
  unfold semExtractElement semExtractElementUsing
  refine bind_pnl _ _ (lv_pnl arrayId) ?_; intro arrVal
  refine bind_pnl _ _ (lv_pnl indexId) ?_; intro idxVal
  refine bind_pnl _ _ ?_ (fun idx => semExtractElement_tail_pnl ty arrVal idx)
  refine bind_pnl _ _ (rejectPartial_pnl idxVal "ExtractElement index") ?_; intro _
  cases idxVal <;> simp only [] <;>
    first
      | exact throwTypeError_pnl _
      | exact ite_pnl (throwUB_pnl _) (p_pnl _)

private theorem semInsertElement_tail_pnl (ty : Ty) (arrVal newVal : Value) (idx : Nat) :
    pnl (match arrVal with
          | .vector _ =>
            match setVectorElement ty arrVal idx newVal with
            | .ok v => Sem.bindFresh v
            | .error e => throw e
          | _ => do
            Sem.rejectPartial newVal "InsertElement"
            match setElement arrVal idx newVal with
            | some v => Sem.bindFresh v
            | none =>
              match arrVal with
              | .array _ | .aggregate _ => Sem.throwUB "InsertElement: index out of bounds"
              | .sequence _ => Sem.throwUB "InsertElement: index out of bounds"
              | _ => Sem.throwTypeError "InsertElement: operand is not an aggregate or vector") := by
  cases arrVal with
  | vector lanes =>
    cases h : setVectorElement ty (Value.vector lanes) idx newVal with
    | ok v => simpa [h] using bf_pnl v
    | error e => simpa [h] using t_pnl e
  | array fields =>
    refine bind_pnl _ _ (rejectPartial_pnl newVal "InsertElement") ?_; intro _
    cases h : setElement (Value.array fields) idx newVal with
    | some v => simpa [h] using bf_pnl v
    | none =>
      simpa [h, Sem.throwUB] using
        (t_pnl (SemError.ub "InsertElement: index out of bounds"))
  | aggregate fields =>
    refine bind_pnl _ _ (rejectPartial_pnl newVal "InsertElement") ?_; intro _
    cases h : setElement (Value.aggregate fields) idx newVal with
    | some v => simpa [h] using bf_pnl v
    | none =>
      simpa [h, Sem.throwUB] using
        (t_pnl (SemError.ub "InsertElement: index out of bounds"))
  | sequence xs =>
    -- WS3.17: `setElement` now writes a sequence (keeping the constructor),
    -- so this case splits exactly like the aggregate one — after the same
    -- poison inspection of the inserted element (roadmap WS2.10).
    refine bind_pnl _ _ (rejectPartial_pnl newVal "InsertElement") ?_; intro _
    cases h : setElement (Value.sequence xs) idx newVal with
    | some v => simpa [h] using bf_pnl v
    | none =>
      simpa [h, Sem.throwUB] using
        (t_pnl (SemError.ub "InsertElement: index out of bounds"))
  | _ =>
    refine bind_pnl _ _ (rejectPartial_pnl newVal "InsertElement") ?_; intro _
    simpa [setElement, Sem.throwTypeError] using
      (t_pnl (SemError.typeError "InsertElement: operand is not an aggregate or vector"))

private theorem semInsertElement_pnl (ty : Ty) (arrayId indexId valueId : ValueId) :
    pnl (semInsertElement ty arrayId indexId valueId) := by
  unfold semInsertElement semInsertElementUsing
  refine bind_pnl _ _ (lv_pnl arrayId) ?_; intro arrVal
  refine bind_pnl _ _ (lv_pnl indexId) ?_; intro idxVal
  refine bind_pnl _ _ (lv_pnl valueId) ?_; intro newVal
  refine bind_pnl _ _ ?_ (fun idx => semInsertElement_tail_pnl ty arrVal newVal idx)
  refine bind_pnl _ _ (rejectPartial_pnl idxVal "InsertElement index") ?_; intro _
  cases idxVal <;> simp only [] <;>
    first
      | exact throwTypeError_pnl _
      | exact ite_pnl (throwUB_pnl _) (p_pnl _)

-- Memory reads: semLoad and semAtomicLoad. Every prefix only reads the state:
-- the operand lookup, the byte size, the alignment check and the access check
-- (`Sem.accessAddr`, which names the allocation the pointer was derived
-- from); the tail reads and decodes bytes and binds one fresh value.
private theorem accessAlign_pnl (op : String) (ty : Ty) (align : Option Nat) :
    pnl (Sem.accessAlign op ty align) := by
  unfold Sem.accessAlign Sem.declaredOrNaturalAlign
  exact ite_pnl (p_pnl _) (throwTypeError_pnl _)

private theorem expectPointer_pnl (op : String) (v : Value) :
    pnl (Sem.expectPointer op v) := by
  unfold Sem.expectPointer
  split
  · exact throwUB_pnl _
  · exact ite_pnl (throwUB_pnl _) (throwUB_pnl _)
  · exact p_pnl _
  · exact throwTypeError_pnl _

private theorem checkedAccess_pnl (op : String) (addr : Addr) (id : AllocId) (size align : Nat) :
    pnl (Sem.checkedAccess op addr id size align) := by
  unfold Sem.checkedAccess
  simp only [Sem.checkTargetRange, pure_bind]
  refine bind_pnl _ _ gs_pnl ?_; intro s
  split
  · exact throwUB_pnl _
  · exact ite_pnl (throwUB_pnl _)
      (ite_pnl (throwUB_pnl _) (ite_pnl (throwUB_pnl _) (p_pnl _)))

private theorem accessAddr_pnl (op : String) (v : Value) (size align : Nat) :
    pnl (Sem.accessAddr op v size align) := by
  unfold Sem.accessAddr
  refine bind_pnl _ _ (expectPointer_pnl _ _) ?_; intro ⟨addr, id⟩
  exact checkedAccess_pnl _ _ _ _ _

private theorem semLoadValueUsing_pnl (decode : Memory → List UInt8 → Except SemError Value)
    (ty : Ty) (ptrVal : Value) (strict : Bool) (align : Option Nat) :
    pnl (semLoadValueUsing decode ty ptrVal strict align) := by
  unfold semLoadValueUsing
  refine bind_pnl _ _ (rejectPartial_pnl ptrVal "Load") ?_; intro _
  simp only [Ty.byteSizeFor, isPartialLoadTyFor]
  refine bind_pnl _ _ (expectPointer_pnl _ _) ?_; intro ⟨ptrAddr, ptrAlloc⟩
  -- The byte-size `match` carries the rest of the block in each arm.
  have tail : ∀ byteSize, pnl (do
      let alignment ← Sem.accessAlign "Load" ty align
      let addr ← Sem.checkedAccess "Load" ptrAddr ptrAlloc byteSize alignment
      let s ← Sem.getState
      match s.memory.readBytes addr byteSize with
      | some bytes =>
        match decode s.memory bytes with
        | .ok v    => pure v
        | .error e => throw e
      | none =>
        if !strict && isPartialLoadTy ty then
          pure (.partial (s.memory.readBytesMaybeUninit addr byteSize))
        else
          Sem.throwUB "Load: reading uninitialized memory") := by
    intro byteSize
    refine bind_pnl _ _ (accessAlign_pnl _ _ _) ?_; intro alignment
    refine bind_pnl _ _ (checkedAccess_pnl _ _ _ _ _) ?_; intro addr
    refine bind_pnl _ _ gs_pnl ?_; intro s
    cases s.memory.readBytes addr byteSize with
    | some bs =>
      dsimp only
      cases decode s.memory bs with
      | ok v    => exact p_pnl v
      | error e => exact t_pnl e
    | none => exact ite_pnl (p_pnl _) (throwUB_pnl _)
  cases ty.byteSize with
  | some bs => exact bind_pnl _ _ (p_pnl bs) tail
  | none    => exact bind_pnl _ _ (throwUnsupported_pnl _ _) tail

private theorem semLoad_pnl (ty : Ty) (ptrId : ValueId) (strict : Bool)
    (align : Option Nat) : pnl (semLoad ty ptrId strict align) := by
  unfold semLoad semLoadUsing
  refine bind_pnl _ _ (lv_pnl ptrId) ?_; intro pointer
  exact bind_pnl _ _ (semLoadValueUsing_pnl _ _ _ _ _) (fun value => bf_pnl value)

-- AtomicLoad: same structure as Load with an ordering-validity prefix.
private theorem semAtomicLoad_pnl (ty : Ty) (ptrId : ValueId) (ordering : MemOrdering) :
    pnl (semAtomicLoad ty ptrId ordering) := by
  unfold semAtomicLoad semAtomicLoadUsing
  have body_pnl : pnl (do
      let ptrVal ← Sem.lookupValue ptrId
      Sem.rejectPartial ptrVal "AtomicLoad"
      let (ptrAddr, ptrAlloc) ← Sem.expectPointer "AtomicLoad" ptrVal
      let byteSize ← match ty.byteSize with
        | some s => pure s
        | none   => Sem.throwUnsupported .layout "AtomicLoad: type has no byte size"
      let alignment ← Sem.accessAlign "AtomicLoad" ty none
      let addr ← Sem.checkedAccess "AtomicLoad" ptrAddr ptrAlloc byteSize alignment
      let s ← Sem.getState
      let bytes ← match s.memory.readBytes addr byteSize with
        | some bs => pure bs
        | none    => Sem.throwUB "AtomicLoad: reading uninitialized memory"
      match decodeValueAt s.memory ty bytes with
      | .ok v    => Sem.bindFresh v
      | .error e => throw e) := by
    refine bind_pnl _ _ (lv_pnl ptrId) ?_; intro ptrVal
    refine bind_pnl _ _ (rejectPartial_pnl ptrVal "AtomicLoad") ?_; intro _
    refine bind_pnl _ _ (expectPointer_pnl _ _) ?_; intro ⟨ptrAddr, ptrAlloc⟩
    have tail : ∀ byteSize, pnl (do
        let alignment ← Sem.accessAlign "AtomicLoad" ty none
        let addr ← Sem.checkedAccess "AtomicLoad" ptrAddr ptrAlloc byteSize alignment
        let s ← Sem.getState
        let bytes ← match s.memory.readBytes addr byteSize with
          | some bs => pure bs
          | none    => Sem.throwUB "AtomicLoad: reading uninitialized memory"
        match decodeValueAt s.memory ty bytes with
        | .ok v    => Sem.bindFresh v
        | .error e => throw e) := by
      intro byteSize
      refine bind_pnl _ _ (accessAlign_pnl _ _ _) ?_; intro alignment
      refine bind_pnl _ _ (checkedAccess_pnl _ _ _ _ _) ?_; intro addr
      refine bind_pnl _ _ gs_pnl ?_; intro s
      have tail_decode : forall bytes, pnl (match decodeValueAt s.memory ty bytes with
        | .ok v    => Sem.bindFresh v
        | .error e => throw e) := by
        intro bytes
        cases decodeValueAt s.memory ty bytes with
        | ok v    => exact bf_pnl v
        | error e => exact t_pnl e
      cases s.memory.readBytes addr byteSize with
      | some bs => exact bind_pnl _ _ (p_pnl bs) tail_decode
      | none    => exact bind_pnl _ _ (throwUB_pnl _) tail_decode
    cases ty.byteSize with
    | some bs => exact bind_pnl _ _ (p_pnl bs) tail
    | none    => exact bind_pnl _ _ (throwUnsupported_pnl _ _) tail
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

-- Source-aware GEP reads declarations and memory but writes only its result
-- SSA binding. The proof covers every layout query and pure integer reader.
private theorem memoryExcept_pnl {α : Type} (result : Except SemError α) :
    pnl (Sem.fromMemoryExcept result) := by
  cases result with
  | ok value => exact p_pnl value
  | error error => exact t_pnl error

private theorem semGEPAddress_pnl (base : Value) (delta : Nat) (model : ByteModel) :
    pnl (semGEPAddress base delta model) := by
  unfold semGEPAddress
  refine bind_pnl _ _ (rejectPartial_pnl base "GEP") ?_
  intro _
  cases base <;> try exact throwTypeError_pnl _
  case nullPtr => exact throwUB_pnl _
  case ptr address provenance =>
    cases provenance with
    | none =>
      refine bind_pnl _ _ (memoryExcept_pnl _) ?_
      intro result
      split
      · exact bind_pnl _ _ (throwUB_pnl _) (fun _ => p_pnl _)
      · exact bind_pnl _ _ (p_pnl _) (fun _ => p_pnl _)
    | some id =>
      refine bind_pnl _ _ gs_pnl ?_
      intro state
      cases hl : state.memory.lookup id with
      | none => intro s result run; cases run
      | some allocation =>
        refine bind_pnl _ _ (p_pnl allocation) ?_; intro allocation
        dsimp only
        split
        · intro s result run; cases run
        · refine bind_pnl _ _ (p_pnl _) ?_; intro _
          refine bind_pnl _ _ (memoryExcept_pnl _) ?_; intro _
          split
          · exact bind_pnl _ _ (throwUB_pnl _) (fun _ => p_pnl _)
          · exact bind_pnl _ _ (p_pnl _) (fun _ => p_pnl _)

private theorem semGEPValuesUsing_pnl {key : Type} (layoutOf : MemoryLayoutQuery)
    (reader : key → Value → Except SemError Int) (ty : Ty) (base : Value)
    (indices : List (key × Value)) (model : ByteModel) :
    pnl (semGEPValuesUsing layoutOf reader ty base indices model) := by
  unfold semGEPValuesUsing
  exact bind_pnl _ _ (memoryExcept_pnl _) (fun delta => semGEPAddress_pnl base delta model)

private theorem mapM_list_pnl {α β : Type} (xs : List α) (f : α → Sem β)
    (h : ∀ x, pnl (f x)) : pnl (xs.mapM f) := by
  have loop : ∀ (ys : List α) (acc : List β), pnl (List.mapM.loop f ys acc) := by
    intro ys
    induction ys with
    | nil => intro acc; exact p_pnl acc.reverse
    | cons x ys ih =>
      intro acc
      exact bind_pnl _ _ (h x) (fun y => ih (y :: acc))
  exact loop xs []

private theorem semGEP_pnl (pointeeTy : Ty) (baseId : ValueId) (indexIds : List ValueId) :
    pnl (semGEP pointeeTy baseId indexIds) := by
  unfold semGEP semGEPUsing
  refine bind_pnl _ _ (lv_pnl baseId) ?_; intro base
  refine bind_pnl _ _ ?_ ?_
  · exact mapM_list_pnl indexIds _ (fun id =>
      bind_pnl _ _ (lv_pnl id) (fun _ => p_pnl _))
  intro inputs
  exact bind_pnl _ _ (semGEPValuesUsing_pnl _ _ _ _ _ _) (fun _ => bf_pnl _)

-- IsUnique: lookupValue ptr, then getAllocIdFromPtrARC (reads state only),
-- then requireArcRef and requireObjectBase (read state only), then getState,
-- then pure arithmetic, bindFresh. All three checks only read state via
-- getState + match + throw.

private theorem getAllocIdFromPtrARC_pnl (ptrVal : Value) : pnl (getAllocIdFromPtrARC ptrVal) := by
  unfold getAllocIdFromPtrARC
  refine bind_pnl _ _ gs_pnl ?_; intro s
  split
  · split
    · exact ite_pnl (p_pnl _) (throwUB_pnl _)
    · exact throwUB_pnl _
  · exact ite_pnl (throwUB_pnl _) (throwUB_pnl _)
  · exact throwUB_pnl _
  · exact throwTypeError_pnl _

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

private theorem requireObjectBase_pnl (op : String) (ptrVal : Value) (allocId : AllocId) :
    pnl (requireObjectBase op ptrVal allocId) := by
  unfold requireObjectBase
  refine bind_pnl _ _ gs_pnl ?_; intro s
  split
  · exact ite_pnl (p_pnl _) (throwUB_pnl _)
  · exact throwUB_pnl _

private theorem semIsUnique_pnl (ptrId : ValueId) : pnl (semIsUnique ptrId) := by
  unfold semIsUnique
  exact bind_pnl _ _ (lv_pnl ptrId) fun ptrVal =>
    bind_pnl _ _ (getAllocIdFromPtrARC_pnl ptrVal) fun allocId =>
      bind_pnl _ _ (requireArcRef_pnl allocId) fun _ =>
        bind_pnl _ _ (requireObjectBase_pnl "IsUnique" ptrVal allocId) fun _ =>
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

-- A Box deref reads the allocation table and binds a local; it writes no
-- memory, permission or reference count.
private theorem semBoxDeref_pnl (pointee : BoxPointee) (v : Value) :
    pnl (semBoxDeref pointee v) := by
  unfold semBoxDeref
  repeat (first
    | exact accessAlign_pnl _ _ _
    | exact checkedAccess_pnl _ _ _ _ _
    | exact rejectPartial_pnl _ _
    | exact p_pnl _
    | exact throwUB_pnl _
    | exact throwTypeError_pnl _
    | exact throwUnsupported_pnl _ _
    | exact bf_pnl _
    | (refine bind_pnl _ _ ?_ (fun value => ?_) <;> dsimp only)
    | split)

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
  --   ExtractField, InsertField, MakeAggregate, ArraySplat, ExtractElement,
  --   InsertElement,
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
  | AssertInvoke => simp [Inst.hasSideEffects, Inst.isTerminator] at hPure
  | DropInvoke => simp [Inst.hasSideEffects, Inst.isTerminator] at hPure
  | InvokeIndirect => simp [Inst.hasSideEffects, Inst.isTerminator] at hPure
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
    have h_pnl : pnl (do let ids ← semOverflow op ty lhs rhs
                         pure (InstrResult.values [ids.1, ids.2])) :=
      bind_pnl _ _ (semOverflow_pnl op ty lhs rhs) (fun _ => p_pnl _)
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
    -- Symbols and checked conversion failures refuse before binding;
    -- successful conversion only allocates a fresh local.
    by_cases hSym : val.hasSymbolAddr = true
    · simp only [stepInst, if_pos hSym, Sem.throwUnsupported, Sem.run, StateT.run,
                 throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind] at hOk
      cases hOk
    cases hChecked : constValueAtChecked ty val with
    | error error =>
      simp only [stepInst, if_neg hSym, hChecked, Sem.run, StateT.run,
                 throw, throwThe, MonadExceptOf.throw, StateT.lift, bind,
                 Except.bind] at hOk
      cases hOk
    | ok value =>
      simp only [stepInst, if_neg hSym, hChecked, Sem.run, StateT.run, Sem.bindFresh,
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
  -- A Box deref binds its operand's pointer or faults; it writes no memory.
  | BoxDeref ptrTy pointee operand fact =>
    have h_pnl : pnl (do let v ← Sem.lookupValue operand
                         semBoxDeref pointee v) :=
      bind_pnl _ _ (lv_pnl operand) fun v => semBoxDeref_pnl pointee v
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
  | MakeClosure ty func captures =>
    simp only [stepInst, Sem.throwUnsupported, Sem.run, StateT.run,
               throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind] at hOk
    cases hOk
  | MakeAggregate ty variant fields =>
    have h_pnl : pnl (do let vid ← semMakeAggregate ty variant fields
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semMakeAggregate_pnl ty variant fields)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
  | ArraySplat ty value =>
    have h_pnl : pnl (do let vid ← semArraySplat ty value
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semArraySplat_pnl ty value)
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
  -- Frame operations preserve heap/permission/ARC state; OpenFrame also
  -- updates its separate monotone lineage state. CloseFrame is side-effecting.
  | OpenFrame def_ =>
    have h_pnl : pnl (do let vid ← semOpenFrame def_
                         pure (InstrResult.value (some vid))) :=
      sem_value_pnl (semOpenFrame_pnl def_)
    simp only [stepInst] at hOk
    exact pnl_to_sel h_pnl s result hOk
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
  -- The bulk ops write memory; always side-effecting (WS3.20).
  | MemCopy dst src bytes overlap =>
    simp [Inst.hasSideEffects] at hPure
  | MemSet dst byte bytes =>
    simp [Inst.hasSideEffects] at hPure
  -- Drop runs a destructor: it frees and can run arbitrary user code, so it is
  -- observable and never DCE-eligible. Discharged by contradiction with hPure,
  -- exactly as Dealloc is.
  | Drop ty ptr =>
    simp [Inst.hasSideEffects] at hPure
  | CallCannotUnwind callee args =>
    simp [Inst.hasSideEffects] at hPure
  | CallIndirectCannotUnwind callee sig args conv =>
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
    cases hOk
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
        | InvokeIndirectReq addr sig callArgs nd nargs ud => exact hOk
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

    Typed ABI metadata is explicitly excluded until transport semantics exist.
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
    (hFn : ctx.functions calleeId = some callee)
    (hAbi : callee.body.abi = none) :
    Sem.run (runCallReq ctx fuel callDepth calleeId callArgs) s
        = .ok (retVals, sEnd)
      ↔ callArgs.length = callee.body.paramTys.length ∧
        callArgs.any Value.isPoison = false ∧
        retVals.length = callee.body.returnTys.length ∧
        retVals.any Value.isPoison = false ∧
        ∃ sCalleeEnd,
          Sem.run (stepNWithContext (ctx.forFunction callee) fuel callDepth
              callee.cfg callee.entryBlock callArgs)
            { s with locals := ValueMap.empty, nextValueId := 0 }
            = .ok (retVals, sCalleeEnd) ∧
          sEnd = restoreFrame sCalleeEnd (saveFrame s none) [] := by
  constructor
  · exact runCallReq_ok_decomp ctx fuel callDepth calleeId callee callArgs
      s sEnd retVals hFn
  · intro h
    obtain ⟨hArity, hArgsClean, hRet, hRetClean, sCalleeEnd, hInline, hEnd⟩ := h
    subst hEnd
    exact runCallReq_ok_of_inline ctx fuel callDepth calleeId callee callArgs
      s sCalleeEnd retVals hFn hAbi hArity hRet hArgsClean hRetClean hInline

-- =================================================================
-- Behaviour refinement: theorems (WS8.15)
-- =================================================================

/-!
## Behaviour refinement

What holds under `behaviour_refines`:

* `id_refines`, `compose_refines` — the analogues of `id_transform_preserving`
  and `compose_preserving`.
* `block_transform_lifts_to_cfg_refines` — the analogue of
  `block_transform_lifts_to_cfg`, under the exact-on-non-UB block hypothesis
  `block_transform_refines`.
* `constant_fold_refines` — the constant-fold instance.
* `unreachableToReturn_refines` — a UB-exploiting rewrite (`Unreachable` to
  `Return []`) is admitted: UB is top.
* `inlining_error_transfer` / `inlining_error_cases` — the trap half of
  `inlining_preserving` (which is itself an iff over returning runs).

What does NOT hold under it:

* `block_transform_lifts_to_cfg` with its `.ok`-only block hypothesis
  (`block_transform_lifts_to_cfg_not_refines`).
* `semantics_preserving` and `semantics_preserving_weak` do not imply it
  (`semantics_preserving_not_imp_refines`,
  `semantics_preserving_weak_not_imp_refines`). Three transforms separate
  them: trap-to-return (`assertElim`), trap-to-divergence (`panicToLoop`) and
  divergence-to-return (`divToRet`, the `core-arch-0916-a/24` shape).
* The splice form of inlining is not stated under either notion (Future work
  item 4).
* Nothing here constrains a body whose calls are executed: a transform that
  retargets a call is a `behaviour_refines` transform and is refused by the
  in-context notion (`TransformRefinementCtx.lean`:
  `callRetarget_refines`, `callRetarget_not_refines_in`). That module states
  `behaviour_refines_in` over `stepNWithContext`, re-proves the UB-top rewrite
  and the trap-removal refusal there, and gives the frame-discipline inlining
  theorem at the behaviour level (`inlining_behaves_iff`).
-/

/-- A single fuel-bounded run never exhibits `diverges` by itself. -/
theorem Outcome.ofRun_ne_diverges (r : Except SemError (List Value × MachineState)) :
    Outcome.ofRun r ≠ some .diverges := by
  cases r with
  | ok v => simp [Outcome.ofRun]
  | error e => cases e <;> simp [Outcome.ofRun]

/-- The only run with no behaviour of its own is `outOfFuel`. -/
theorem Outcome.ofRun_eq_none_iff (r : Except SemError (List Value × MachineState)) :
    Outcome.ofRun r = none ↔ r = .error .outOfFuel := by
  cases r with
  | ok v => simp [Outcome.ofRun]
  | error e => cases e <;> simp [Outcome.ofRun]

/-- Every program has at least one behaviour from every input: either some
    fuel stops the run, or it runs out of fuel at every fuel and so diverges.
    This is the property a terminating-outcomes-only definition lacks. -/
theorem behaves_nonempty (cfg : CFG) (pc : BlockId) (args : List Value)
    (s : MachineState) : ∃ o, Behaves cfg pc args s o := by
  by_cases hDiv : ∀ fuel, Sem.run (stepN fuel cfg pc args) s = .error .outOfFuel
  · exact ⟨.diverges, Or.inr ⟨rfl, hDiv⟩⟩
  · have ⟨fuel, hFuel⟩ := Classical.not_forall.mp hDiv
    cases hO : Outcome.ofRun (Sem.run (stepN fuel cfg pc args) s) with
    | none => exact absurd ((Outcome.ofRun_eq_none_iff _).mp hO) hFuel
    | some o => exact ⟨o, Or.inl ⟨fuel, hO⟩⟩

/-- The UB-freeness premise of `behaviour_refines`, spelled as in the
    roadmap: no fuel gives the source `.error (.ub _)`. -/
theorem not_behaves_ub_iff (cfg : CFG) (pc : BlockId) (args : List Value)
    (s : MachineState) :
    ¬ Behaves cfg pc args s .ub ↔
      ∀ fuel msg, Sem.run (stepN fuel cfg pc args) s ≠ .error (.ub msg) := by
  constructor
  · intro h fuel msg hRun
    exact h (Or.inl ⟨fuel, by rw [hRun]; rfl⟩)
  · intro h hB
    rcases hB with ⟨fuel, hO⟩ | ⟨hEq, _⟩
    · cases hR : Sem.run (stepN fuel cfg pc args) s with
      | ok v => rw [hR] at hO; simp [Outcome.ofRun] at hO
      | error e =>
        rw [hR] at hO
        cases e with
        | ub msg => exact h fuel msg hR
        | _ => simp [Outcome.ofRun] at hO
    · cases hEq

/-- Programs whose runs agree at every fuel have the same behaviours. -/
theorem behaves_congr (cfg1 cfg2 : CFG) (pc : BlockId) (args : List Value)
    (s : MachineState)
    (hEq : ∀ fuel, Sem.run (stepN fuel cfg1 pc args) s
      = Sem.run (stepN fuel cfg2 pc args) s) (o : Outcome) :
    Behaves cfg1 pc args s o → Behaves cfg2 pc args s o := by
  intro h
  rcases h with ⟨fuel, hO⟩ | ⟨hO, hDiv⟩
  · exact Or.inl ⟨fuel, by rw [← hEq]; exact hO⟩
  · exact Or.inr ⟨hO, fun fuel => by rw [← hEq]; exact hDiv fuel⟩

/-- The identity transform is a behaviour refinement (the analogue of
    `id_transform_preserving`). -/
theorem id_refines : behaviour_refines (fun cfg => cfg) := by
  intro cfg pc args s _ o h
  exact h

/-- Behaviour refinement composes (the analogue of `compose_preserving`).
    The UB-freeness of the intermediate program `t1 cfg` is not assumed: it
    follows from `h1`, because a UB behaviour of `t1 cfg` would be a UB
    behaviour of the UB-free source. -/
theorem compose_refines (t1 t2 : CFG → CFG)
    (h1 : behaviour_refines t1) (h2 : behaviour_refines t2) :
    behaviour_refines (fun cfg => t2 (t1 cfg)) := by
  intro cfg pc args s hNoUB o h
  have hNoUB1 : ¬ Behaves (t1 cfg) pc args s .ub :=
    fun hUB => hNoUB (h1 cfg pc args s hNoUB .ub hUB)
  exact h1 cfg pc args s hNoUB o (h2 (t1 cfg) pc args s hNoUB1 o h)

-- -----------------------------------------------------------------
-- Behaviour refinement: block-level lifting
-- -----------------------------------------------------------------

/-- A block transform refines on `cfg` when, for every block of `cfg` and
    every run of that block that is not UB, the transformed block's run is
    EXACTLY the source block's run (returns, traps and state alike). This
    replaces the `.ok`-only `block_transform_preserving`, which does not lift
    to `behaviour_refines` (`block_transform_lifts_to_cfg_not_refines`). -/
def block_transform_refines (transform : BasicBlock → BasicBlock) (cfg : CFG) : Prop :=
  ∀ bid, match cfg bid with
    | none => True
    | some block =>
      ∀ args s, (∀ msg, Sem.run (stepBlock block args) s ≠ .error (.ub msg)) →
        Sem.run (stepBlock (transform block) args) s = Sem.run (stepBlock block args) s

/-- Helper: at a fuel where the source run is not UB, the pointwise
    transformed CFG runs exactly like the source. Every block the source
    executes before stopping is then not UB either, so `hBlock` applies at
    each step. -/
private theorem stepN_block_refines_aux
    (transform : BasicBlock → BasicBlock) (fuel : Nat)
    (cfg : CFG) (pc : BlockId) (args : List Value) (s : MachineState)
    (hBlock : block_transform_refines transform cfg)
    (hNoUB : ∀ msg, Sem.run (stepN fuel cfg pc args) s ≠ .error (.ub msg)) :
    Sem.run (stepN fuel (fun bid => (cfg bid).map transform) pc args) s
      = Sem.run (stepN fuel cfg pc args) s := by
  induction fuel generalizing pc args s with
  | zero => rfl
  | succ n ih =>
    simp only [stepN] at hNoUB ⊢
    cases hCfg : cfg pc with
    | none => simp only [hCfg, Option.map]
    | some block =>
      simp only [hCfg, Option.map] at hNoUB ⊢
      rw [sem_run_bind_eq] at hNoUB ⊢
      rw [sem_run_bind_eq]
      have hBP := hBlock pc
      simp only [hCfg] at hBP
      have hBlockNoUB : ∀ msg, Sem.run (stepBlock block args) s ≠ .error (.ub msg) := by
        intro msg hSB
        rw [hSB] at hNoUB
        exact hNoUB msg rfl
      rw [hBP args s hBlockNoUB]
      cases hSB : Sem.run (stepBlock block args) s with
      | error e => rfl
      | ok val =>
        obtain ⟨sr, s'⟩ := val
        rw [hSB] at hNoUB
        simp only at hNoUB ⊢
        cases sr with
        | Continue nextPc nextArgs => exact ih nextPc nextArgs s' hNoUB
        | _ => rfl

/-- **Lifting under behaviour refinement** (the refinement analogue of
    `block_transform_lifts_to_cfg`): a block transform that refines on every
    CFG lifts to a CFG transform that is a behaviour refinement. -/
theorem block_transform_lifts_to_cfg_refines (transform : BasicBlock → BasicBlock)
    (hBlock : ∀ c : CFG, block_transform_refines transform c) :
    behaviour_refines (fun cfg bid => (cfg bid).map transform) := by
  intro cfg pc args s hNoUB o h
  have hNoUB' := (not_behaves_ub_iff cfg pc args s).mp hNoUB
  exact behaves_congr _ _ pc args s
    (fun fuel => stepN_block_refines_aux transform fuel cfg pc args s
      (hBlock cfg) (hNoUB' fuel)) o h

-- -----------------------------------------------------------------
-- Behaviour refinement: the constant-fold instance
-- -----------------------------------------------------------------

/-- Rewrite every body instruction of a block with `g`. -/
def mapBody (g : Inst → Inst) (block : BasicBlock) : BasicBlock :=
  { block with body := block.body.map g }

/-- `for` over a mapped list is `for` over the list with the rewrite folded
    into the loop body. -/
private theorem forIn_map_eq {m : Type → Type} [Monad m] {α β : Type}
    (l : List α) (g : α → α) (b : β) (F : α → β → m (ForInStep β)) :
    forIn (l.map g) b F = forIn l b (fun a => F (g a)) := by
  induction l generalizing b with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.forIn_cons]
    congr 1
    funext step
    cases step with
    | done b' => rfl
    | yield b' => exact ih b'

/-- Rewriting body instructions by an `inst_equiv`-preserving `g` leaves a
    block's step unchanged, on every input and outcome. -/
theorem stepBlock_mapBody (g : Inst → Inst) (hg : ∀ i, inst_equiv i (g i))
    (block : BasicBlock) (args : List Value) :
    stepBlock (mapBody g block) args = stepBlock block args := by
  have hstep : ∀ i, stepInst (g i) = stepInst i := fun i => funext fun s => (hg i s).symm
  simp only [stepBlock, mapBody]
  rw [forIn_map_eq]
  simp only [hstep]

/-- Any `inst_equiv`-justified body rewrite is a behaviour refinement. -/
theorem mapBody_refines (g : Inst → Inst) (hg : ∀ i, inst_equiv i (g i)) :
    behaviour_refines (fun cfg bid => (cfg bid).map (mapBody g)) := by
  apply block_transform_lifts_to_cfg_refines
  intro c bid
  cases c bid with
  | none => trivial
  | some block =>
    intro args s _
    rw [stepBlock_mapBody g hg]

open Classical in
/-- The constant-fold rewrite: every occurrence of `BinOp op ty lhs rhs`
    becomes `Const ty constResult`. (`Inst` has no decidable equality, so
    the test is classical; the transform is a proof object, not code.) -/
noncomputable def foldBinOp (op : BinOp) (ty : Ty) (lhs rhs : ValueId)
    (constResult : Constant) (i : Inst) : Inst :=
  if i = .BinOp op ty lhs rhs then .Const ty constResult else i

/-- **Positive instance: constant folding is a behaviour refinement.** The
    instruction-level `constant_fold_binop` justification, lifted through
    `block_transform_lifts_to_cfg_refines`. -/
theorem constant_fold_refines (op : BinOp) (ty : Ty) (lhs rhs : ValueId)
    (constResult : Constant)
    (hFold : inst_equiv (.BinOp op ty lhs rhs) (.Const ty constResult)) :
    behaviour_refines
      (fun cfg bid => (cfg bid).map (mapBody (foldBinOp op ty lhs rhs constResult))) := by
  apply mapBody_refines
  intro i
  unfold foldBinOp
  by_cases h : i = .BinOp op ty lhs rhs
  · rw [if_pos h, h]
    exact constant_fold_binop op ty lhs rhs constResult hFold
  · rw [if_neg h]
    exact inst_equiv_refl i

-- -----------------------------------------------------------------
-- Counter-models: what the `.ok`-only notions accept
-- -----------------------------------------------------------------

/-- Recognise an `Assert`. -/
def Inst.isAssert : Inst → Bool
  | .Assert _ _ _ => true
  | _ => false

/-- Delete every `Assert` from a block body. -/
def dropAsserts (block : BasicBlock) : BasicBlock :=
  { block with body := block.body.filter (fun i => !i.isAssert) }

/-- `assertElim`: delete every `Assert` in the program. Under panic=abort a
    failing assertion is a DEFINED trap, so this changes observable
    behaviour. -/
def assertElim (cfg : CFG) : CFG := fun bid => (cfg bid).map dropAsserts

/-- Filtering out loop elements whose step always succeeds as a no-op
    keeps a successful `for` run successful with the same result. -/
private theorem forIn_filter_ok {F : Inst → PUnit → Sem (ForInStep PUnit)}
    (p : Inst → Bool)
    (hF : ∀ a s r, p a = false → Sem.run (F a PUnit.unit) s = .ok r →
      r = (ForInStep.yield PUnit.unit, s))
    (l : List Inst) (s : MachineState) (r : PUnit × MachineState)
    (h : Sem.run (forIn l PUnit.unit F) s = .ok r) :
    Sem.run (forIn (l.filter p) PUnit.unit F) s = .ok r := by
  induction l generalizing s with
  | nil => exact h
  | cons a as ih =>
    rw [List.forIn_cons, sem_run_bind_eq] at h
    rw [List.filter_cons]
    cases hp : p a with
    | true =>
      simp only [if_pos]
      rw [List.forIn_cons, sem_run_bind_eq]
      cases hFa : Sem.run (F a PUnit.unit) s with
      | error e => rw [hFa] at h; cases h
      | ok v =>
        rw [hFa] at h
        obtain ⟨step, s1⟩ := v
        cases step with
        | done b => exact h
        | yield b => exact ih s1 h
    | false =>
      simp only [Bool.false_eq_true, if_false]
      cases hFa : Sem.run (F a PUnit.unit) s with
      | error e => rw [hFa] at h; cases h
      | ok v =>
        rw [hFa] at h
        have hv := hF a s v hp hFa
        subst hv
        exact ih s h

/-- A successful `Assert` leaves the state unchanged and its condition was
    `true`, whatever its kind. -/
theorem stepInst_assert_ok (c : ValueId) (k : AssertKind) (site : Option PanicSite)
    (s : MachineState) (r : InstrResult × MachineState)
    (hr : Sem.run (stepInst (.Assert c k site)) s = .ok r) :
    r = (.value none, s) ∧ s.lookupValue c = some (.bool true) := by
  simp only [stepInst, sem_run_bind_eq] at hr
  cases hv : s.lookupValue c with
  | none =>
    have hL : Sem.run (Sem.lookupValue c) s = .error (.typeError s!"undefined SSA value: {repr c}") := by
      simp only [Sem.run, Sem.lookupValue, Sem.getState, StateT.run, StateT.get,
        bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, hv]
      rfl
    rw [hL] at hr; cases hr
  | some v =>
    have hL : Sem.run (Sem.lookupValue c) s = .ok (v, s) := by
      simp only [Sem.run, Sem.lookupValue, Sem.getState, StateT.run, StateT.get,
        bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, hv]
    rw [hL] at hr
    simp only [sem_run_bind_eq] at hr
    cases v with
    | «partial» bs => cases hr
    | bool b =>
      cases b with
      | true => cases hr; exact ⟨rfl, rfl⟩
      | false =>
        exact absurd (show Sem.run (semAssertFail k site : Sem InstrResult) s = .ok r from hr)
          (semAssertFail_run_not_ok k site s r)
    | _ => cases hr

/-- A successful assertion is a no-op, so deleting assertions preserves
    every SUCCESSFUL block run (the `.ok`-only block notion). -/
theorem dropAsserts_block_preserving (c : CFG) :
    block_transform_preserving dropAsserts c := by
  intro bid
  cases c bid with
  | none => trivial
  | some block =>
    intro args s result h
    simp only [stepBlock, dropAsserts] at h ⊢
    rw [sem_run_bind_eq] at h ⊢
    cases hP : Sem.run (bindBlockParams block.params args) s with
    | error e => rw [hP] at h; cases h
    | ok v =>
      rw [hP] at h
      obtain ⟨u, s1⟩ := v
      simp only at h ⊢
      rw [sem_run_bind_eq] at h ⊢
      cases hB : Sem.run (forIn block.body PUnit.unit _) s1 with
      | error e => rw [hB] at h; cases h
      | ok w =>
        rw [hB] at h
        rw [forIn_filter_ok _ _ block.body s1 w hB]
        exact h
        intro a s r hp hr
        cases a <;> simp [Inst.isAssert] at hp
        rename_i c k site
        simp only [sem_run_bind_eq] at hr
        cases hS : Sem.run (stepInst (.Assert c k site)) s with
        | error e => rw [hS] at hr; cases hr
        | ok v =>
          obtain ⟨hv, _⟩ := stepInst_assert_ok c k site s v hS
          subst hv
          rw [hS] at hr
          cases hr; rfl

/-- **Mutation control: the old notion accepts assertion deletion.** Fuel
    counts blocks, so deleting an `Assert` inside a block keeps the fuel,
    and `semantics_preserving` holds. -/
theorem assertElim_semantics_preserving : semantics_preserving assertElim :=
  block_transform_lifts_to_cfg dropAsserts (fun _ => none) dropAsserts_block_preserving

/-- Counter-model source for `assertElim`: block 0 asserts its `Bool`
    parameter and returns. Entered with `false`, it panics. -/
def failingAssertCFG : CFG := fun bid =>
  if bid = ⟨0⟩ then
    some { params := [(⟨0⟩, .Bool)], body := [.Assert ⟨0⟩ .Unspecified none], terminator := .Return [] }
  else none

/-- The source panics at every positive fuel. -/
theorem failingAssertCFG_panics (n : Nat) (s : MachineState) :
    Sem.run (stepN (n + 1) failingAssertCFG ⟨0⟩ [.bool false]) s
      = .error (.panic "assertion failed" none) := rfl

/-- The asserts-deleted target returns. -/
theorem assertElim_failingAssertCFG_returns :
    ∃ r, Sem.run (stepN 1 (assertElim failingAssertCFG) ⟨0⟩ [.bool false])
      MachineState.empty = .ok r := ⟨_, rfl⟩

/-- Zero fuel is `outOfFuel`. -/
theorem stepN_zero_run (cfg : CFG) (pc : BlockId) (args : List Value) (s : MachineState) :
    Sem.run (stepN 0 cfg pc args) s = .error .outOfFuel := rfl

/-- A program that panics at every positive fuel has exactly one behaviour,
    that panic. -/
theorem behaves_of_always_panics (cfg : CFG) (pc : BlockId) (args : List Value)
    (s : MachineState) (msg : String) (site : Option PanicOutcomeSite)
    (hPanic : ∀ n, Sem.run (stepN (n + 1) cfg pc args) s = .error (.panic msg site))
    (o : Outcome) (h : Behaves cfg pc args s o) : o = .panics msg site := by
  rcases h with ⟨fuel, hO⟩ | ⟨_, hDiv⟩
  · cases fuel with
    | zero => rw [stepN_zero_run] at hO; simp [Outcome.ofRun] at hO
    | succ n => rw [hPanic n] at hO; simp [Outcome.ofRun] at hO; exact hO.symm
  · have := hDiv 1
    rw [hPanic 0] at this
    cases this

/-- **Negative twin: assertion deletion is NOT a behaviour refinement.** The
    source `failingAssertCFG` panics; the target returns. -/
theorem assertElim_not_refines : ¬ behaviour_refines assertElim := by
  intro h
  have hNoUB : ¬ Behaves failingAssertCFG ⟨0⟩ [.bool false] MachineState.empty .ub := by
    intro hB
    have := behaves_of_always_panics _ _ _ _ _ _
      (fun n => failingAssertCFG_panics n MachineState.empty) _ hB
    cases this
  obtain ⟨r, hr⟩ := assertElim_failingAssertCFG_returns
  have hSrc := h failingAssertCFG ⟨0⟩ [.bool false] MachineState.empty hNoUB
    (.returns r) (Or.inl ⟨1, by rw [hr]; rfl⟩)
  have := behaves_of_always_panics _ _ _ _ _ _
    (fun n => failingAssertCFG_panics n MachineState.empty) _ hSrc
  cases this

/-- `block_transform_lifts_to_cfg` does NOT hold under `behaviour_refines`:
    its `.ok`-only block hypothesis admits `dropAsserts`, whose lifting is not
    a refinement. Use `block_transform_lifts_to_cfg_refines`. -/
theorem block_transform_lifts_to_cfg_not_refines :
    ¬ (∀ transform : BasicBlock → BasicBlock,
        (∀ c : CFG, block_transform_preserving transform c) →
        behaviour_refines (fun cfg bid => (cfg bid).map transform)) :=
  fun hLift => assertElim_not_refines (hLift dropAsserts dropAsserts_block_preserving)

/-- A self-loop: block 0 branches to itself. -/
def loopCFG : CFG := fun bid =>
  if bid = ⟨0⟩ then some { params := [], body := [], terminator := .Br ⟨0⟩ [] } else none

/-- `loopCFG` runs out of fuel at every fuel, from every state. -/
theorem loopCFG_diverges (fuel : Nat) (s : MachineState) :
    Sem.run (stepN fuel loopCFG ⟨0⟩ []) s = .error .outOfFuel := by
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
    have hStep : ∃ s', Sem.run (stepN (n + 1) loopCFG ⟨0⟩ []) s
        = Sem.run (stepN n loopCFG ⟨0⟩ []) s' := ⟨_, rfl⟩
    obtain ⟨s', hs'⟩ := hStep
    rw [hs']
    exact ih s'

/-- A terminating, UB-free source: block 0 returns. -/
def returnCFG : CFG := fun bid =>
  if bid = ⟨0⟩ then some { params := [], body := [], terminator := .Return [] } else none

/-- `returnCFG` returns at every positive fuel. -/
theorem returnCFG_returns (n : Nat) (s : MachineState) :
    ∃ r, Sem.run (stepN (n + 1) returnCFG ⟨0⟩ []) s = .ok r := ⟨_, rfl⟩

/-- **Mutation control: divergence is an observable behaviour.** Replacing a
    terminating source with a self-loop is not a refinement. A definition
    weakened back to "every TERMINATING target outcome is a source outcome"
    would accept this transform vacuously, because the loop never
    terminates. -/
theorem loop_not_refines : ¬ behaviour_refines (fun _ => loopCFG) := by
  intro h
  have hNoUB : ¬ Behaves returnCFG ⟨0⟩ [] MachineState.empty .ub := by
    rw [not_behaves_ub_iff]
    intro fuel msg hRun
    cases fuel with
    | zero => rw [stepN_zero_run] at hRun; cases hRun
    | succ n =>
      obtain ⟨r, hr⟩ := returnCFG_returns n MachineState.empty
      rw [hr] at hRun; cases hRun
  have hSrc := h returnCFG ⟨0⟩ [] MachineState.empty hNoUB .diverges
    (Or.inr ⟨rfl, fun fuel => loopCFG_diverges fuel MachineState.empty⟩)
  rcases hSrc with ⟨fuel, hO⟩ | ⟨_, hDiv⟩
  · exact Outcome.ofRun_ne_diverges _ hO
  · obtain ⟨r, hr⟩ := returnCFG_returns 0 MachineState.empty
    rw [hDiv 1] at hr
    cases hr

/-- A successful `for` over `l1 ++ l2`, whose steps always yield, splits
    into a successful run over `l1` followed by one over `l2`. -/
private theorem forIn_append_split {F : Inst → PUnit → Sem (ForInStep PUnit)}
    (hF : ∀ a s r, Sem.run (F a PUnit.unit) s = .ok r → r.1 = ForInStep.yield PUnit.unit)
    (l1 l2 : List Inst) (s : MachineState) (r : PUnit × MachineState)
    (h : Sem.run (forIn (l1 ++ l2) PUnit.unit F) s = .ok r) :
    ∃ s1, Sem.run (forIn l1 PUnit.unit F) s = .ok (PUnit.unit, s1) ∧
      Sem.run (forIn l2 PUnit.unit F) s1 = .ok r := by
  induction l1 generalizing s with
  | nil => exact ⟨s, rfl, h⟩
  | cons a as ih =>
    rw [List.cons_append, List.forIn_cons, sem_run_bind_eq] at h
    cases hFa : Sem.run (F a PUnit.unit) s with
    | error e => rw [hFa] at h; cases h
    | ok v =>
      rw [hFa] at h
      obtain ⟨step, s'⟩ := v
      have hy : step = ForInStep.yield PUnit.unit := hF a s _ hFa
      subst hy
      obtain ⟨s1, h1, h2⟩ := ih s' h
      refine ⟨s1, ?_, h2⟩
      rw [List.forIn_cons, sem_run_bind_eq, hFa]
      exact h1

/-- `Sem.lookupValue` of a bound value succeeds without changing state. -/
theorem lookupValue_run_some (c : ValueId) (s : MachineState) (v : Value)
    (hv : s.lookupValue c = some v) : Sem.run (Sem.lookupValue c) s = .ok (v, s) := by
  simp only [Sem.run, Sem.lookupValue, Sem.getState, StateT.run, StateT.get,
    bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, hv]

/-- A `CondBr` whose condition is `true` steps exactly like a `Br` to its
    then-edge. -/
theorem condBr_run_eq_br (c : ValueId) (target : BlockId) (targetArgs : List ValueId)
    (elseTarget : BlockId) (elseArgs : List ValueId) (s : MachineState)
    (hc : s.lookupValue c = some (.bool true)) :
    Sem.run (stepInst (.CondBr c target targetArgs elseTarget elseArgs)) s
      = Sem.run (stepInst (.Br target targetArgs)) s := by
  simp only [stepInst, semCondBr, semBr, sem_run_bind_eq, lookupValue_run_some c s _ hc]
  rfl

/-- Turn a trailing `Assert c` before a `Br target args` into the branch
    condition: `CondBr c target args bid params`. The failing edge re-enters
    the block itself with its own parameters, so a failing assertion becomes
    a self-loop instead of a panic. Other blocks are unchanged. -/
def panicToLoopBlock (bid : BlockId) (block : BasicBlock) : BasicBlock :=
  match block.body.reverse, block.terminator with
  | .Assert c _ _ :: rpre, .Br target targetArgs =>
    { block with
      body := rpre.reverse
      terminator := .CondBr c target targetArgs bid (block.params.map Prod.fst) }
  | _, _ => block

/-- `panicToLoop`: apply `panicToLoopBlock` at every block. -/
def panicToLoop (cfg : CFG) : CFG := fun bid => (cfg bid).map (panicToLoopBlock bid)

/-- On every SUCCESSFUL run the assertion held, so the `CondBr` takes the
    then-edge exactly as the `Br` did. -/
theorem panicToLoopBlock_preserving (bid : BlockId) (block : BasicBlock)
    (args : List Value) (s : MachineState) (result : StepResult × MachineState)
    (h : Sem.run (stepBlock block args) s = .ok result) :
    Sem.run (stepBlock (panicToLoopBlock bid block) args) s = .ok result := by
  unfold panicToLoopBlock
  split
  · rename_i c k site rpre target targetArgs hRev hTerm
    have hBody : block.body = rpre.reverse ++ [.Assert c k site] := by
      rw [← List.reverse_reverse block.body, hRev, List.reverse_cons]
    simp only [stepBlock] at h ⊢
    rw [hBody, hTerm] at h
    rw [sem_run_bind_eq] at h ⊢
    cases hP : Sem.run (bindBlockParams block.params args) s with
    | error e => rw [hP] at h; cases h
    | ok v =>
      rw [hP] at h
      obtain ⟨u, s1⟩ := v
      simp only at h ⊢
      rw [sem_run_bind_eq] at h ⊢
      cases hB : Sem.run (forIn (rpre.reverse ++ [.Assert c k site]) PUnit.unit _) s1 with
      | error e => rw [hB] at h; cases h
      | ok w =>
        rw [hB] at h
        obtain ⟨s2, h1, h2⟩ := forIn_append_split (by
          intro a st r hr
          rw [sem_run_bind_eq] at hr
          cases hI : Sem.run (stepInst a) st with
          | error e => rw [hI] at hr; cases hr
          | ok v =>
            rw [hI] at hr
            obtain ⟨ir, st'⟩ := v
            cases ir with
            | value x => cases hr; rfl
            | values xs => cases hr; rfl
            | terminator sr => cases sr <;> cases hr)
          rpre.reverse [.Assert c k site] s1 w hB
        rw [List.forIn_cons, sem_run_bind_eq] at h2
        simp only [sem_run_bind_eq] at h2
        cases hA : Sem.run (stepInst (.Assert c k site)) s2 with
        | error e => rw [hA] at h2; cases h2
        | ok ir =>
          obtain ⟨hIr, hc⟩ := stepInst_assert_ok c k site s2 ir hA
          subst hIr
          rw [hA] at h2
          cases h2
          rw [h1]
          simp only at h ⊢
          rw [sem_run_bind_eq] at h ⊢
          rw [condBr_run_eq_br c target targetArgs bid _ s2 hc]
          exact h
  · exact h

/-- The `stepN_block_transform_aux` induction for a block transform that
    may depend on the block's id. -/
private theorem stepN_blockAt_transform_aux
    (transform : BlockId → BasicBlock → BasicBlock) (fuel : Nat)
    (cfg : CFG) (pc : BlockId) (args : List Value) (s : MachineState)
    (result : List Value × MachineState)
    (hBlock : ∀ bid block args s r, cfg bid = some block →
      Sem.run (stepBlock block args) s = .ok r →
      Sem.run (stepBlock (transform bid block) args) s = .ok r)
    (hOk : Sem.run (stepN fuel cfg pc args) s = .ok result) :
    Sem.run (stepN fuel (fun bid => (cfg bid).map (transform bid)) pc args) s
      = .ok result := by
  induction fuel generalizing pc args s with
  | zero => cases hOk
  | succ n ih =>
    simp only [stepN] at hOk ⊢
    cases hCfg : cfg pc with
    | none =>
      simp only [hCfg, Option.map] at hOk ⊢
      exact hOk
    | some block =>
      simp only [hCfg, Option.map] at hOk ⊢
      rw [sem_run_bind_eq] at hOk ⊢
      cases hSB : Sem.run (stepBlock block args) s with
      | error e => rw [hSB] at hOk; cases hOk
      | ok val =>
        rw [hSB] at hOk
        rw [hBlock pc block args s val hCfg hSB]
        obtain ⟨sr, s'⟩ := val
        simp only at hOk ⊢
        cases sr with
        | Continue nextPc nextArgs => exact ih nextPc nextArgs s' hOk
        | _ => exact hOk

/-- Equal-fuel preservation implies the weak form. -/
theorem semantics_preserving_weak_of_preserving (t : CFG → CFG)
    (h : semantics_preserving t) : semantics_preserving_weak t := by
  intro cfg pc args s result ⟨fuel, hOk⟩
  exact ⟨fuel, h cfg pc args s fuel result hOk⟩

/-- `panicToLoop` preserves every returning run at equal fuel. (The rewrite
    stays inside the block, so the strong form holds as well as the weak
    one.) -/
theorem panicToLoop_semantics_preserving : semantics_preserving panicToLoop := by
  intro cfg pc args s fuel result hOk
  exact stepN_blockAt_transform_aux panicToLoopBlock fuel cfg pc args s result
    (fun bid block args s r _ h => panicToLoopBlock_preserving bid block args s r h) hOk

/-- **Mutation control: the old weak notion accepts `panicToLoop`.** It says
    nothing once the source panics. -/
theorem panicToLoop_semantics_preserving_weak : semantics_preserving_weak panicToLoop :=
  semantics_preserving_weak_of_preserving panicToLoop panicToLoop_semantics_preserving

/-- Counter-model source for `panicToLoop`: block 0 asserts its `Bool`
    parameter and branches to block 1, which returns. Entered with `false`,
    it panics. -/
def failingAssertBrCFG : CFG := fun bid =>
  if bid = ⟨0⟩ then
    some { params := [(⟨0⟩, .Bool)], body := [.Assert ⟨0⟩ .Unspecified none], terminator := .Br ⟨1⟩ [] }
  else if bid = ⟨1⟩ then
    some { params := [], body := [], terminator := .Return [] }
  else none

/-- The source panics at every positive fuel. -/
theorem failingAssertBrCFG_panics (n : Nat) (s : MachineState) :
    Sem.run (stepN (n + 1) failingAssertBrCFG ⟨0⟩ [.bool false]) s
      = .error (.panic "assertion failed" none) := rfl

/-- The `panicToLoop` target diverges: the failing edge re-enters block 0
    with `false` forever. -/
theorem panicToLoop_failingAssertBrCFG_diverges (fuel : Nat) (s : MachineState) :
    Sem.run (stepN fuel (panicToLoop failingAssertBrCFG) ⟨0⟩ [.bool false]) s
      = .error .outOfFuel := by
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
    have hStep : ∃ s', Sem.run (stepN (n + 1) (panicToLoop failingAssertBrCFG) ⟨0⟩ [.bool false]) s
        = Sem.run (stepN n (panicToLoop failingAssertBrCFG) ⟨0⟩ [.bool false]) s' := ⟨_, rfl⟩
    obtain ⟨s', hs'⟩ := hStep
    rw [hs']
    exact ih s'

/-- **Mutation control: `panicToLoop` is NOT a behaviour refinement.** The
    source panics and the target diverges. This pins the divergence clause
    on its own: the source never returns, so no `.ok`-only notion can see the
    difference. -/
theorem panicToLoop_not_refines : ¬ behaviour_refines panicToLoop := by
  intro h
  have hPanic := fun n => failingAssertBrCFG_panics n MachineState.empty
  have hNoUB : ¬ Behaves failingAssertBrCFG ⟨0⟩ [.bool false] MachineState.empty .ub := by
    intro hB
    cases behaves_of_always_panics _ _ _ _ _ _ hPanic _ hB
  have hSrc := h failingAssertBrCFG ⟨0⟩ [.bool false] MachineState.empty hNoUB .diverges
    (Or.inr ⟨rfl, fun fuel => panicToLoop_failingAssertBrCFG_diverges fuel MachineState.empty⟩)
  cases behaves_of_always_panics _ _ _ _ _ _ hPanic _ hSrc


/-- Block 0 is `Unreachable`: UB at every positive fuel. -/
def unreachableCFG : CFG := fun bid =>
  if bid = ⟨0⟩ then some { params := [], body := [], terminator := .Unreachable } else none

/-- `unreachableCFG` is UB at every positive fuel. -/
theorem unreachableCFG_ub (n : Nat) (s : MachineState) :
    Sem.run (stepN (n + 1) unreachableCFG ⟨0⟩ []) s = .error (.ub "reached unreachable") := rfl

/-- **Mutation control: UB is an outcome of the target too.** Replacing a
    UB-free source with UB is not a refinement. A definition that dropped
    `ub` from the target's behaviours would accept it, because a UB run has
    no other behaviour. -/
theorem ub_introduction_not_refines : ¬ behaviour_refines (fun _ => unreachableCFG) := by
  intro h
  have hNoUB : ¬ Behaves returnCFG ⟨0⟩ [] MachineState.empty .ub := by
    rw [not_behaves_ub_iff]
    intro fuel msg hRun
    cases fuel with
    | zero => rw [stepN_zero_run] at hRun; cases hRun
    | succ n =>
      obtain ⟨r, hr⟩ := returnCFG_returns n MachineState.empty
      rw [hr] at hRun; cases hRun
  exact hNoUB (h returnCFG ⟨0⟩ [] MachineState.empty hNoUB .ub
    (Or.inl ⟨1, by rw [unreachableCFG_ub 0]; rfl⟩))

/-- **Inlining under behaviour refinement, trap half.** Every non-return
    outcome of the callee body run inline (UB, panic, type error,
    unsupported, out of fuel) is the Call's outcome too, verbatim. Together
    with `inlining_preserving` (the return half), the frame-discipline form
    transfers every behaviour of the inline run to the Call. The arguments
    must be poison-free: poison may not cross a call boundary (roadmap
    WS2.10), so a poison argument is the Call's own UB, not the body's. -/
theorem inlining_error_transfer
    (ctx : EvalContext) (fuel callDepth : Nat)
    (calleeId : FuncId) (callee : EvalFunction) (callArgs : List Value)
    (s : MachineState) (e : SemError)
    (hFn : ctx.functions calleeId = some callee)
    (hAbi : callee.body.abi = none)
    (hArity : callArgs.length = callee.body.paramTys.length)
    (hArgsClean : callArgs.any Value.isPoison = false)
    (hInline : Sem.run (stepNWithContext (ctx.forFunction callee) fuel callDepth
          callee.cfg callee.entryBlock callArgs)
        { s with locals := ValueMap.empty, nextValueId := 0 } = .error e) :
    Sem.run (runCallReq ctx fuel callDepth calleeId callArgs) s = .error e := by
  have hget : ∀ st : MachineState, Sem.run Sem.getState st = .ok (st, st) :=
    fun _ => rfl
  have hset : ∀ st st' : MachineState, Sem.run (Sem.setState st') st = .ok ((), st') :=
    fun _ _ => rfl
  unfold runCallReq
  simp only [hFn, hAbi, requireUntypedAbi_none, checkCallArity_ok callArgs callee.body.paramTys hArity,
    Sem.run_bind, Sem.run_pure, hget, hset, Except.bind,
    Sem.rejectPoisonValues_run_ok callArgs _ s hArgsClean, hInline]

/-- The converse of `inlining_error_transfer`: a failing Call (on poison-free
    arguments) either failed in the callee body with the same error, or the
    body returned with the wrong number of values or with a poison value
    (roadmap WS2.10), which the Call refuses. The Call adds no other
    outcome when the callee has no typed ABI descriptor. -/
theorem inlining_error_cases
    (ctx : EvalContext) (fuel callDepth : Nat)
    (calleeId : FuncId) (callee : EvalFunction) (callArgs : List Value)
    (s : MachineState) (e : SemError)
    (hFn : ctx.functions calleeId = some callee)
    (hAbi : callee.body.abi = none)
    (hArity : callArgs.length = callee.body.paramTys.length)
    (hArgsClean : callArgs.any Value.isPoison = false)
    (hCall : Sem.run (runCallReq ctx fuel callDepth calleeId callArgs) s = .error e) :
    Sem.run (stepNWithContext (ctx.forFunction callee) fuel callDepth callee.cfg callee.entryBlock callArgs)
        { s with locals := ValueMap.empty, nextValueId := 0 } = .error e ∨
    ∃ retVals sCalleeEnd,
      Sem.run (stepNWithContext (ctx.forFunction callee) fuel callDepth callee.cfg callee.entryBlock callArgs)
          { s with locals := ValueMap.empty, nextValueId := 0 } = .ok (retVals, sCalleeEnd) ∧
      (retVals.length ≠ callee.body.returnTys.length ∨
        retVals.any Value.isPoison = true) := by
  cases hIn : Sem.run (stepNWithContext (ctx.forFunction callee) fuel callDepth callee.cfg callee.entryBlock callArgs)
      { s with locals := ValueMap.empty, nextValueId := 0 } with
  | error e' =>
    left
    rw [inlining_error_transfer ctx fuel callDepth calleeId callee callArgs s e' hFn hAbi hArity
      hArgsClean hIn] at hCall
    exact congrArg Except.error (Except.error.inj hCall)
  | ok v =>
    right
    obtain ⟨retVals, sCalleeEnd⟩ := v
    refine ⟨retVals, sCalleeEnd, rfl, ?_⟩
    by_cases hRet : retVals.length = callee.body.returnTys.length
    · right
      cases hp : retVals.any Value.isPoison with
      | true => rfl
      | false =>
        rw [runCallReq_ok_of_inline ctx fuel callDepth calleeId callee callArgs s sCalleeEnd
          retVals hFn hAbi hArity hRet hArgsClean hp hIn] at hCall
        cases hCall
    · exact Or.inl hRet


/-- The `.ok`-only notion does not imply behaviour refinement. -/
theorem semantics_preserving_not_imp_refines :
    ¬ (∀ t, semantics_preserving t → behaviour_refines t) :=
  fun h => assertElim_not_refines (h assertElim assertElim_semantics_preserving)

/-- Nor does the weak `.ok`-only notion. -/
theorem semantics_preserving_weak_not_imp_refines :
    ¬ (∀ t, semantics_preserving_weak t → behaviour_refines t) :=
  fun h => panicToLoop_not_refines (h panicToLoop panicToLoop_semantics_preserving_weak)

-- -----------------------------------------------------------------
-- Review counter-models (WS8.15 adversarial review)
-- -----------------------------------------------------------------

/-- `loopCFG` never returns, from ANY entry block, arguments or state: a
    missing block and an arity mismatch are type errors, and block 0 with no
    arguments loops (`loopCFG_diverges`). -/
theorem loopCFG_never_returns (fuel : Nat) (pc : BlockId) (args : List Value)
    (s : MachineState) (r : List Value × MachineState) :
    Sem.run (stepN fuel loopCFG pc args) s ≠ .ok r := by
  cases args with
  | nil =>
    by_cases hpc : pc = ⟨0⟩
    · subst hpc
      rw [loopCFG_diverges fuel s]
      intro impossible; cases impossible
    · cases fuel with
      | zero => intro impossible; cases impossible
      | succ n =>
        have hNone : loopCFG pc = none := by simp [loopCFG, hpc]
        simp only [stepN, hNone]
        intro impossible; cases impossible
  | cons a as =>
    cases fuel with
    | zero => intro impossible; cases impossible
    | succ n =>
      by_cases hpc : pc = ⟨0⟩
      · subst hpc
        intro impossible; cases impossible
      · have hNone : loopCFG pc = none := by simp [loopCFG, hpc]
        simp only [stepN, hNone]
        intro impossible; cases impossible

open Classical in
/-- `divToRet`: a program that never returns, from any input, is replaced by
    `returnCFG`; every other program is kept. This is the counter-model of
    roadmap row `core-arch-0916-a/24`: turning a divergent source into a
    returning target. -/
noncomputable def divToRet (cfg : CFG) : CFG :=
  if ∀ fuel pc args s r, Sem.run (stepN fuel cfg pc args) s ≠ .ok r then returnCFG else cfg

/-- **Counter-model: the `.ok`-only notion accepts divergence-to-return.** It
    holds vacuously on every rewritten program, because such a program never
    returns. -/
theorem divToRet_semantics_preserving : semantics_preserving divToRet := by
  intro cfg pc args s fuel result hOk
  by_cases hc : ∀ fuel pc args s r, Sem.run (stepN fuel cfg pc args) s ≠ .ok r
  · exact absurd hOk (hc fuel pc args s result)
  · simp only [divToRet, if_neg hc]
    exact hOk

/-- **Counter-model: divergence-to-return is NOT a behaviour refinement.** The
    UB-free, diverging source `loopCFG` becomes `returnCFG`, which returns.
    This catches a definition that treats a diverging source as licensing
    every target behaviour (as if divergence were UB). -/
theorem divToRet_not_refines : ¬ behaviour_refines divToRet := by
  intro h
  have hRew : divToRet loopCFG = returnCFG := by
    simp only [divToRet]
    rw [if_pos (fun fuel pc args s r => loopCFG_never_returns fuel pc args s r)]
  have hNoUB : ¬ Behaves loopCFG ⟨0⟩ [] MachineState.empty .ub := by
    rw [not_behaves_ub_iff]
    intro fuel msg hRun
    rw [loopCFG_diverges fuel MachineState.empty] at hRun
    cases hRun
  obtain ⟨r, hr⟩ := returnCFG_returns 0 MachineState.empty
  have hSrc := h loopCFG ⟨0⟩ [] MachineState.empty hNoUB (.returns r)
    (Or.inl ⟨1, by rw [hRew, hr]; rfl⟩)
  rcases hSrc with ⟨fuel, hO⟩ | ⟨hEq, _⟩
  · rw [loopCFG_diverges fuel MachineState.empty] at hO
    cases hO
  · cases hEq

/-- **Counter-model: trap classes are distinguished.** Replacing a panicking
    source with the empty CFG (a type error: undefined block) is not a
    refinement. A definition that collapsed every trap into one class would
    accept it. -/
theorem trapClass_not_refines : ¬ behaviour_refines (fun _ _ => none) := by
  intro h
  have hPanic := fun n => failingAssertCFG_panics n MachineState.empty
  have hNoUB : ¬ Behaves failingAssertCFG ⟨0⟩ [.bool false] MachineState.empty .ub := by
    intro hB
    cases behaves_of_always_panics _ _ _ _ _ _ hPanic _ hB
  have hSrc := h failingAssertCFG ⟨0⟩ [.bool false] MachineState.empty hNoUB .typeError
    (Or.inl ⟨1, rfl⟩)
  cases behaves_of_always_panics _ _ _ _ _ _ hPanic _ hSrc

/-- Rewrite an `Unreachable` terminator into `Return []`. -/
def unreachableToReturnBlock (block : BasicBlock) : BasicBlock :=
  match block.terminator with
  | .Unreachable => { block with terminator := .Return [] }
  | _ => block

/-- `unreachableToReturn`: rewrite every `Unreachable` terminator into
    `Return []`. Reaching `Unreachable` is UB, so this exploits UB. -/
def unreachableToReturn (cfg : CFG) : CFG := fun bid => (cfg bid).map unreachableToReturnBlock

/-- A block's run under `unreachableToReturnBlock` either equals the source
    run, or the source reached `Unreachable` (`Stuck`) and the target returns
    `[]` from the same state. -/
theorem stepBlock_unreachableToReturn (block : BasicBlock) (args : List Value)
    (s : MachineState) :
    Sem.run (stepBlock (unreachableToReturnBlock block) args) s
        = Sem.run (stepBlock block args) s ∨
      ∃ s2, Sem.run (stepBlock block args) s = .ok (.Stuck, s2) ∧
        Sem.run (stepBlock (unreachableToReturnBlock block) args) s = .ok (.Ret [], s2) := by
  unfold unreachableToReturnBlock
  split
  · rename_i hT
    simp only [stepBlock]
    rw [sem_run_bind_eq, sem_run_bind_eq]
    cases hP : Sem.run (bindBlockParams block.params args) s with
    | error e => left; rfl
    | ok v =>
      obtain ⟨u, s1⟩ := v
      simp only
      rw [sem_run_bind_eq, sem_run_bind_eq]
      cases hB : Sem.run (forIn block.body PUnit.unit _) s1 with
      | error e => left; rfl
      | ok w =>
        obtain ⟨u2, s2⟩ := w
        right
        refine ⟨s2, ?_, ?_⟩
        · simp only [hT]
          rfl
        · rfl
  · left; rfl

/-- At a fuel where the source is not UB, the `unreachableToReturn` target
    runs exactly like the source: a UB-free run never reaches `Unreachable`. -/
private theorem stepN_unreachableToReturn_aux (fuel : Nat)
    (cfg : CFG) (pc : BlockId) (args : List Value) (s : MachineState)
    (hNoUB : ∀ msg, Sem.run (stepN fuel cfg pc args) s ≠ .error (.ub msg)) :
    Sem.run (stepN fuel (unreachableToReturn cfg) pc args) s
      = Sem.run (stepN fuel cfg pc args) s := by
  induction fuel generalizing pc args s with
  | zero => rfl
  | succ n ih =>
    simp only [stepN, unreachableToReturn] at hNoUB ⊢
    cases hCfg : cfg pc with
    | none => simp only [hCfg, Option.map]
    | some block =>
      simp only [hCfg, Option.map] at hNoUB ⊢
      rw [sem_run_bind_eq] at hNoUB ⊢
      rw [sem_run_bind_eq]
      rcases stepBlock_unreachableToReturn block args s with hEq | ⟨s2, hSrc, _⟩
      · rw [hEq]
        cases hSB : Sem.run (stepBlock block args) s with
        | error e => rfl
        | ok val =>
          obtain ⟨sr, s'⟩ := val
          rw [hSB] at hNoUB
          simp only at hNoUB ⊢
          cases sr with
          | Continue nextPc nextArgs => exact ih nextPc nextArgs s' hNoUB
          | _ => rfl
      · rw [hSrc] at hNoUB
        exact absurd rfl (hNoUB "reached unreachable")

/-- **Positive: UB is top.** Rewriting `Unreachable` into a return is a
    behaviour refinement: the rewrite changes only runs that are UB, and a UB
    source licenses every target behaviour. This is the ruling for the
    `core-arch-0916-b/46` "UB-to-return" shape: it is ADMITTED by design, while
    trap-to-return (`assertElim_not_refines`) and divergence-to-return
    (`divToRet_not_refines`) are refused. A definition that dropped the
    UB-freeness premise would refuse this legitimate transform. -/
theorem unreachableToReturn_refines : behaviour_refines unreachableToReturn := by
  intro cfg pc args s hNoUB o h
  have hNoUB' := (not_behaves_ub_iff cfg pc args s).mp hNoUB
  exact behaves_congr _ _ pc args s
    (fun fuel => stepN_unreachableToReturn_aux fuel cfg pc args s (hNoUB' fuel)) o h

/-- The rewrite is not vacuous: the UB source `unreachableCFG` becomes a
    returning program. -/
theorem unreachableToReturn_unreachableCFG_returns :
    ∃ r, Sem.run (stepN 1 (unreachableToReturn unreachableCFG) ⟨0⟩ [])
      MachineState.empty = .ok r := ⟨_, rfl⟩

-- =================================================================
-- Amendment P: the panic site (wire v54, SPEC_RATIFICATIONS §19.1)
-- =================================================================

/-- **Elision soundness.** A `true` check steps identically whatever its kind
    and site: the operands, the location and the entry are read only on
    failure, so a proof that the check passes licenses its removal whatever
    panic it would have been. -/
theorem assert_true_step_independent_of_kind_and_site (c : ValueId) (k k' : AssertKind)
    (site site' : Option PanicSite) (s : MachineState)
    (hc : s.lookupValue c = some (.bool true)) :
    Sem.run (stepInst (.Assert c k site)) s = Sem.run (stepInst (.Assert c k' site')) s := by
  simp only [stepInst, sem_run_bind_eq, lookupValue_run_some c s _ hc] <;> rfl

/-- **`AssertInvoke` is a sited `Assert` followed by `Br`** under stepping
    (the panic=abort projection): a passing check continues to its normal
    edge exactly as `Br normalDest normalArgs` does, a failing one is the
    sited panic, and the unwind edge is never taken. -/
theorem assertInvoke_is_sited_assert_then_br (c : ValueId) (k : AssertKind)
    (site : PanicSite) (nd : BlockId) (na : List ValueId) (ud : BlockId)
    (s : MachineState) :
    Sem.run (stepInst (.AssertInvoke c k site nd na ud)) s
      = Sem.run (stepInst (.Assert c k (some site)) >>= fun _ => stepInst (.Br nd na)) s := by
  rw [sem_run_bind_eq (stepInst (.Assert c k (some site)))]
  simp only [stepInst]
  rw [sem_run_bind_eq, sem_run_bind_eq]
  cases hL : Sem.run (Sem.lookupValue c) s with
  | error e => rfl
  | ok v =>
    obtain ⟨x, s1⟩ := v
    dsimp only
    rw [sem_run_bind_eq, sem_run_bind_eq]
    cases hR : Sem.run (Sem.rejectPartial x "Assert") s1 with
    | error e => rfl
    | ok w =>
      obtain ⟨u, s2⟩ := w
      dsimp only
      cases x with
      | bool b =>
        cases b with
        | true => rfl
        | false =>
          cases hF : Sem.run (semAssertFail k (some site) : Sem InstrResult) s2 with
          | ok r => exact absurd hF (semAssertFail_run_not_ok k (some site) s2 r)
          | error e => rfl
      | _ => rfl

/-- Retarget every sited `Assert`'s entry to `entry'`: a transform that keeps
    every check and its kind and changes only WHICH entry a failure calls. -/
def retargetSitesBlock (entry' : FuncId) (block : BasicBlock) : BasicBlock :=
  { block with body := block.body.map fun i => match i with
      | .Assert c k (some site) => .Assert c k (some { site with entry := entry' })
      | i => i }

/-- `siteRewrite`: retarget every panic site to function 1. -/
def siteRewrite (cfg : CFG) : CFG := fun bid => (cfg bid).map (retargetSitesBlock ⟨1⟩)

/-- Counter-model source for `siteRewrite`: block 0 asserts its `Bool`
    parameter with the site (entry 0, location global 0) and returns.
    Entered with `false`, it panics with that site. -/
def failingSitedAssertCFG : CFG := fun bid =>
  if bid = ⟨0⟩ then
    some { params := [(⟨0⟩, .Bool)],
           body := [.Assert ⟨0⟩ .Unspecified (some ⟨⟨0⟩, .global ⟨0⟩⟩)],
           terminator := .Return [] }
  else none

/-- The source panics at every positive fuel, naming entry 0. -/
theorem failingSitedAssertCFG_panics (n : Nat) (s : MachineState) :
    Sem.run (stepN (n + 1) failingSitedAssertCFG ⟨0⟩ [.bool false]) s
      = .error (.panic "assertion failed" (some ⟨⟨0⟩, .global ⟨0⟩ 0⟩)) := rfl

/-- The rewritten target panics at every positive fuel, naming entry 1. -/
theorem siteRewrite_failingSitedAssertCFG_panics (n : Nat) (s : MachineState) :
    Sem.run (stepN (n + 1) (siteRewrite failingSitedAssertCFG) ⟨0⟩ [.bool false]) s
      = .error (.panic "assertion failed" (some ⟨⟨1⟩, .global ⟨0⟩ 0⟩)) := rfl

/-- **Rewriting a failing assert's site is not a behaviour refinement.** The
    check, its kind and its message are unchanged; only the entry differs,
    and the panic outcome names it. -/
theorem siteRewrite_not_refines : ¬ behaviour_refines siteRewrite := by
  intro h
  have hPanic := fun n => failingSitedAssertCFG_panics n MachineState.empty
  have hNoUB : ¬ Behaves failingSitedAssertCFG ⟨0⟩ [.bool false] MachineState.empty .ub := by
    intro hB
    cases behaves_of_always_panics _ _ _ _ _ _ hPanic _ hB
  have hSrc := h failingSitedAssertCFG ⟨0⟩ [.bool false] MachineState.empty hNoUB
    (.panics "assertion failed" (some ⟨⟨1⟩, .global ⟨0⟩ 0⟩)) (Or.inl ⟨1, rfl⟩)
  have := behaves_of_always_panics _ _ _ _ _ _ hPanic _ hSrc
  simp at this

/-- The site-free projection of a run: the pre-amendment-P panic outcome,
    which carried no site. -/
def eraseSite : Except SemError (List Value × MachineState) →
    Except SemError (List Value × MachineState)
  | .error (.panic msg _) => .error (.panic msg none)
  | r => r

/-- **Mutation control: a site-free panic outcome cannot see the rewrite.**
    Erasing the site, the source and the rewritten target run identically, so
    `siteRewrite_not_refines` rests on the outcome naming the site. -/
theorem siteRewrite_invisible_without_sites (n : Nat) (s : MachineState) :
    eraseSite (Sem.run (stepN (n + 1) failingSitedAssertCFG ⟨0⟩ [.bool false]) s)
      = eraseSite (Sem.run (stepN (n + 1) (siteRewrite failingSitedAssertCFG) ⟨0⟩
          [.bool false]) s) := by
  rw [failingSitedAssertCFG_panics, siteRewrite_failingSitedAssertCFG_panics]
  rfl

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
   blocks so they execute in the caller's SSA id space. The caller's source
   type table must also be extended or rederived for those new declarations;
   installing the callee's table does not model a caller-CFG splice. That requires a
   value-id/block-id renaming function and a `stepInst`-equivariance lemma
   under renaming (per instruction), which the model does not yet have.  The
   renaming is dynamic as well as static: a callee frame starts with empty
   locals and `nextValueId := 0`, and `bindFresh` numbers results from that
   counter, so a spliced body would number them from the caller's counter.
   The behaviour-level statement the splice form must refine is
   `inlining_behaves_iff` (`TransformRefinementCtx.lean`).

5. **Function-table transforms:**
   `program_refines` (`TransformRefinementCtx.lean`) is stated for a context
   transform, but lifting a CFG transform over every function of the context
   is not proved. Constant lowering is now total and uses only the target
   model and definition tables; `constValueAtWithDefs_mapFunctionCFGs` and
   `stepInstWithContext_const_withFunctions` prove function-table independence
   for the complete constant result and instruction state transition. The
   contextual-instruction result is now extended to every instruction by
   `stepInstWithContext_mapFunctionCFGs`, including closure header checks.
   The remaining lift needs recursive callee-body and control-flow preservation;
   local instruction equality alone grants no whole-program refinement.
-/

end TrustIr
