-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Coroutine resume-dispatch theorems (WS2.25): the `stepInst`-sequence
-- equivalence behind `semCoroSuspend`, and the two-state generator
-- round trip over the real evaluator.

import TrustIr.Semantics.Eval
import TrustIr.Proofs.MemoryProps
import TrustIr.Proofs.MemorySafety
import TrustIr.Proofs.TargetStepProps
import TrustIr.Proofs.IntResidue
import TrustIr.Proofs.MetaTheorems
import TrustIr.Proofs.SSACharProps

namespace TrustIr

-- Canonical folds after contextual codecs reduce at the fixed I64 frame type.
-- These are function equalities, so they also rewrite under evaluator binds.
private theorem sr_legacy_load (ty : Ty) (ptr : ValueId) (strict : Bool)
    (align : Option Nat) (model : ByteModel) :
    semLoadUsing (fun mem bytes => decodeMemoryAt model mem ty bytes)
        ty ptr strict align model = semLoad ty ptr strict align model := rfl

private theorem sr_legacy_store (ty : Ty) (ptr value : ValueId) (strict : Bool)
    (align : Option Nat) (model : ByteModel) :
    semStoreUsing (encodeMemoryAt model ty) ty ptr value strict align model =
      semStore ty ptr value strict align model := rfl

/-- Fold the held-value selector's exact lookup/publication sequence back to
its original scalar action, under the actual continuation. -/
private theorem sr_held_load_bind {α : Type} (ty : Ty) (ptr : ValueId) (strict : Bool)
    (align : Option Nat) (model : ByteModel) (next : ValueId → Sem α) :
    (do
      let pointer ← Sem.lookupValue ptr
      let value ← semLoadValueUsing (fun memory bytes => decodeMemoryAt model memory ty bytes)
        ty pointer strict align model
      let id ← Sem.bindFresh value
      next id) = (semLoad ty ptr strict align model >>= next) := by
  simp only [semLoad, semLoadUsing, bind_assoc]

private theorem sr_held_store_bind {α : Type} (ty : Ty) (ptr value : ValueId) (strict : Bool)
    (align : Option Nat) (model : ByteModel) (next : Unit → Sem α) :
    (do
      let pointer ← Sem.lookupValue ptr
      let held ← Sem.lookupValue value
      let result ← semStoreValueUsing (scalarMemoryLayout model) (encodeMemoryAt model ty)
        ty pointer held strict align model
      next result) = (semStore ty ptr value strict align model >>= next) := by
  simp only [semStore, semStoreUsing, bind_assoc]

private theorem sr_encode_i64 (model : ByteModel) (order : FunctionAddressOrder) :
    encodeMemoryWithFunctions model order .I64 = encodeMemoryAt model .I64 := rfl

set_option smartUnfolding false

/-!
# Coroutine resume dispatch

The intrinsic uses held values and publishes no SSA temporaries. The old
raw-spine equality was false: a literal expansion changes locals/counters
and could even create a previously undefined yield operand. The exact
held-value composition below replaces those auxiliary contracts. The
source-aware graph replacement is in GenericCoroProps at the real call-frame
boundary, retaining every error and the complete caller world.

The finite generator uses actual result destination rows and independently
inferred source/target type tables. Its expansion names 1/2/3 are disjoint
from every original declaration, including the unvisited final block. The
intrinsic and expanded forms have distinct, explicit complete exit states;
both drive the same resume state machine and reject the miswired store.
-/

-- =================================================================
-- Monadic bookkeeping: read-only prefixes and fresh-result tails
-- =================================================================

/-- A computation that, whenever it succeeds, leaves the state untouched. -/
def Sem.ReadOnly {α : Type} (m : Sem α) : Prop :=
  ∀ s r s', StateT.run m s = .ok (r, s') → s' = s

/-- A `ValueId`-returning computation that, whenever it succeeds, is exactly
    one fresh bind on the input state: it returns `ValueId.mk s.nextValueId`
    and the state `s.bindValue v` for some value `v`. -/
def Sem.EndsFresh (m : Sem ValueId) : Prop :=
  ∀ s p s', StateT.run m s = .ok (p, s') → ∃ v, (p, s') = s.bindValue v

theorem Sem.ReadOnly.bind {α β : Type} {m : Sem α} {f : α → Sem β}
    (hm : m.ReadOnly) (hf : ∀ x, (f x).ReadOnly) : (m >>= f).ReadOnly := by
  intro s r s' h
  rw [sr_bind] at h
  cases hm' : StateT.run m s with
  | error e => rw [hm'] at h; cases h
  | ok p =>
    obtain ⟨x, s1⟩ := p
    rw [hm'] at h
    have h1 := hm s x s1 hm'
    have h2 := hf x s1 r s' h
    exact h2.trans h1

theorem Sem.ReadOnly.bindFresh {α : Type} {m : Sem α} {f : α → Sem ValueId}
    (hm : m.ReadOnly) (hf : ∀ x, (f x).EndsFresh) : (m >>= f).EndsFresh := by
  intro s p s' h
  rw [sr_bind] at h
  cases hm' : StateT.run m s with
  | error e => rw [hm'] at h; cases h
  | ok q =>
    obtain ⟨x, s1⟩ := q
    rw [hm'] at h
    have h1 := hm s x s1 hm'
    rw [h1] at h
    exact hf x s p s' h

theorem Sem.ReadOnly.pure {α : Type} (x : α) : (pure x : Sem α).ReadOnly := by
  intro s r s' h
  rw [sr_pure] at h
  cases h; rfl

theorem Sem.ReadOnly.throw {α : Type} (e : SemError) : (throw e : Sem α).ReadOnly := by
  intro s r s' h
  rw [sr_throw] at h
  cases h

theorem Sem.ReadOnly.throwUB {α : Type} (msg : String) :
    (Sem.throwUB msg : Sem α).ReadOnly := Sem.ReadOnly.throw _

theorem Sem.ReadOnly.throwTypeError {α : Type} (msg : String) :
    (Sem.throwTypeError msg : Sem α).ReadOnly := Sem.ReadOnly.throw _

theorem Sem.ReadOnly.lookupValue (id : ValueId) : (Sem.lookupValue id).ReadOnly := by
  intro s r s' h
  rw [sr_lookup] at h
  cases hl : s.lookupValue id with
  | none => rw [hl] at h; cases h
  | some v => rw [hl] at h; cases h; rfl

theorem Sem.EndsFresh.bindFresh (v : Value) : (Sem.bindFresh v).EndsFresh := by
  intro s p s' h
  rw [sr_bindFresh] at h
  exact ⟨v, (Except.ok.inj h).symm⟩

/-- A `for` loop over a list whose every body step is read-only is read-only. -/
theorem Sem.ReadOnly.forIn_list {α β : Type} (xs : List α) (acc : β)
    (body : α → β → Sem (ForInStep β)) (hBody : ∀ x a, (body x a).ReadOnly) :
    (forIn xs acc body : Sem β).ReadOnly := by
  induction xs generalizing acc with
  | nil =>
    simp only [List.forIn_nil, List.forIn_cons]
    exact Sem.ReadOnly.pure _
  | cons x xs ih =>
    simp only [List.forIn_nil, List.forIn_cons]
    exact Sem.ReadOnly.bind (hBody x acc) fun step => by
      cases step with
      | yield b => exact ih b
      | done b => exact Sem.ReadOnly.pure _

theorem Sem.ReadOnly.targetAddress (model : ByteModel) (op : String) (address : Nat) :
    (Sem.targetAddress model op address).ReadOnly := by
  cases model with
  | le64 => exact Sem.ReadOnly.pure _
  | le32 =>
    simp only [Sem.targetAddress]
    split
    · exact Sem.ReadOnly.pure _
    · exact Sem.ReadOnly.throwUB _

theorem Sem.ReadOnly.fromMemoryExcept {α : Type} (result : Except SemError α) :
    (Sem.fromMemoryExcept result).ReadOnly := by
  cases result with
  | ok value => exact Sem.ReadOnly.pure value
  | error error => exact Sem.ReadOnly.throw error

theorem Sem.ReadOnly.getState : Sem.getState.ReadOnly := by
  intro s r s' h
  rw [sr_get] at h
  exact (Prod.mk.inj (Except.ok.inj h)).2.symm

theorem Sem.ReadOnly.rejectPartial (value : Value) (op : String) :
    (Sem.rejectPartial value op).ReadOnly := by
  cases value <;> first | exact Sem.ReadOnly.pure _ | exact Sem.ReadOnly.throwUB _

theorem Sem.ReadOnly.throwBind {α β : Type} (error : SemError) (next : α → Sem β) :
    ((MonadExcept.throw error : Sem α) >>= next).ReadOnly := by
  intro s r s' h
  simp only [sr_bind, sr_throw, Except.bind] at h <;> cases h

theorem Sem.ReadOnly.gepAddress (base : Value) (delta : Nat) (model : ByteModel) :
    (semGEPAddress base delta model).ReadOnly := by
  unfold semGEPAddress
  refine Sem.ReadOnly.bind (Sem.ReadOnly.rejectPartial base _) ?_
  intro _
  cases base <;> first
    | exact Sem.ReadOnly.throwUB _
    | exact Sem.ReadOnly.throwTypeError _
    | skip
  rename_i address origin
  cases origin with
  | none =>
    refine Sem.ReadOnly.bind (Sem.ReadOnly.fromMemoryExcept _) ?_
    intro result
    split
    · exact Sem.ReadOnly.throwBind _ _
    · exact Sem.ReadOnly.bind (Sem.ReadOnly.pure _) fun _ => Sem.ReadOnly.pure _
  | some id =>
    refine Sem.ReadOnly.bind Sem.ReadOnly.getState ?_
    intro state
    cases state.memory.lookup id with
    | none => exact Sem.ReadOnly.throwBind _ _
    | some allocation =>
      simp only [pure_bind]
      split
      · exact Sem.ReadOnly.throwBind _ _
      · refine Sem.ReadOnly.bind (Sem.ReadOnly.fromMemoryExcept _) ?_
        intro _
        split
        · exact Sem.ReadOnly.throwBind _ _
        · exact Sem.ReadOnly.bind (Sem.ReadOnly.pure _) fun _ => Sem.ReadOnly.pure _

theorem Sem.ReadOnly.mapM_list {α β : Type} (items : List α) (f : α → Sem β)
    (h : ∀ item, (f item).ReadOnly) : (items.mapM f).ReadOnly := by
  have loop : ∀ acc, (List.mapM.loop f items acc).ReadOnly := by
    induction items with
    | nil => intro acc; exact Sem.ReadOnly.pure _
    | cons item items ih =>
      intro acc
      simp only [List.mapM.loop]
      exact Sem.ReadOnly.bind (h item) fun result => ih (result :: acc)
  exact loop []

theorem Sem.ReadOnly.gepValues {key : Type} (layoutOf : MemoryLayoutQuery)
    (reader : key → Value → Except SemError Int) (ty : Ty) (base : Value)
    (indices : List (key × Value)) (model : ByteModel) :
    (semGEPValuesUsing layoutOf reader ty base indices model).ReadOnly := by
  unfold semGEPValuesUsing
  exact Sem.ReadOnly.bind (Sem.ReadOnly.fromMemoryExcept _) fun delta =>
    Sem.ReadOnly.gepAddress base delta model

/-- A successful GEP publishes exactly one fresh pointer. Its held-value
    layout, integer, and address checks leave the complete state unchanged. -/
theorem semGEP_endsFresh (pointeeTy : Ty) (baseId : ValueId) (indexIds : List ValueId)
    (model : ByteModel := .le64) : (semGEP pointeeTy baseId indexIds model).EndsFresh := by
  unfold semGEP semGEPUsing
  refine Sem.ReadOnly.bindFresh (Sem.ReadOnly.lookupValue baseId) ?_
  intro base
  refine Sem.ReadOnly.bindFresh ?_ ?_
  · exact Sem.ReadOnly.mapM_list indexIds _ fun id =>
      Sem.ReadOnly.bind (Sem.ReadOnly.lookupValue id) fun value =>
        Sem.ReadOnly.pure (id, value)
  intro inputs
  exact Sem.ReadOnly.bindFresh (Sem.ReadOnly.gepValues _ _ _ _ _ _) fun value =>
    Sem.EndsFresh.bindFresh value

@[simp] theorem bitWidthFor_i64 (model : ByteModel) : Ty.I64.bitWidthFor model = some 64 := by
  cases model <;> trustIrReduce

@[simp] theorem bitWidthFor_i32 (model : ByteModel) : Ty.I32.bitWidthFor model = some 32 := by
  cases model <;> trustIrReduce

private theorem typedIntegerValue_i64_zero (model : ByteModel) :
    typedIntegerValue model .I64 (Value.intAt 64 0) = .ok 0 := by
  cases model <;> trustIrReduce

-- =================================================================
-- 1. The stepInst-sequence equivalence
-- =================================================================

/-- The literal macro-expansion of `CoroSuspend {frame, stateSlot, nextState,
    value}` as a `stepInst` sequence, with the operand ids of a REAL
    instruction stream: `n` is the fresh id the first `Const` receives, so
    the `GEP` reads `%n`, and the `Store` reads `%n+1` (the GEP result) and
    `%n+2` (the second `Const`). Exactly what inst.rs documents backends
    lower the terminator to. -/
def coroSuspendExpansion (frame : ValueId) (stateSlot : Nat) (nextState : Int)
    (value : ValueId) (n : Nat) (model : ByteModel := .le64) : Sem InstrResult := do
  let _ ← stepInst (.Const .I64 (.int stateSlot)) model
  let _ ← stepInst (.GEP .I64 frame [ValueId.mk n] false) model
  let _ ← stepInst (.Const .I64 (.int nextState)) model
  let _ ← stepInst (.Store .I64 (ValueId.mk (n + 1)) (ValueId.mk (n + 2)) false none) model
  stepInst (.Return [value]) model

/-- The expansion spine at fresh ids `n`, `n+1`, `n+2`, continued by an
    arbitrary terminator continuation `k` (the evaluator continues a
    terminator's `StepResult` with its own dispatch, not with
    `InstrResult.terminator`). This is the `simp`-normal form of the four
    `stepInst` steps of `coroSuspendExpansion` followed by `semReturn`. -/
def coroSuspendSpine {β : Type} (frame : ValueId) (stateSlot : Nat) (nextState : Int)
    (value : ValueId) (n : Nat) (k : StepResult → Sem β) (model : ByteModel := .le64) : Sem β := do
  let _ ← Sem.bindFresh (Value.intAt 64 stateSlot)
  let _ ← semGEP .I64 frame [ValueId.mk n] model
  let _ ← Sem.bindFresh (Value.intAt 64 nextState)
  semStore .I64 (ValueId.mk (n + 1)) (ValueId.mk (n + 2)) false none model
  let sr ← semReturn [value]
  k sr

/-- The intrinsic's actual held-value composition, including every error
    and complete post-state, is stable under every continuation. It does not
    assert equality with a stream that publishes private SSA temporaries. -/
theorem semCoroSuspend_bind_value_composition {β : Type} (frame : ValueId)
    (stateSlot : Nat) (nextState : Int) (value : ValueId) (k : StepResult → Sem β)
    (model : ByteModel := .le64) :
    (semCoroSuspend frame stateSlot nextState value model >>= k) = (do
      let frameValue ← Sem.lookupValue frame
      let slot ← semGEPValuesUsing (scalarMemoryLayout model)
        (fun (_ : Unit) v => typedIntegerValue model .I64 v)
        .I64 frameValue [((), Value.intAt 64 stateSlot)] model
      semStoreValueUsing (scalarMemoryLayout model) (encodeMemoryAt model .I64)
        .I64 slot (Value.intAt 64 nextState) false none model
      let result ← semReturn [value]
      k result) := by
  simp only [semCoroSuspend, bind_assoc]

/-- The spine only ever reaches its continuation with a `.Ret`: two
    continuations that agree on `.Ret` give the same program. -/
theorem coroSuspendSpine_congr {β : Type} (frame : ValueId) (stateSlot : Nat)
    (nextState : Int) (value : ValueId) (n : Nat) (k1 k2 : StepResult → Sem β)
    (h : ∀ vals, k1 (.Ret vals) = k2 (.Ret vals)) (model : ByteModel := .le64) :
    coroSuspendSpine frame stateSlot nextState value n k1 model
      = coroSuspendSpine frame stateSlot nextState value n k2 model := by
  simp only [coroSuspendSpine, semReturn, bind_assoc, pure_bind]
  refine congrArg _ (funext fun _ => ?_)
  refine congrArg _ (funext fun _ => ?_)
  refine congrArg _ (funext fun _ => ?_)
  refine congrArg _ (funext fun _ => ?_)
  exact congrArg _ (funext fun vals => h vals)

/-- Bare dispatch exposes the faithful intrinsic. Actual source-graph
    expansion correctness is proved at the caller frame boundary in
    GenericCoroProps; raw register maps are deliberately not equated. -/
theorem semCoroSuspend_step_value_composition (frame : ValueId) (stateSlot : Nat)
    (nextState : Int) (value : ValueId) (model : ByteModel := .le64) :
    stepInst (.CoroSuspend frame stateSlot nextState value) model =
      (semCoroSuspend frame stateSlot nextState value model >>= fun result =>
        pure (InstrResult.terminator result)) := rfl

/- The former bind/step private-spine equalities and the contextual expansion
   lift were false: expansion temporaries are observable in raw SSA maps and
   may synthesize an originally missing operand. Concrete counterexamples are
   retained below and GenericCoroProps supplies the source-aware replacement.
   No absent-table restriction or success-only replacement is used. -/

/-- A concrete all-state counterexample to the retired private-spine
    equality. Its first Const overwrites the frame's source id, whereas the
    faithful intrinsic reads the original null pointer and raises UB. -/
theorem coro_private_spine_counterexample :
    let state := { MachineState.empty with
      locals := ValueMap.empty.set ⟨0⟩ .nullPtr }
    Sem.run (stepInst (.CoroSuspend ⟨0⟩ 0 1 ⟨0⟩)) state =
      .error (.ub "GEP: null base pointer") ∧
    Sem.run (coroSuspendExpansion ⟨0⟩ 0 1 ⟨0⟩ 0) state =
      .error (.unsupported .ssaTypeTable "integer operand requires its original declaration") := by
  constructor <;> trustIrReduce

-- =================================================================
-- 2. The two-state generator round trip
-- =================================================================

/-!
## The two-state generator

The smallest coroutine with a real resume dispatch: a `resume` function
whose entry loads the state index out of the frame and switches on it,
one suspend state and one final state.

    bb0(%fp: ptr):                       ; resume entry
        %state = load i64 %fp            ; frame[0] is the state slot
        switch %state, default bb3 [0 → bb1, 1 → bb2]
    bb1:                                 ; state 0: yield 42, go to state 1
        %y = const i32 42
        coro_suspend frame=%fp slot=0 next=1 value=%y
    bb2:                                 ; state 1: return 7
        %f = const i32 7
        return %f
    bb3:                                 ; no such state
        unreachable

Each resume is a CALL of this function: the frame pointer is the entry
argument, the register file starts EMPTY (`locals := ValueMap.empty`,
`nextValueId := 0` — exactly what `stepNWithContext`'s call machinery sets
up for a callee), and the FRAME MEMORY persists between resumes. The
named result destinations (`bodyResultDests`) mirror Rust `InstrNode.results`.
-/

namespace CoroGen

/-- The entry parameter: the coroutine frame pointer. -/
def fp : ValueId := ⟨0⟩
/-- `%state`, the loaded state index. -/
def stateId : ValueId := ⟨10⟩
/-- `%y`, the suspended (yielded) value. -/
def yieldId : ValueId := ⟨11⟩
/-- `%f`, the final value. -/
def finalId : ValueId := ⟨12⟩

def bbEntry : BlockId := ⟨0⟩
def bbSuspend : BlockId := ⟨1⟩
def bbFinal : BlockId := ⟨2⟩
def bbTrap : BlockId := ⟨3⟩

/-- The value the first resume yields. -/
def yieldValue : Value := .int 32 42
/-- The value the second resume returns. -/
def finalValue : Value := .int 32 7

/-- The resume dispatch: `switch %state [0 → suspend, 1 → final]`. -/
def entryCases : List SwitchCase :=
  [{ value := .int 0, target := bbSuspend, args := [] },
   { value := .int 1, target := bbFinal, args := [] }]

def entryBlock : BasicBlock :=
  { params := [(fp, .Ptr)]
    body := [.Load .I64 fp false none]
    bodyResultDests := [[stateId]]
    terminator := .Switch stateId bbTrap [] entryCases false }

/-- The suspend state, parameterised by the NEXT state index it records
    (`1` for the generator; the mutation control passes `2`). -/
def suspendBlock (nextState : Int) : BasicBlock :=
  { params := []
    body := [.Const .I32 (.int 42)]
    bodyResultDests := [[yieldId]]
    terminator := .CoroSuspend fp 0 nextState yieldId }

def finalBlock : BasicBlock :=
  { params := []
    body := [.Const .I32 (.int 7)]
    bodyResultDests := [[finalId]]
    terminator := .Return [finalId] }

def trapBlock : BasicBlock :=
  { params := [], body := [], terminator := .Unreachable }

/-- Globally fresh source names for this graph: 1/2/3 are absent from
    the original declarations 0/10/11/12. Internal evaluator temporaries are
    a separate namespace and are accounted for in the complete exit state. -/
def expansionIndexId : ValueId := ⟨1⟩
def expansionPointerId : ValueId := ⟨2⟩
def expansionStateId : ValueId := ⟨3⟩

def suspendBlockExpanded (nextState : Int) (storeFrom : ValueId) : BasicBlock :=
  { params := []
    body := [.Const .I32 (.int 42), .Const .I64 (.int 0),
      .GEP .I64 fp [expansionIndexId] false,
      .Const .I64 (.int nextState), .Store .I64 expansionPointerId storeFrom false none]
    bodyResultDests := [[yieldId], [expansionIndexId], [expansionPointerId], [expansionStateId], []]
    terminator := .Return [yieldId] }

/-- The generator's CFG with an arbitrary block in the suspend-state slot
    (`bb1`). The entry dispatch, the final state and the trap are fixed;
    `cfg` instantiates `bb1` with the `CoroSuspend` terminator form, and the
    review controls instantiate it with the terminator's literal expansion
    and with a mis-wired expansion. -/
def cfgWith (susp : BasicBlock) : CFG := fun b =>
  match b.index with
  | 0 => some entryBlock
  | 1 => some susp
  | 2 => some finalBlock
  | 3 => some trapBlock
  | _ => none

/-- The generator's CFG. -/
def cfg (nextState : Int) : CFG := cfgWith (suspendBlock nextState)

/-- Two actual source graphs used by the illustrative generator model. -/
inductive Model where
  | intrinsic (nextState : Int)
  | expanded (nextState : Int) (storeFrom : ValueId)

def Model.suspend : Model → BasicBlock
  | .intrinsic nextState => suspendBlock nextState
  | .expanded nextState storeFrom => suspendBlockExpanded nextState storeFrom

def Model.cfg (model : Model) : CFG := cfgWith model.suspend

def Model.blocks (model : Model) : List BasicBlock :=
  [entryBlock, model.suspend, finalBlock, trapBlock]

def Model.localTypes (model : Model) : Option LocalTypeTable :=
  match inferLocalTypes (fun _ => none) (fun _ => none)
      (trustIrListBind model.blocks (fun block => block.params))
      (trustIrListBind model.blocks (fun block =>
        bodyInstsWithResultDests block.body block.bodyResultDests ++
          [(block.terminator, block.terminatorResultDests)])) with
  | .ok table => some table
  | .error _ => none

/-- Inference always succeeds for these actual finite source graphs; the
    failure branch never creates an unchecked manual-context fallback. -/
theorem Model.localTypes_present (model : Model) : model.localTypes.isSome = true := by
  cases model <;> trustIrReduce

def Model.function (model : Model) : EvalFunction :=
  { body := { paramTys := [.Ptr], returnTys := [.I32] }
    cfg := model.cfg, entryBlock := bbEntry, localTypes := model.localTypes }

def Model.context (model : Model) (ctx : EvalContext) : EvalContext :=
  ctx.forFunction model.function

/-- These concrete frame interfaces contain no nominal item lane; retain
    the operational validation and prove its exact success. -/
private theorem sr_items_nil (ctx : EvalContext) :
    checkFunctionItemValues ctx [] [] = .ok () := rfl

private theorem sr_items_ptr (ctx : EvalContext) (address : Addr) (allocation : AllocId) :
    checkFunctionItemValues ctx [.Ptr] [.ptr address (some allocation)] = .ok () := by trustIrReduce

private theorem sr_items_yield (ctx : EvalContext) :
    checkFunctionItemValues ctx [.I32] [yieldValue] = .ok () := by trustIrReduce

private theorem sr_items_final (ctx : EvalContext) :
    checkFunctionItemValues ctx [.I32] [finalValue] = .ok () := by trustIrReduce

private theorem sr_model_returnTypes (model : Model) (ctx : EvalContext) :
    (model.context ctx).functionReturnTypes = some [.I32] := rfl

private theorem sr_model_byteModel (model : Model) (ctx : EvalContext) :
    (model.context ctx).byteModel = ctx.byteModel := rfl

private theorem sr_model_functionOrder (model : Model) (ctx : EvalContext) :
    (model.context ctx).functionOrder = ctx.functionOrder := rfl

private theorem sr_model_gep (model : Model) (ctx : EvalContext)
    (reader : ValueId → Value → Except SemError Int) (base : ValueId) (indices : List ValueId) :
    semGEPUsing (model.context ctx).memoryLayout reader .I64 base indices ctx.byteModel =
      semGEPUsing (scalarMemoryLayout ctx.byteModel) reader .I64 base indices ctx.byteModel := by
  simpa only [sr_model_byteModel] using
    (EvalContext.semGEPUsing_canonical (model.context ctx) reader .I64 base indices rfl)


/-- Freshness is checked against the actual original graph's declarations,
    including the final block that is not visited on the suspend path. -/
theorem expansion_ids_absent_from_original (nextState : Int) :
    (Model.intrinsic nextState).localTypes.map (fun table =>
      [table expansionIndexId, table expansionPointerId, table expansionStateId]) =
      some [none, none, none] := rfl

theorem expanded_source_declarations (nextState : Int) (storeFrom : ValueId) :
    (Model.expanded nextState storeFrom).localTypes.map (fun table =>
      [table expansionIndexId, table expansionPointerId, table expansionStateId]) =
      some [some .I64, some .Ptr, some .I64] := rfl

theorem expanded_preserves_original_declarations (nextState : Int) (storeFrom : ValueId) :
    (Model.expanded nextState storeFrom).localTypes.map (fun table =>
      [table fp, table stateId, table yieldId, table finalId]) =
    (Model.intrinsic nextState).localTypes.map (fun table =>
      [table fp, table stateId, table yieldId, table finalId]) := rfl

private theorem sr_model_load (model : Model) (ctx : EvalContext) (result : ValueId) :
    (model.context ctx).bindInstructionResults (.Load .I64 fp false none)
        (.value (some result)) [stateId] =
      bindInstrResultDests (.value (some result)) [stateId] := by
  apply bindInstructionResults_single_nonChar _ _ _ _ .I64
  · cases model <;> trustIrReduce
  · intro h; cases h

private theorem sr_model_yield (model : Model) (ctx : EvalContext) (raw : Int) (result : ValueId) :
    (model.context ctx).bindInstructionResults (.Const .I32 (.int raw))
        (.value (some result)) [yieldId] =
      bindInstrResultDests (.value (some result)) [yieldId] := by
  apply bindInstructionResults_single_nonChar _ _ _ _ .I32
  · cases model <;> trustIrReduce
  · intro h; cases h

private theorem sr_model_final (model : Model) (ctx : EvalContext) (raw : Int) (result : ValueId) :
    (model.context ctx).bindInstructionResults (.Const .I32 (.int raw))
        (.value (some result)) [finalId] =
      bindInstrResultDests (.value (some result)) [finalId] := by
  apply bindInstructionResults_single_nonChar _ _ _ _ .I32
  · cases model <;> trustIrReduce
  · intro h; cases h

private theorem sr_model_index (ctx : EvalContext) (nextState raw : Int)
    (storeFrom result : ValueId) :
    ((Model.expanded nextState storeFrom).context ctx).bindInstructionResults
        (.Const .I64 (.int raw)) (.value (some result)) [expansionIndexId] =
      bindInstrResultDests (.value (some result)) [expansionIndexId] := by
  apply bindInstructionResults_single_nonChar _ _ _ _ .I64
  · trustIrReduce
  · intro h; cases h

private theorem sr_model_pointer (ctx : EvalContext) (nextState : Int)
    (storeFrom result : ValueId) :
    ((Model.expanded nextState storeFrom).context ctx).bindInstructionResults
        (.GEP .I64 fp [expansionIndexId] false) (.value (some result)) [expansionPointerId] =
      bindInstrResultDests (.value (some result)) [expansionPointerId] := by
  apply bindInstructionResults_single_nonChar _ _ _ _ .Ptr
  · trustIrReduce
  · intro h; cases h

private theorem sr_model_state (ctx : EvalContext) (nextState raw : Int)
    (storeFrom result : ValueId) :
    ((Model.expanded nextState storeFrom).context ctx).bindInstructionResults
        (.Const .I64 (.int raw)) (.value (some result)) [expansionStateId] =
      bindInstrResultDests (.value (some result)) [expansionStateId] := by
  apply bindInstructionResults_single_nonChar _ _ _ _ .I64
  · trustIrReduce
  · intro h; cases h

private theorem sr_model_store (ctx : EvalContext) (pointer value : ValueId) :
    ctx.bindInstructionResults (.Store .I64 pointer value false none) (.value none) [] =
      pure () := by
  cases h : ctx.localTypes <;>
    simp [EvalContext.bindInstructionResults, EvalContext.checkInstructionResults,
      EvalContext.instructionResultTypes, ssaInstructionResultTypes, localResultTypes,
      checkSSACharValues, Bind.bind, Pure.pure, Except.bind, Except.pure, h] <;> rfl

private theorem sr_checked_nil : bindBlockParamsChecked [] [] = bindBlockParams [] [] := rfl
private theorem sr_checked_ptr (id : ValueId) (value : Value) :
    bindBlockParamsChecked [(id, .Ptr)] [value] = bindBlockParams [(id, .Ptr)] [value] := rfl

/-- Resume the actual source graph with its own original declarations. All
    other context fields, resources and the complete world state are retained. -/
def resumeWith (ctx : EvalContext) (depth : Nat) (model : Model) (a : Addr) (fid : AllocId)
    (s : MachineState) : Except SemError (List Value × MachineState) :=
  Sem.run (stepNWithContext (model.context ctx) 2 depth model.cfg bbEntry [.ptr a (some fid)])
    { s with locals := ValueMap.empty, nextValueId := 0 }

def resume (ctx : EvalContext) (depth : Nat) (nextState : Int) (a : Addr) (fid : AllocId)
    (s : MachineState) : Except SemError (List Value × MachineState) :=
  resumeWith ctx depth (.intrinsic nextState) a fid s

end CoroGen

-- -----------------------------------------------------------------
-- Per-instruction run characterisations (the `sr_*` toolkit of
-- MemorySafety.lean, specialised to the shapes the generator executes)
-- -----------------------------------------------------------------

theorem sr_lookupValue_some (id : ValueId) (st : MachineState) (v : Value)
    (h : st.lookupValue id = some v) :
    StateT.run (Sem.lookupValue id) st = .ok (v, st) := by
  rw [sr_lookup, h]

@[simp] theorem byteSizeFor_i64 (model : ByteModel) : Ty.I64.byteSizeFor model = some 8 := by
  cases model <;> trustIrReduce

@[simp] theorem byteAlignFor_i64 (model : ByteModel) : Ty.I64.byteAlignFor model = some 8 := by
  cases model <;> trustIrReduce

@[simp] theorem fatPtrStoreValueValidFor_i64 (model : ByteModel) (value : Value) :
    fatPtrStoreValueValidFor model .I64 value = true := by
  cases model <;> trustIrReduce

@[simp] theorem encodeMemoryAt_i64_int (model : ByteModel) (width : Nat) (value : Int) :
    encodeMemoryAt model .I64 (.int width value) = encodeValueAt .I64 (.int width value) := by
  cases model <;> trustIrReduce

theorem decodeMemoryAt_i64_success (model : ByteModel) (mem : Memory) (bytes : List UInt8)
    (value : Value) (h : decodeValueAt mem .I64 bytes = .ok value) :
    decodeMemoryAt model mem .I64 bytes = .ok value := by
  cases model with
  | le64 => exact h
  | le32 =>
    by_cases hb : bytes.length == 8
    · simpa only [decodeMemoryAt, decodeTypedAtModel, decodeImageAtModel, decodeValueAt,
        decodeImageAt, Ty.isFloat, Bool.false_eq_true, ↓reduceIte, decodeValueAtModel,
        decodeValue, hb, Except.bind, pure, Except.pure] using h
    · simp only [decodeValueAt, decodeImageAt, Ty.isFloat, Bool.false_eq_true, ↓reduceIte,
        decodeValue, hb] at h <;> cases h


theorem accessAlign_ok_model (op : String) (ty : Ty) (align : Option Nat) (s : MachineState)
    (model : ByteModel) (h : isPow2 (align.getD ((ty.byteAlignFor model).getD 1)) = true) :
    StateT.run (Sem.accessAlign op ty align model) s =
      .ok (align.getD ((ty.byteAlignFor model).getD 1), s) := by
  unfold Sem.accessAlign Sem.declaredOrNaturalAlign
  simp only [h, if_true]
  rfl

/-- A successful typed load: the pointer is derived from a live allocation
    and passes the access check at `a`, whose `n` bytes read back as `bs`,
    which decodes (in the current memory) to `v`; the result is one fresh bind
    of `v`. -/
theorem sr_semLoad_ok (ty : Ty) (ptrId : ValueId) (st : MachineState) (a : Addr) (fid : AllocId)
    (bs : List UInt8) (n : Nat) (v : Value) (model : ByteModel := .le64)
    (hP : st.lookupValue ptrId = some (.ptr a (some fid)))
    (hBS : (ty.byteSizeFor model) = some n)
    (hAl : isPow2 ((none : Option Nat).getD ((ty.byteAlignFor model).getD 1)) = true)
    (hAcc : StateT.run (Sem.checkedAccess "Load" a fid n
      ((none : Option Nat).getD ((ty.byteAlignFor model).getD 1)) model) st = .ok (a, st))
    (hRead : st.memory.readBytes a n = some bs) (hDec : decodeMemoryAt model st.memory ty bs = .ok v) :
    StateT.run (semLoad ty ptrId false none model) st = .ok (st.bindValue v) := by
  unfold semLoad semLoadUsing semLoadValueUsing
  simp only [sr_bind, sr_lookup, hP, Except.bind, Sem.rejectPartial, expectPointer_ptr, hBS, sr_pure]
  rw [accessAlign_ok_model _ _ _ _ model hAl]
  simp only [Except.bind]
  rw [hAcc]
  simp only [Except.bind, sr_bind, sr_get, hRead, hDec, sr_bindFresh, sr_pure]

/-- The generator's frame pointer `a` is derived from (provenance `fid`) a
    live allocation that holds the eight-byte state slot at `a`, eight-byte
    aligned: the condition under which its `i64` `Load` and `Store` pass the
    access check (`Sem.accessAddr`). Writing bytes keeps it. -/
def FrameOk (mem : Memory) (a : Addr) (fid : AllocId) (model : ByteModel := .le64) : Prop :=
  ∃ alloc, mem.lookup fid = some alloc ∧ alloc.alive = true ∧ a % 8 = 0 ∧
    alloc.base ≤ a ∧ a - alloc.base + 8 ≤ alloc.size ∧ a - alloc.base ≤ word64Max ∧
    (model = .le32 → a + 8 ≤ ByteModel.le32.addressLimit)

/-- The exact legacy frame domain includes the provenance-relative u64
    offset check performed by the runtime GEP, without an absolute-address
    restriction on provenance pointers. -/
theorem FrameOk.legacy_iff (mem : Memory) (a : Addr) (fid : AllocId) :
    FrameOk mem a fid .le64 ↔ ∃ alloc,
      mem.lookup fid = some alloc ∧ alloc.alive = true ∧ a % 8 = 0 ∧
        alloc.base ≤ a ∧ a - alloc.base + 8 ≤ alloc.size ∧ a - alloc.base ≤ word64Max := by
  simp [FrameOk]

theorem FrameOk.addressBound {mem : Memory} {a : Addr} {fid : AllocId} {model : ByteModel}
    (h : FrameOk mem a fid model) (hm : model = .le32) : a < ByteModel.le32.addressLimit := by
  obtain ⟨_, _, _, _, _, _, _, hBound⟩ := h
  have hb := hBound hm
  exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 8)) hb

/-- A frame in the selected address space passes the unchanged provenance
    and allocation check as well as the target-range check. -/
theorem FrameOk.access {st : MachineState} {a : Addr} {fid : AllocId} {model : ByteModel}
    (h : FrameOk st.memory a fid model) (op : String) :
    StateT.run (Sem.checkedAccess op a fid 8
      ((none : Option Nat).getD ((Ty.I64.byteAlignFor model).getD 1)) model) st = .ok (a, st) := by
  have hAddress := h.addressBound
  obtain ⟨alloc, hl, hAlive, hAl, hBase, hEnd, _, hBound⟩ := h
  have hLegacy := checkedAccess_ok_of op 8 8 st a fid alloc hl hAlive (Or.inr hAl) hBase hEnd
  have hTarget : StateT.run (Sem.checkTargetRange model op a 8) st = .ok ((), st) := by
    cases model with
    | le64 => rfl
    | le32 => simp [Sem.checkTargetRange, hAddress rfl, hBound rfl, sr_pure, pure, Except.pure, StateT.pure, StateT.run]
  simp only [byteAlignFor_i64, Option.getD_some, Option.getD_none]
  rw [checkedAccess_model_factor]
  simp only [sr_bind, hTarget, Except.bind]
  exact hLegacy

/-- The fixed I64 frame store uses the held-value core. No temporary
    pointer or stored-value SSA binding is manufactured. -/
theorem sr_semStoreValue_i64_ok (st : MachineState) (a : Addr) (fid : AllocId)
    (value : Value) (enc : List UInt8) (model : ByteModel)
    (hFrame : FrameOk st.memory a fid model) (hNP : value.isPoison = false)
    (hEnc : encodeMemoryAt model .I64 value = .ok enc) (hLen : enc.length = 8) :
    StateT.run (semStoreValueUsing (scalarMemoryLayout model) (encodeMemoryAt model .I64)
      .I64 (.ptr a (some fid)) value false none model) st =
      .ok ((), {st with memory := st.memory.writeBytes a enc}) := by
  have layout : scalarMemoryLayout model .I64 = .ok ⟨8, 8⟩ := by cases model <;> trustIrReduce
  have alignment : checkedMemoryAlign "Store" 8 none = .ok 8 := rfl
  have access := hFrame.access "Store"
  simp only [byteAlignFor_i64, Option.getD_some, Option.getD_none] at access
  unfold semStoreValueUsing
  simp only [Sem.rejectPartial, pure_bind, layout, alignment, Sem.fromMemoryExcept,
    sr_bind, sr_pure, Except.bind, expectPointer_ptr]
  rw [access]
  simp only [Except.bind, sr_bind, sr_get, hNP, Bool.false_eq_true, ↓reduceIte,
    fatPtrStoreValueValidFor_i64, Bool.not_true, hEnc, hLen, bne_self_eq_false,
    sr_modify, sr_pure]

/-- A zero-offset GEP at the live frame preserves the held pointer and the
    complete state. Its immediate reader is the actual known I64 type. -/
theorem sr_semGEPValues_i64_zero {key : Type} (reader : key → Value → Except SemError Int)
    (identity : key) (st : MachineState) (a : Addr) (fid : AllocId) (model : ByteModel)
    (hFrame : FrameOk st.memory a fid model)
    (hInteger : reader identity (Value.intAt 64 0) = .ok 0) :
    StateT.run (semGEPValuesUsing (scalarMemoryLayout model) reader .I64
      (.ptr a (some fid)) [(identity, Value.intAt 64 0)] model) st =
      .ok (.ptr a (some fid), st) := by
  obtain ⟨allocation, hLookup, _, _, hBase, _, hWord, hTarget⟩ := hFrame
  have layout : scalarMemoryLayout model .I64 = .ok ⟨8, 8⟩ := by cases model <;> trustIrReduce
  have operand : checkedWord64Operand "GEP" false 0 = .ok 0 := rfl
  have multiply : checkedWord64Mul "GEP" 8 0 = .ok 0 := rfl
  have add : checkedWord64Add "GEP" 0 0 = .ok 0 := rfl
  have plan : gepOffsetUsing (scalarMemoryLayout model) reader .I64
      [(identity, Value.intAt 64 0)] = .ok 0 := by
    simp only [gepOffsetUsing, layout, hInteger, operand, multiply, add,
      List.forIn_nil, List.forIn_cons, Bind.bind, Pure.pure, Except.bind, Except.pure]
  simp only [semGEPValuesUsing, plan, Sem.fromMemoryExcept, pure_bind]
  unfold semGEPAddress
  simp only [Sem.rejectPartial, pure_bind, sr_bind, sr_get, Except.bind, hLookup,
    sr_pure, Nat.not_lt.mpr hBase, ↓reduceIte, Nat.add_zero]
  have hOffset : a - allocation.base ≤ word64Max := hWord
  simp only [checkedWord64Add, Nat.add_zero, hOffset, ↓reduceIte,
    Sem.fromMemoryExcept, sr_pure, Except.bind]
  cases model with
  | le64 => rfl
  | le32 =>
    have bound := hTarget rfl
    have address : a < ByteModel.le32.addressLimit :=
      Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 8)) bound
    simp only [address, Nat.not_le.mpr address, show decide False = false from rfl, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, sr_pure]

/-- Source-aware single-index GEP with a proved original declaration.
    The old context-free carrier-based helper is intentionally not reused. -/
theorem sr_semGEPUsing_i64_zero (reader : IntegerOperandReader) (base index : ValueId)
    (st : MachineState) (a : Addr) (fid : AllocId) (model : ByteModel)
    (hFrame : FrameOk st.memory a fid model)
    (hBase : st.lookupValue base = some (.ptr a (some fid)))
    (hIndex : st.lookupValue index = some (Value.intAt 64 0))
    (hInteger : reader index (Value.intAt 64 0) = .ok 0) :
    StateT.run (semGEPUsing (scalarMemoryLayout model) reader .I64 base [index] model) st =
      .ok (st.bindValue (.ptr a (some fid))) := by
  unfold semGEPUsing
  simp only [List.mapM, List.mapM.loop, sr_bind, sr_lookup, hBase, hIndex,
    sr_pure, Except.bind, List.reverse_cons, List.reverse_nil, List.nil_append]
  rw [sr_semGEPValues_i64_zero reader index st a fid model hFrame hInteger]
  rfl

theorem sr_semStore_i64_ok (pointer storedId : ValueId) (st : MachineState)
    (a : Addr) (fid : AllocId) (value : Value) (enc : List UInt8) (model : ByteModel)
    (hFrame : FrameOk st.memory a fid model)
    (hPointer : st.lookupValue pointer = some (.ptr a (some fid)))
    (hStored : st.lookupValue storedId = some value) (hNP : value.isPoison = false)
    (hEnc : encodeMemoryAt model .I64 value = .ok enc) (hLen : enc.length = 8) :
    StateT.run (semStore .I64 pointer storedId false none model) st =
      .ok ((), {st with memory := st.memory.writeBytes a enc}) := by
  unfold semStore semStoreUsing
  simp only [sr_bind, sr_lookup, hPointer, hStored, Except.bind]
  exact sr_semStoreValue_i64_ok st a fid value enc model hFrame hNP hEnc hLen

theorem sr_semReturn_one (id : ValueId) (st : MachineState) (v : Value)
    (h : st.lookupValue id = some v) :
    StateT.run (semReturn [id]) st = .ok (.Ret [v], st) := by
  simp only [semReturn, List.mapM, List.mapM.loop, sr_bind, sr_lookup, h, Except.bind, sr_pure,
    List.reverse_cons, List.reverse_nil, List.nil_append]

/-- A switch whose scrutinee the in-order scan matches to an argument-free
    case continues to that case's target. -/
theorem sr_semSwitch_case (id : ValueId) (d : BlockId) (cases : List SwitchCase)
    (st : MachineState) (k : Int) (c : Int) (t : BlockId)
    (h : st.lookupValue id = some (.int 64 k))
    (hDisp : matchSwitchCase (.int 64 k) cases
      = some { value := .int c, target := t, args := [] }) :
    StateT.run (semSwitch id d [] cases) st = .ok (.Continue t [], st) := by
  simp only [semSwitch, sr_bind, sr_lookup, h, Except.bind, Sem.rejectPartial, sr_pure, hDisp,
    Constant.hasSymbolAddr, Bool.false_eq_true, ↓reduceIte, List.mapM, List.mapM.loop,
    List.reverse_nil]

/-- A switch no case matches takes the (argument-free) default edge. -/
theorem sr_semSwitch_default (id : ValueId) (d : BlockId) (cases : List SwitchCase)
    (st : MachineState) (k : Int)
    (h : st.lookupValue id = some (.int 64 k))
    (hDisp : matchSwitchCase (.int 64 k) cases = none) :
    StateT.run (semSwitch id d [] cases) st = .ok (.Continue d [], st) := by
  simp only [semSwitch, sr_bind, sr_lookup, h, Except.bind, Sem.rejectPartial, sr_pure, hDisp,
    List.mapM, List.mapM.loop, List.reverse_nil]

theorem sr_bindBlockParams_one (p : ValueId) (ty : Ty) (v : Value) (st : MachineState) :
    StateT.run (bindBlockParams [(p, ty)] [v]) st
      = .ok ((), { st with
          locals := st.locals.set p v
          nextValueId := max st.nextValueId (p.index + 1) }) := rfl

theorem sr_bindBlockParams_nil (st : MachineState) :
    StateT.run (bindBlockParams [] []) st = .ok ((), st) := rfl

theorem sr_bindResultDests_one (d : ValueId) (v : Value) (st : MachineState) :
    StateT.run (bindResultDests [d] [v]) st
      = .ok ((), { st with
          locals := st.locals.set d v
          nextValueId := max st.nextValueId (d.index + 1) }) := rfl

-- -----------------------------------------------------------------
-- Block-level runs of the generator
-- -----------------------------------------------------------------

/-- Full publication state, including private-result retirement. -/
def publishedResultState (st : MachineState) (result dest : ValueId) (value : Value) : MachineState :=
  let published : MachineState :=
    { st with
      locals := st.locals.set dest value
      nextValueId := max st.nextValueId (dest.index + 1) }
  if result != dest then
    { published with locals := fun id => if id == result then none else published.locals id }
  else published

theorem sr_bindInstrResultDests_one (result dest : ValueId) (st : MachineState) (value : Value)
    (h : st.lookupValue result = some value) :
    StateT.run (bindInstrResultDests (.value (some result)) [dest]) st =
      .ok ((), publishedResultState st result dest value) := by
  simp only [bindInstrResultDests, sr_bind, sr_lookup, h, Except.bind,
    sr_bindResultDests_one]
  by_cases same : result != dest <;>
    simp only [publishedResultState, same, Bool.false_eq_true, ↓reduceIte, sr_bind, sr_get,
      sr_set, sr_pure, Except.bind]

namespace CoroGen

/-- Register file at the exit of the entry block (the state
    `stepNWithContext` hands to the dispatched successor): `%fp`, the load's
    result is published at `%state` and its private fresh id is retired;
    `nextValueId` has moved past `%state`. -/
def entryExit (s : MachineState) (a : Addr) (fid : AllocId) (k : Int) : MachineState :=
  publishedResultState
    {s with locals := (ValueMap.empty.set fp (.ptr a (some fid))).set ⟨1⟩ (.int 64 k)
            nextValueId := 2} ⟨1⟩ stateId (.int 64 k)

/-- The intrinsic publishes the declared yield only. Its held-value GEP
    and Store introduce no SSA results or counter increments. -/
def suspendExit (s : MachineState) (a : Addr) (fid : AllocId) (k _nextState : Int)
    (enc : List UInt8) : MachineState :=
  let yielded := publishedResultState ((entryExit s a fid k).bindValue yieldValue).2
    ⟨11⟩ yieldId yieldValue
  { yielded with memory := s.memory.writeBytes a enc }

/-- The final result is published to 12; its private fresh result 11 is
    retired. The caller-visible world is otherwise retained. -/
def finalExit (s : MachineState) (a : Addr) (fid : AllocId) (k : Int) : MachineState :=
  publishedResultState ((entryExit s a fid k).bindValue finalValue).2
    ⟨11⟩ finalId finalValue

set_option maxHeartbeats 3200000 in
/-- **Entry, case edge.** From a fresh register file over `s`, the entry
    block loads the state index `k` out of the frame at `a` and continues at
    the case target the in-order scan selects. -/
theorem entry_run_case (ctx : EvalContext) (fuel depth : Nat) (model : Model) (a : Addr) (fid : AllocId)
    (s : MachineState) (bs : List UInt8) (k c : Int) (target : BlockId)
    (hFrame : FrameOk s.memory a fid ctx.byteModel)
    (hRead : s.memory.readBytes a 8 = some bs)
    (hDec : decodeValueAt s.memory .I64 bs = .ok (.int 64 k))
    (hDisp : matchSwitchCase (.int 64 k) entryCases
      = some { value := .int c, target := target, args := [] }) :
    Sem.run (stepNWithContext (model.context ctx) (fuel + 1) depth model.cfg bbEntry [.ptr a (some fid)])
        { s with locals := ValueMap.empty, nextValueId := 0 }
      = Sem.run (stepNWithContext (model.context ctx) fuel depth model.cfg target [])
          (entryExit s a fid k) := by
  conv => lhs; unfold stepNWithContext
  simp only [sr_model_byteModel, sr_model_functionOrder, sr_model_returnTypes,
    sr_items_nil, sr_items_ptr, sr_items_yield, sr_items_final, Sem.fromMemoryExcept, EvalContext.resolveBlock, EvalContext.resolveDrop, List.map_nil, List.map_cons,
    Model.cfg, cfgWith, bbEntry, entryBlock, bodyInstsWithResultDests, sr_checked_nil, sr_checked_ptr, sr_model_load, sr_model_yield,
    sr_model_final, sr_model_index, sr_model_pointer, sr_model_state, sr_model_store, List.forIn_nil, List.forIn_cons, stepInstWithContext, sr_encode_i64, decodeMemoryWithFunctions,
    sr_model_gep, EvalContext.semGEPUsing_canonical, EvalContext.loadMemoryValueAligned,
    EvalContext.storeMemoryValueAligned, EvalContext.memoryRoute, EvalContext.originalClosureFor,
    EvalContext.memoryServiceFor, Ty.hasCanonicalMemoryLayout, if_true,
    sr_legacy_load, sr_legacy_store, sr_held_load_bind, sr_held_store_bind, stepTermWithContext, closureTermWithContext, stepInst, pure_bind, bind_assoc]
  simp only [Sem.run, sr_bind, Except.bind]
  rw [sr_bindBlockParams_one]
  dsimp only
  rw [sr_semLoad_ok (model := ctx.byteModel) (a := a) (fid := fid) (bs := bs) (n := 8) (v := .int 64 k)]
  · dsimp only [MachineState.bindValue]
    rw [sr_bindInstrResultDests_one (value := .int 64 k)]
    · dsimp only
      rw [sr_semSwitch_case (k := k) (c := c) (t := target)]
      · rfl
      · rfl
      · exact hDisp
    · rfl
  · rfl
  · exact byteSizeFor_i64 ctx.byteModel
  · simpa only [byteAlignFor_i64, Option.getD_none, Option.getD_some] using (show isPow2 8 = true from rfl)
  · apply FrameOk.access; exact hFrame
  · exact hRead
  · exact decodeMemoryAt_i64_success ctx.byteModel _ _ _ hDec

set_option maxHeartbeats 3200000 in
/-- **Entry, default edge.** A state index no case matches dispatches to the
    trap block. -/
theorem entry_run_default (ctx : EvalContext) (fuel depth : Nat) (model : Model) (a : Addr) (fid : AllocId)
    (s : MachineState) (bs : List UInt8) (k : Int)
    (hFrame : FrameOk s.memory a fid ctx.byteModel)
    (hRead : s.memory.readBytes a 8 = some bs)
    (hDec : decodeValueAt s.memory .I64 bs = .ok (.int 64 k))
    (hDisp : matchSwitchCase (.int 64 k) entryCases = none) :
    Sem.run (stepNWithContext (model.context ctx) (fuel + 1) depth model.cfg bbEntry [.ptr a (some fid)])
        { s with locals := ValueMap.empty, nextValueId := 0 }
      = Sem.run (stepNWithContext (model.context ctx) fuel depth model.cfg bbTrap [])
          (entryExit s a fid k) := by
  conv => lhs; unfold stepNWithContext
  simp only [sr_model_byteModel, sr_model_functionOrder, sr_model_returnTypes,
    sr_items_nil, sr_items_ptr, sr_items_yield, sr_items_final, Sem.fromMemoryExcept, EvalContext.resolveBlock, EvalContext.resolveDrop, List.map_nil, List.map_cons,
    Model.cfg, cfgWith, bbEntry, entryBlock, bodyInstsWithResultDests, sr_checked_nil, sr_checked_ptr, sr_model_load, sr_model_yield,
    sr_model_final, sr_model_index, sr_model_pointer, sr_model_state, sr_model_store, List.forIn_nil, List.forIn_cons, stepInstWithContext, sr_encode_i64, decodeMemoryWithFunctions,
    sr_model_gep, EvalContext.semGEPUsing_canonical, EvalContext.loadMemoryValueAligned,
    EvalContext.storeMemoryValueAligned, EvalContext.memoryRoute, EvalContext.originalClosureFor,
    EvalContext.memoryServiceFor, Ty.hasCanonicalMemoryLayout, if_true,
    sr_legacy_load, sr_legacy_store, sr_held_load_bind, sr_held_store_bind, stepTermWithContext, closureTermWithContext, stepInst, pure_bind, bind_assoc]
  simp only [Sem.run, sr_bind, Except.bind]
  rw [sr_bindBlockParams_one]
  dsimp only
  rw [sr_semLoad_ok (model := ctx.byteModel) (a := a) (fid := fid) (bs := bs) (n := 8) (v := .int 64 k)]
  · dsimp only [MachineState.bindValue]
    rw [sr_bindInstrResultDests_one (value := .int 64 k)]
    · dsimp only
      rw [sr_semSwitch_default (k := k)]
      · rfl
      · rfl
      · exact hDisp
    · rfl
  · rfl
  · exact byteSizeFor_i64 ctx.byteModel
  · simpa only [byteAlignFor_i64, Option.getD_none, Option.getD_some] using (show isPow2 8 = true from rfl)
  · apply FrameOk.access; exact hFrame
  · exact hRead
  · exact decodeMemoryAt_i64_success ctx.byteModel _ _ _ hDec

set_option maxHeartbeats 3200000 in
/-- **Suspend block.** Materialise `%y = 42`, record `nextState` in the
    frame's state slot, yield `[42]`. -/
theorem suspend_run (ctx : EvalContext) (fuel depth : Nat) (nextState : Int) (a : Addr) (fid : AllocId)
    (s : MachineState) (k : Int) (enc : List UInt8)
    (hFrame : FrameOk s.memory a fid ctx.byteModel)
    (hEnc : encodeValueAt .I64 (Value.intAt 64 nextState) = .ok enc) (hLen : enc.length = 8) :
    Sem.run (stepNWithContext ((Model.intrinsic nextState).context ctx) (fuel + 1) depth (Model.intrinsic nextState).cfg bbSuspend []) (entryExit s a fid k)
      = .ok ([yieldValue], suspendExit s a fid k nextState enc) := by
  unfold stepNWithContext
  simp only [sr_model_byteModel, sr_model_functionOrder, sr_model_returnTypes,
    sr_items_nil, sr_items_ptr, sr_items_yield, sr_items_final, Sem.fromMemoryExcept, EvalContext.resolveBlock, EvalContext.resolveDrop, List.map_nil, List.map_cons,
    Model.cfg, Model.suspend, cfgWith, bbSuspend, suspendBlock, bodyInstsWithResultDests, sr_checked_nil, sr_checked_ptr, sr_model_load, sr_model_yield,
    sr_model_final, sr_model_index, sr_model_pointer, sr_model_state, sr_model_store, List.forIn_nil, List.forIn_cons, stepInstWithContext, sr_encode_i64, decodeMemoryWithFunctions,
    sr_model_gep, EvalContext.semGEPUsing_canonical, EvalContext.loadMemoryValueAligned,
    EvalContext.storeMemoryValueAligned, EvalContext.memoryRoute, EvalContext.originalClosureFor,
    EvalContext.memoryServiceFor, Ty.hasCanonicalMemoryLayout, if_true,
    sr_legacy_load, sr_legacy_store, sr_held_load_bind, sr_held_store_bind, stepTermWithContext, closureTermWithContext, stepInst, pure_bind, bind_assoc,
    semCoroSuspend, Constant.hasSymbolAddr, constValueAtChecked_i64, constValueAtChecked_i32, constPointerFormsSupported, Ty.isInteger,
    constValueAt, constWidthAmbiguous, constHasInexactFloat,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bitWidthFor_i64, bitWidthFor_i32]
  simp only [Sem.run, sr_bind, Except.bind]
  rw [sr_bindBlockParams_nil]
  dsimp only
  rw [sr_bindFresh]
  dsimp only [MachineState.bindValue]
  rw [sr_bindInstrResultDests_one (value := yieldValue)]
  · dsimp only
    rw [sr_lookupValue_some (v := .ptr a (some fid))]
    · dsimp only
      simp only [Int.ofNat_zero]
      rw [sr_semGEPValues_i64_zero (key := Unit)
        (reader := fun (_ : Unit) value => typedIntegerValue ctx.byteModel .I64 value)
        (identity := ()) (a := a) (fid := fid) (model := ctx.byteModel)]
      · dsimp only
        rw [sr_semStoreValue_i64_ok (a := a) (fid := fid) (enc := enc) (model := ctx.byteModel)]
        · dsimp only
          rw [sr_semReturn_one (v := yieldValue)]
          · trustIrReduce
          · rfl
        · exact hFrame
        · trustIrReduce
        · simpa only [Value.intAt, encodeMemoryAt_i64_int] using hEnc
        · exact hLen
      · exact hFrame
      · exact typedIntegerValue_i64_zero ctx.byteModel
    · rfl
  · rfl

set_option maxHeartbeats 3200000 in
/-- **Final block.** Materialise `%f = 7` and return `[7]`. -/
theorem final_run (ctx : EvalContext) (fuel depth : Nat) (model : Model) (a : Addr) (fid : AllocId)
    (s : MachineState) (k : Int) :
    Sem.run (stepNWithContext (model.context ctx) (fuel + 1) depth model.cfg bbFinal []) (entryExit s a fid k)
      = .ok ([finalValue], finalExit s a fid k) := by
  unfold stepNWithContext
  simp only [sr_model_byteModel, sr_model_functionOrder, sr_model_returnTypes,
    sr_items_nil, sr_items_ptr, sr_items_yield, sr_items_final, Sem.fromMemoryExcept, EvalContext.resolveBlock, EvalContext.resolveDrop, List.map_nil, List.map_cons,
    Model.cfg, cfgWith, bbFinal, finalBlock, bodyInstsWithResultDests, sr_checked_nil, sr_checked_ptr, sr_model_load, sr_model_yield,
    sr_model_final, sr_model_index, sr_model_pointer, sr_model_state, sr_model_store, List.forIn_nil, List.forIn_cons, stepInstWithContext, sr_encode_i64, decodeMemoryWithFunctions,
    sr_model_gep, EvalContext.semGEPUsing_canonical, EvalContext.loadMemoryValueAligned,
    EvalContext.storeMemoryValueAligned, EvalContext.memoryRoute, EvalContext.originalClosureFor,
    EvalContext.memoryServiceFor, Ty.hasCanonicalMemoryLayout, if_true,
    sr_legacy_load, sr_legacy_store, sr_held_load_bind, sr_held_store_bind, stepTermWithContext, closureTermWithContext, stepInst, pure_bind, bind_assoc,
    Constant.hasSymbolAddr, constValueAtChecked_i64, constValueAtChecked_i32, constPointerFormsSupported, constValueAt, Ty.isInteger,
    constWidthAmbiguous, constHasInexactFloat,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bitWidthFor_i64, bitWidthFor_i32]
  simp only [Sem.run, sr_bind, Except.bind]
  rw [sr_bindBlockParams_nil]
  dsimp only
  rw [sr_bindFresh]
  dsimp only [MachineState.bindValue]
  rw [sr_bindInstrResultDests_one (value := .int 32 7)]
  · dsimp only
    rw [sr_semReturn_one (v := finalValue)]
    · trustIrReduce
    · rfl
  · rfl

set_option maxHeartbeats 3200000 in
/-- **Trap block.** `unreachable` is undefined behaviour. -/
theorem trap_run (ctx : EvalContext) (fuel depth : Nat) (model : Model) (st : MachineState) :
    Sem.run (stepNWithContext (model.context ctx) (fuel + 1) depth model.cfg bbTrap []) st
      = .error (.ub "reached unreachable") := by
  unfold stepNWithContext
  simp only [sr_model_byteModel, sr_model_functionOrder, sr_model_returnTypes,
    sr_items_nil, sr_items_ptr, sr_items_yield, sr_items_final, Sem.fromMemoryExcept, EvalContext.resolveBlock, EvalContext.resolveDrop, List.map_nil, List.map_cons,
    Model.cfg, cfgWith, bbTrap, trapBlock, bodyInstsWithResultDests, sr_checked_nil, sr_checked_ptr, sr_model_load, sr_model_yield,
    sr_model_final, sr_model_index, sr_model_pointer, sr_model_state, sr_model_store, List.forIn_nil, List.forIn_cons, stepTermWithContext, closureTermWithContext, stepInst, pure_bind, bind_assoc]
  simp only [Sem.run, sr_bind, Except.bind]
  rw [sr_bindBlockParams_nil]
  rfl

end CoroGen

-- -----------------------------------------------------------------
-- The round trip, and its mutation control
-- -----------------------------------------------------------------

namespace CoroGen

/-- The little-endian `i64` image of state index 1 (what the generator's
    suspend records). -/
def stateOneBytes : List UInt8 := [1, 0, 0, 0, 0, 0, 0, 0]

/-- The `i64` image of state index 2 (what the MUTANT suspend records). -/
def stateTwoBytes : List UInt8 := [2, 0, 0, 0, 0, 0, 0, 0]

theorem beq_zero_eq_false_of_ne {a : Addr} (h : a ≠ 0) : (a == 0) = false := by
  cases a with
  | zero => exact (h rfl).elim
  | succ a => rfl

#trustIrAxiomsExact beq_zero_eq_false_of_ne == []

/-- **The two-state generator round trip** (B3 depth ledger "Coroutine
    resume dispatch"). For EVERY machine state `s0` whose frame at `a` is a
    live, in-bounds `i64` cell holding state index 0, resuming the generator
    yields `42` and leaves the frame recording state 1 (the exit state is
    stated exactly: `suspendExit`), and resuming it AGAIN — fresh registers,
    the same frame memory — returns `7`. The `Load` + `Switch` dispatch
    composed with `CoroSuspend`'s store therefore forms the intended state
    machine over the real evaluator `stepNWithContext`. -/
theorem coro_two_state_roundtrip (ctx : EvalContext) (depth : Nat) (a : Addr) (fid : AllocId)
    (s0 : MachineState) (hFrame : FrameOk s0.memory a fid ctx.byteModel)
    (hZero : s0.memory.readBytes a 8 = some (List.replicate 8 0)) :
    resume ctx depth 1 a fid s0 = .ok ([yieldValue], suspendExit s0 a fid 0 1 stateOneBytes) ∧
    resume ctx depth 1 a fid (suspendExit s0 a fid 0 1 stateOneBytes)
      = .ok ([finalValue], finalExit (suspendExit s0 a fid 0 1 stateOneBytes) a fid 1) := by
  have hFrame' : FrameOk (s0.memory.writeBytes a stateOneBytes) a fid ctx.byteModel := hFrame
  have hRead1 : (s0.memory.writeBytes a stateOneBytes).readBytes a 8 = some stateOneBytes :=
    writeBytes_readBytes_general s0.memory a stateOneBytes
  constructor
  · -- First resume: state 0 → suspend block → yield 42, record state 1.
    have h1 := entry_run_case ctx 1 depth (.intrinsic 1) a fid s0 (List.replicate 8 0) 0 0 bbSuspend
      hFrame hZero rfl rfl
    have h2 := suspend_run ctx 0 depth 1 a fid s0 0 stateOneBytes hFrame rfl rfl
    simp only [Nat.zero_add] at h2
    unfold resume resumeWith
    rw [show (2 : Nat) = 1 + 1 from rfl, h1, h2]
  · -- Second resume: state 1 → final block → return 7.
    have h1 := entry_run_case ctx 1 depth (.intrinsic 1) a fid (suspendExit s0 a fid 0 1 stateOneBytes)
      stateOneBytes 1 1 bbFinal hFrame' hRead1 rfl rfl
    have h2 := final_run ctx 0 depth (.intrinsic 1) a fid (suspendExit s0 a fid 0 1 stateOneBytes) 1
    simp only [Nat.zero_add] at h2
    unfold resume resumeWith
    rw [show (2 : Nat) = 1 + 1 from rfl, h1, h2]

/-- **Mutation control.** A suspend that records `next + 1` (state 2
    instead of 1) still yields `42` on the first resume — the yield is not
    what the round trip checks — but the SECOND resume lands on the
    default edge and traps (`unreachable` is UB). The round trip is
    therefore sensitive to exactly the store the theorem is about. -/
theorem coro_two_state_mutant_traps (ctx : EvalContext) (depth : Nat) (a : Addr) (fid : AllocId)
    (s0 : MachineState) (hFrame : FrameOk s0.memory a fid ctx.byteModel)
    (hZero : s0.memory.readBytes a 8 = some (List.replicate 8 0)) :
    resume ctx depth 2 a fid s0 = .ok ([yieldValue], suspendExit s0 a fid 0 2 stateTwoBytes) ∧
    resume ctx depth 2 a fid (suspendExit s0 a fid 0 2 stateTwoBytes)
      = .error (.ub "reached unreachable") := by
  have hFrame' : FrameOk (s0.memory.writeBytes a stateTwoBytes) a fid ctx.byteModel := hFrame
  have hRead2 : (s0.memory.writeBytes a stateTwoBytes).readBytes a 8 = some stateTwoBytes :=
    writeBytes_readBytes_general s0.memory a stateTwoBytes
  constructor
  · have h1 := entry_run_case ctx 1 depth (.intrinsic 2) a fid s0 (List.replicate 8 0) 0 0 bbSuspend
      hFrame hZero rfl rfl
    have h2 := suspend_run ctx 0 depth 2 a fid s0 0 stateTwoBytes hFrame rfl rfl
    simp only [Nat.zero_add] at h2
    unfold resume resumeWith
    rw [show (2 : Nat) = 1 + 1 from rfl, h1, h2]
  · have h1 := entry_run_default ctx 1 depth (.intrinsic 2) a fid (suspendExit s0 a fid 0 2 stateTwoBytes)
      stateTwoBytes 2 hFrame' hRead2 rfl rfl
    have h2 := trap_run ctx 0 depth (.intrinsic 2) (entryExit (suspendExit s0 a fid 0 2 stateTwoBytes) a fid 2)
    simp only [Nat.zero_add] at h2
    unfold resume resumeWith
    rw [show (2 : Nat) = 1 + 1 from rfl, h1, h2]

/-- The mutant's round trip is REFUTED, not merely unproved: no final state
    makes its second resume return the final value. -/
theorem coro_two_state_roundtrip_mutant_refuted (ctx : EvalContext) (depth : Nat) (a : Addr) (fid : AllocId)
    (s0 : MachineState) (hFrame : FrameOk s0.memory a fid ctx.byteModel)
    (hZero : s0.memory.readBytes a 8 = some (List.replicate 8 0)) :
    ¬ ∃ s2, resume ctx depth 2 a fid (suspendExit s0 a fid 0 2 stateTwoBytes)
      = .ok ([finalValue], s2) := by
  intro ⟨s2, h⟩
  rw [(coro_two_state_mutant_traps ctx depth a fid s0 hFrame hZero).2] at h
  cases h

end CoroGen

-- =================================================================
-- Review controls (WS2.25 adversarial review)
-- =================================================================

/-!
## Review controls

Three ways the round trip could have been an artefact, each refuted:

* **A silent mutant.** The `next + 1` mutant above TRAPS, so a round trip
  that only demanded "the second resume succeeds" would already refute it.
  The `next - 1` mutant (the suspend records state 0 again — the generator
  that never leaves its first state) SUCCEEDS on the second resume and
  re-yields `42`; `coro_two_state_mutant_loops_refuted` shows the round trip
  refutes it on the returned VALUE.
* **The initial-state hypothesis is load-bearing.** From a frame that
  already records state 1, the first resume returns `7` and never yields
  (`coro_two_state_from_state_one_never_yields`): the round trip is a
  statement about a frame that starts at state 0, not about the CFG alone.
* **The expansion is the same state machine, with its own source state.**
  The correct store reads source id 3; the mutation reads the slot immediate
  from source id 1. Each graph has actual destination rows and its own inferred
  declarations. Their complete intrinsic/expanded exit states differ, while
  both resumptions preserve the frame state machine. GenericCoroProps proves
  the actual source-aware expansion relation at the caller frame boundary.
-/

namespace CoroGen

/-- The `i64` image of state index 0: what the `next - 1` mutant and the
    mis-wired expansion record. -/
def stateZeroBytes : List UInt8 := List.replicate 8 0

theorem yieldValue_ne_finalValue : yieldValue ≠ finalValue := by
  intro h
  injection h with _ h
  exact absurd h (by decide)

/-- **Silent mutation control.** A suspend that records `next - 1` (state 0
    again) still yields `42`, and its SECOND resume succeeds and yields `42`
    again — the generator never reaches its final state. -/
theorem coro_two_state_mutant_loops (ctx : EvalContext) (depth : Nat) (a : Addr) (fid : AllocId)
    (s0 : MachineState) (hFrame : FrameOk s0.memory a fid ctx.byteModel)
    (hZero : s0.memory.readBytes a 8 = some (List.replicate 8 0)) :
    resume ctx depth 0 a fid s0 = .ok ([yieldValue], suspendExit s0 a fid 0 0 stateZeroBytes) ∧
    resume ctx depth 0 a fid (suspendExit s0 a fid 0 0 stateZeroBytes)
      = .ok ([yieldValue],
          suspendExit (suspendExit s0 a fid 0 0 stateZeroBytes) a fid 0 0 stateZeroBytes) := by
  have hFrame' : FrameOk (s0.memory.writeBytes a stateZeroBytes) a fid ctx.byteModel := hFrame
  have hRead0 : (s0.memory.writeBytes a stateZeroBytes).readBytes a 8 = some stateZeroBytes :=
    writeBytes_readBytes_general s0.memory a stateZeroBytes
  constructor
  · have h1 := entry_run_case ctx 1 depth (.intrinsic 0) a fid s0 (List.replicate 8 0) 0 0 bbSuspend
      hFrame hZero rfl rfl
    have h2 := suspend_run ctx 0 depth 0 a fid s0 0 stateZeroBytes hFrame rfl rfl
    simp only [Nat.zero_add] at h2
    unfold resume resumeWith
    rw [show (2 : Nat) = 1 + 1 from rfl, h1, h2]
  · have h1 := entry_run_case ctx 1 depth (.intrinsic 0) a fid (suspendExit s0 a fid 0 0 stateZeroBytes)
      stateZeroBytes 0 0 bbSuspend hFrame' hRead0 rfl rfl
    have h2 := suspend_run ctx 0 depth 0 a fid (suspendExit s0 a fid 0 0 stateZeroBytes) 0 stateZeroBytes
      hFrame' rfl rfl
    simp only [Nat.zero_add] at h2
    unfold resume resumeWith
    rw [show (2 : Nat) = 1 + 1 from rfl, h1, h2]

/-- The looping mutant's round trip is refuted on the returned VALUE: its
    second resume succeeds, but with `42`, never `7`. -/
theorem coro_two_state_mutant_loops_refuted (ctx : EvalContext) (depth : Nat) (a : Addr) (fid : AllocId)
    (s0 : MachineState) (hFrame : FrameOk s0.memory a fid ctx.byteModel)
    (hZero : s0.memory.readBytes a 8 = some (List.replicate 8 0)) :
    ¬ ∃ s2, resume ctx depth 0 a fid (suspendExit s0 a fid 0 0 stateZeroBytes)
      = .ok ([finalValue], s2) := by
  intro ⟨s2, h⟩
  rw [(coro_two_state_mutant_loops ctx depth a fid s0 hFrame hZero).2] at h
  exact yieldValue_ne_finalValue (List.cons.inj (Prod.mk.inj (Except.ok.inj h)).1).1

/-- **The initial-state hypothesis is load-bearing.** From a frame that
    already records state 1, the FIRST resume returns `7`. -/
theorem coro_two_state_from_state_one_returns (ctx : EvalContext) (depth : Nat) (a : Addr) (fid : AllocId)
    (s0 : MachineState) (hFrame : FrameOk s0.memory a fid ctx.byteModel)
    (hOne : s0.memory.readBytes a 8 = some stateOneBytes) :
    resume ctx depth 1 a fid s0 = .ok ([finalValue], finalExit s0 a fid 1) := by
  have h1 := entry_run_case ctx 1 depth (.intrinsic 1) a fid s0 stateOneBytes 1 1 bbFinal
    hFrame hOne rfl rfl
  have h2 := final_run ctx 0 depth (.intrinsic 1) a fid s0 1
  simp only [Nat.zero_add] at h2
  unfold resume resumeWith
  rw [show (2 : Nat) = 1 + 1 from rfl, h1, h2]

/-- From state 1 the generator never yields: the round trip's `hZero` is not
    decorative. -/
theorem coro_two_state_from_state_one_never_yields (ctx : EvalContext) (depth : Nat)
    (a : Addr) (fid : AllocId) (s0 : MachineState) (hFrame : FrameOk s0.memory a fid ctx.byteModel)
    (hOne : s0.memory.readBytes a 8 = some stateOneBytes) :
    ¬ ∃ s1, resume ctx depth 1 a fid s0 = .ok ([yieldValue], s1) := by
  intro ⟨s1, h⟩
  rw [coro_two_state_from_state_one_returns ctx depth a fid s0 hFrame hOne] at h
  exact yieldValue_ne_finalValue (List.cons.inj (Prod.mk.inj (Except.ok.inj h)).1).1.symm

/-- Actual source destinations remain; private results 12/13/14 are
    retired on publication to the globally fresh source ids 1/2/3. -/
def expandedStoreRegs (s : MachineState) (a : Addr) (fid : AllocId) (k nextState : Int) : ValueMap :=
  let yielded := publishedResultState ((entryExit s a fid k).bindValue yieldValue).2
    ⟨11⟩ yieldId yieldValue
  let indexed := publishedResultState (yielded.bindValue (Value.intAt 64 0)).2
    ⟨12⟩ expansionIndexId (Value.intAt 64 0)
  let pointed := publishedResultState (indexed.bindValue (.ptr a (some fid))).2
    ⟨13⟩ expansionPointerId (.ptr a (some fid))
  (publishedResultState (pointed.bindValue (Value.intAt 64 nextState)).2
    ⟨14⟩ expansionStateId (Value.intAt 64 nextState)).locals

/-- The source-aware expanded graph has its own complete post-state. It is
    not falsely identified with the intrinsic's private temporary register file. -/
def expandedSuspendExit (s : MachineState) (a : Addr) (fid : AllocId) (k nextState : Int)
    (enc : List UInt8) : MachineState :=
  { s with locals := expandedStoreRegs s a fid k nextState
           nextValueId := 15
           memory := s.memory.writeBytes a enc }

set_option maxHeartbeats 3200000 in
/-- **Expanded suspend block, either wiring.** The block runs to the exit
    state `suspendExit s a fid k nextState enc` where `enc` is the byte image of
    whatever `storeFrom` holds: `nextState` for source id 3, the slot immediate
    `0` for source id 1. Stated once for both wirings via `stored`, the value the
    store operand denotes. -/
theorem suspend_run_expanded (ctx : EvalContext) (fuel depth : Nat) (nextState : Int)
    (storeFrom : ValueId) (stored : Int) (a : Addr) (fid : AllocId) (s : MachineState) (k : Int)
    (enc : List UInt8)
    (hFrame : FrameOk s.memory a fid ctx.byteModel)
    (hFrom : (expandedStoreRegs s a fid k nextState).get storeFrom = some (.int 64 stored))
    (hEnc : encodeValueAt .I64 (.int 64 stored) = .ok enc) (hLen : enc.length = 8) :
    Sem.run (stepNWithContext ((Model.expanded nextState storeFrom).context ctx) (fuel + 1) depth
        (Model.expanded nextState storeFrom).cfg bbSuspend []) (entryExit s a fid k)
      = .ok ([yieldValue], expandedSuspendExit s a fid k nextState enc) := by
  unfold stepNWithContext
  simp only [sr_model_byteModel, sr_model_functionOrder, sr_model_returnTypes,
    sr_items_nil, sr_items_ptr, sr_items_yield, sr_items_final, Sem.fromMemoryExcept, EvalContext.resolveBlock, EvalContext.resolveDrop, List.map_nil, List.map_cons,
    Model.cfg, Model.suspend, cfgWith, bbSuspend, suspendBlockExpanded, bodyInstsWithResultDests, sr_checked_nil, sr_checked_ptr, sr_model_load, sr_model_yield,
    sr_model_final, sr_model_index, sr_model_pointer, sr_model_state, sr_model_store, List.forIn_nil, List.forIn_cons, stepInstWithContext, sr_encode_i64, decodeMemoryWithFunctions,
    sr_model_gep, EvalContext.semGEPUsing_canonical, EvalContext.loadMemoryValueAligned,
    EvalContext.storeMemoryValueAligned, EvalContext.memoryRoute, EvalContext.originalClosureFor,
    EvalContext.memoryServiceFor, Ty.hasCanonicalMemoryLayout, if_true,
    sr_legacy_load, sr_legacy_store, sr_held_load_bind, sr_held_store_bind, stepTermWithContext, closureTermWithContext, stepInst, pure_bind,
    bind_assoc, Constant.hasSymbolAddr, constValueAtChecked_i64, constValueAtChecked_i32, constPointerFormsSupported, Ty.isInteger,
    constValueAt, constWidthAmbiguous, constHasInexactFloat,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bitWidthFor_i64, bitWidthFor_i32]
  simp only [Sem.run, sr_bind, Except.bind]
  rw [sr_bindBlockParams_nil]
  dsimp only
  rw [sr_bindFresh]
  dsimp only [MachineState.bindValue]
  rw [sr_bindInstrResultDests_one (value := yieldValue)]
  · dsimp only
    rw [sr_bindFresh]
    dsimp only [MachineState.bindValue]
    rw [sr_bindInstrResultDests_one (value := Value.intAt 64 0)]
    · dsimp only
      rw [sr_semGEPUsing_i64_zero]
      · dsimp only [MachineState.bindValue]
        rw [sr_bindInstrResultDests_one (value := .ptr a (some fid))]
        · dsimp only
          rw [sr_bindFresh]
          dsimp only [MachineState.bindValue]
          rw [sr_bindInstrResultDests_one (value := Value.intAt 64 nextState)]
          · dsimp only
            rw [sr_semStore_i64_ok (a := a) (fid := fid) (value := .int 64 stored) (enc := enc) (model := ctx.byteModel)]
            · dsimp only
              rw [sr_semReturn_one (v := yieldValue)]
              · trustIrReduce
              · rfl
            · exact hFrame
            · rfl
            · exact hFrom
            · rfl
            · simpa only [Value.intAt, encodeMemoryAt_i64_int] using hEnc
            · exact hLen
          · rfl
        · rfl
      · exact hFrame
      · rfl
      · rfl
      · exact typedIntegerValue_i64_zero ctx.byteModel
    · rfl
  · rfl

/-- **The expansion is the same state machine.** The generator whose suspend
    state is the correctly wired expansion has EXACTLY the round trip of the
    terminator form — same yielded values and frame writes; its additional source names are explicit in the exit states. -/
theorem coro_two_state_roundtrip_expanded (ctx : EvalContext) (depth : Nat) (a : Addr) (fid : AllocId)
    (s0 : MachineState) (hFrame : FrameOk s0.memory a fid ctx.byteModel)
    (hZero : s0.memory.readBytes a 8 = some (List.replicate 8 0)) :
    resumeWith ctx depth (.expanded 1 expansionStateId) a fid s0
      = .ok ([yieldValue], expandedSuspendExit s0 a fid 0 1 stateOneBytes) ∧
    resumeWith ctx depth (.expanded 1 expansionStateId) a fid (expandedSuspendExit s0 a fid 0 1 stateOneBytes)
      = .ok ([finalValue], finalExit (expandedSuspendExit s0 a fid 0 1 stateOneBytes) a fid 1) := by
  have hFrame' : FrameOk (s0.memory.writeBytes a stateOneBytes) a fid ctx.byteModel := hFrame
  have hRead1 : (s0.memory.writeBytes a stateOneBytes).readBytes a 8 = some stateOneBytes :=
    writeBytes_readBytes_general s0.memory a stateOneBytes
  constructor
  · have h1 := entry_run_case ctx 1 depth (.expanded 1 expansionStateId) a fid s0
      (List.replicate 8 0) 0 0 bbSuspend hFrame hZero rfl rfl
    have h2 := suspend_run_expanded ctx 0 depth 1 expansionStateId 1 a fid s0 0 stateOneBytes hFrame rfl rfl rfl
    simp only [Nat.zero_add] at h2
    unfold resumeWith
    rw [show (2 : Nat) = 1 + 1 from rfl, h1, h2]
  · have h1 := entry_run_case ctx 1 depth (.expanded 1 expansionStateId) a fid
      (expandedSuspendExit s0 a fid 0 1 stateOneBytes) stateOneBytes 1 1 bbFinal hFrame' hRead1 rfl rfl
    have h2 := final_run ctx 0 depth (.expanded 1 expansionStateId) a fid
      (expandedSuspendExit s0 a fid 0 1 stateOneBytes) 1
    simp only [Nat.zero_add] at h2
    unfold resumeWith
    rw [show (2 : Nat) = 1 + 1 from rfl, h1, h2]

/-- **Mis-wired expansion.** The expansion whose `store` reads the slot
    immediate source `%1` records state 0: its first resume still yields `42`, and
    its second resume yields `42` AGAIN. -/
theorem coro_two_state_miswired_loops (ctx : EvalContext) (depth : Nat) (a : Addr) (fid : AllocId)
    (s0 : MachineState) (hFrame : FrameOk s0.memory a fid ctx.byteModel)
    (hZero : s0.memory.readBytes a 8 = some (List.replicate 8 0)) :
    resumeWith ctx depth (.expanded 1 expansionIndexId) a fid s0
      = .ok ([yieldValue], expandedSuspendExit s0 a fid 0 1 stateZeroBytes) ∧
    resumeWith ctx depth (.expanded 1 expansionIndexId) a fid (expandedSuspendExit s0 a fid 0 1 stateZeroBytes)
      = .ok ([yieldValue],
          expandedSuspendExit (expandedSuspendExit s0 a fid 0 1 stateZeroBytes) a fid 0 1 stateZeroBytes) := by
  have hFrame' : FrameOk (s0.memory.writeBytes a stateZeroBytes) a fid ctx.byteModel := hFrame
  have hRead0 : (s0.memory.writeBytes a stateZeroBytes).readBytes a 8 = some stateZeroBytes :=
    writeBytes_readBytes_general s0.memory a stateZeroBytes
  constructor
  · have h1 := entry_run_case ctx 1 depth (.expanded 1 expansionIndexId) a fid s0
      (List.replicate 8 0) 0 0 bbSuspend hFrame hZero rfl rfl
    have h2 := suspend_run_expanded ctx 0 depth 1 expansionIndexId 0 a fid s0 0 stateZeroBytes hFrame rfl rfl rfl
    simp only [Nat.zero_add] at h2
    unfold resumeWith
    rw [show (2 : Nat) = 1 + 1 from rfl, h1, h2]
  · have h1 := entry_run_case ctx 1 depth (.expanded 1 expansionIndexId) a fid
      (expandedSuspendExit s0 a fid 0 1 stateZeroBytes) stateZeroBytes 0 0 bbSuspend hFrame' hRead0 rfl rfl
    have h2 := suspend_run_expanded ctx 0 depth 1 expansionIndexId 0 a fid (expandedSuspendExit s0 a fid 0 1 stateZeroBytes) 0
      stateZeroBytes hFrame' rfl rfl rfl
    simp only [Nat.zero_add] at h2
    unfold resumeWith
    rw [show (2 : Nat) = 1 + 1 from rfl, h1, h2]

/-- The mis-wired expansion's round trip is refuted: the operand wiring
    the source-aware expansion uses is load-bearing in the whole module. -/
theorem coro_two_state_roundtrip_miswired_refuted (ctx : EvalContext) (depth : Nat)
    (a : Addr) (fid : AllocId) (s0 : MachineState) (hFrame : FrameOk s0.memory a fid ctx.byteModel)
    (hZero : s0.memory.readBytes a 8 = some (List.replicate 8 0)) :
    ¬ ∃ s2, resumeWith ctx depth (.expanded 1 expansionIndexId) a fid
      (expandedSuspendExit s0 a fid 0 1 stateZeroBytes) = .ok ([finalValue], s2) := by
  intro ⟨s2, h⟩
  rw [(coro_two_state_miswired_loops ctx depth a fid s0 hFrame hZero).2] at h
  exact yieldValue_ne_finalValue (List.cons.inj (Prod.mk.inj (Except.ok.inj h)).1).1

end CoroGen

end TrustIr
