-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Phase 5 memory safety meta-theorem: whole-program safety properties
-- for memory, borrows, and ARC.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md, Section 6 Phase 5
-- Reference: Jung et al., "RustBelt: Securing the Foundations of the
--            Rust Programming Language", POPL 2018
-- Reference: Boyland, "Checking interference with fractional permissions", SAS 2003

import TrustIr.Semantics.Memory
import TrustIr.Semantics.Borrow
import TrustIr.Semantics.ARC
import TrustIr.Semantics.Step
import TrustIr.Proofs.MemoryProps

namespace TrustIr

/-!
# Memory Safety Meta-Theorems (Phase 5)

These theorems establish WHOLE-PROGRAM memory safety properties,
complementing the per-instruction properties in MemoryProps.lean,
BorrowProps.lean, and ARCProps.lean.

## Proved properties

1. **Well-formed memory invariant:** Definition and preservation of
   the well-formedness predicate for the memory subsystem.

2. **Borrow stack discipline:** The permission model maintains
   well-nested borrow invariants across borrow/endBorrow sequences.

3. **ARC soundness:** Balanced retain/release maintains the ARC
   invariant (no leaks, no use-after-free).

4. **Alloca progress:** Stack allocation always succeeds for
   well-typed requests.

5. **Load-after-store theorem sketch:** At the program level.

## Design note

These meta-theorems express properties about the interaction between
multiple subsystems (memory + permissions + refcounts), whereas the
Phase 2-3 proofs were per-subsystem. The key insight is that the
permission model serves as the unifying safety mechanism across all
three language paradigms (Rust borrows, Swift ARC, C raw pointers).
-/

-- =================================================================
-- Simp lemmas for monadic reduction
-- =================================================================

/-- Reduce throw applied to a state in the Sem monad. -/
@[simp] private theorem throw_sem_apply {α : Type} (e : SemError) (s : MachineState) :
    (throw e : Sem α) s = Except.error e := rfl

/-- Reduce Sem.throwUB applied to a state. -/
@[simp] private theorem Sem_throwUB_apply {α : Type} (msg : String) (s : MachineState) :
    (Sem.throwUB msg : Sem α) s = Except.error (SemError.ub msg) := rfl

/-- Reduce Sem.throwTypeError applied to a state. -/
@[simp] private theorem Sem_throwTypeError_apply {α : Type} (msg : String) (s : MachineState) :
    (Sem.throwTypeError msg : Sem α) s = Except.error (SemError.typeError msg) := rfl

-- =================================================================
-- Well-formed memory invariant
-- =================================================================

/-- A memory state is well-formed if:
    1. Every live allocation has a corresponding permission entry.
    2. No two live allocations overlap in address space.
    3. All addresses in live allocations are below nextAddr. -/
def well_formed_memory (s : MachineState) : Prop :=
  -- All live allocations have permissions
  (forall alloc, alloc ∈ s.memory.allocations -> alloc.alive ->
    s.permissions.get alloc.id != none) /\
  -- No overlapping live allocations
  (forall a1 a2 : Allocation,
    a1 ∈ s.memory.allocations -> a2 ∈ s.memory.allocations ->
    a1.alive -> a2.alive -> a1.id != a2.id ->
    a1.base + a1.size <= a2.base \/ a2.base + a2.size <= a1.base) /\
  -- All live allocations are below nextAddr
  (forall alloc, alloc ∈ s.memory.allocations -> alloc.alive ->
    alloc.base + alloc.size <= s.memory.nextAddr)

/-- The empty machine state is well-formed. -/
theorem empty_state_well_formed :
    well_formed_memory MachineState.empty := by
  simp [well_formed_memory, MachineState.empty, Memory.empty]

-- =================================================================
-- StateT.run characterization helpers
-- =================================================================
-- `Sem.run` unfolds definitionally to `StateT.run`, after which the
-- trailing monadic bind fuses into the discriminant of each `match`.
-- These lemmas commute `StateT.run` through the primitive `Sem`
-- operations, bind, pure, and if-then-else, so a `semStore` / `semLoad`
-- do-block can be peeled one effect at a time (keyed on `StateT.run`).

theorem sr_lookup (id : ValueId) (s : MachineState) :
    StateT.run (Sem.lookupValue id) s
      = match s.lookupValue id with
        | some v => .ok (v, s)
        | none => .error (.typeError s!"undefined SSA value: {repr id}") := by
  trustIrCompilerProof {
  unfold Sem.lookupValue
  cases h : s.lookupValue id <;>
    simp [h, Sem.getState, Sem.throwTypeError, bind, StateT.bind, StateT.get,
      StateT.run, pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, Except.bind,
      Except.pure, StateT.lift]
  } {
  unfold Sem.lookupValue
  cases h : s.lookupValue id <;>
    simp [h, Sem.getState, Sem.throwTypeError, bind, StateT.bind, StateT.get,
      StateT.run, pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, Except.bind,
      Except.pure, StateT.lift] <;> rfl
  }

theorem sr_get (s : MachineState) :
    StateT.run Sem.getState s = .ok (s, s) := rfl

theorem sr_modify (f : MachineState → MachineState) (s : MachineState) :
    StateT.run (Sem.modifyState f) s = .ok ((), f s) := rfl

theorem sr_set (s' s : MachineState) :
    StateT.run (Sem.setState s') s = .ok ((), s') := rfl

theorem sr_throwUB {α : Type} (m : String) (s : MachineState) :
    StateT.run (Sem.throwUB m : Sem α) s = .error (.ub m) := rfl

theorem sr_throwTE {α : Type} (m : String) (s : MachineState) :
    StateT.run (Sem.throwTypeError m : Sem α) s = .error (.typeError m) := rfl

theorem sr_throwUnsupported {α : Type} (f : UnsupportedFeature) (m : String) (s : MachineState) :
    StateT.run (Sem.throwUnsupported f m : Sem α) s = .error (.unsupported f m) := rfl

theorem sr_throw {α : Type} (e : SemError) (s : MachineState) :
    StateT.run (throw e : Sem α) s = .error e := rfl

theorem sr_bind {α β : Type} (m : Sem α) (f : α → Sem β) (s : MachineState) :
    StateT.run (m >>= f) s
      = (StateT.run m s).bind (fun p => StateT.run (f p.1) p.2) := rfl

theorem sr_pure {α : Type} (x : α) (s : MachineState) :
    StateT.run (pure x : Sem α) s = .ok (x, s) := rfl

theorem sr_ite {α : Type} (c : Prop) [Decidable c] (a b : Sem α) (s : MachineState) :
    StateT.run (if c then a else b) s = if c then StateT.run a s else StateT.run b s := by
  split <;> rfl

/-- `Sem.run` of `bindFresh` is the `bindValue` pair wrapped in `ok`. -/
theorem bindFresh_run (v : Value) (s0 : MachineState) :
    Sem.run (Sem.bindFresh v) s0 = .ok (s0.bindValue v) := rfl

/-- `StateT.run` of `bindFresh` is the `bindValue` pair (`StateT` spelling
    of `bindFresh_run`). -/
theorem sr_bindFresh (v : Value) (s : MachineState) :
    StateT.run (Sem.bindFresh v) s = .ok (s.bindValue v) := rfl

-- =================================================================
-- Invariant preservation, compositionally (`Sem.Keeps`)
-- =================================================================
-- A state predicate `P` is KEPT by a computation when every successful run
-- from a `P` state ends in a `P` state. Keeping composes through `bind`, and
-- a `match` / `if` keeps `P` when every branch does (`split`), so a whole
-- instruction is shown to keep an invariant by keeping it at each effect.

/-- `m` keeps `P`: every successful run from a `P` state ends in a `P`
    state. -/
def Sem.Keeps {α : Type} (P : MachineState → Prop) (m : Sem α) : Prop :=
  ∀ s r s', P s → Sem.run m s = .ok (r, s') → P s'

namespace Sem.Keeps
variable {P : MachineState → Prop}

theorem bind {α β : Type} {m : Sem α} {f : α → Sem β}
    (hm : Sem.Keeps P m) (hf : ∀ a, Sem.Keeps P (f a)) : Sem.Keeps P (m >>= f) := by
  intro s r s' hP h
  rw [Sem.run_bind] at h
  cases hr : Sem.run m s with
  | error e => rw [hr] at h; cases h
  | ok p =>
    rw [hr] at h
    exact hf p.1 p.2 r s' (hm s p.1 p.2 hP hr) h

theorem pure' {α : Type} (x : α) : Sem.Keeps P (pure x : Sem α) := by
  intro s r s' hP h
  simp only [Sem.run, StateT.run, pure, StateT.pure, Except.pure] at h
  cases h; exact hP

theorem throwUB {α : Type} (m : String) : Sem.Keeps P (Sem.throwUB m : Sem α) := by
  intro s r s' _ h; cases h

theorem throwTypeError {α : Type} (m : String) : Sem.Keeps P (Sem.throwTypeError m : Sem α) := by
  intro s r s' _ h; cases h

theorem getState : Sem.Keeps P Sem.getState := by
  intro s r s' hP h
  simp only [Sem.run, Sem.getState, StateT.run, StateT.get, pure, Except.pure] at h
  cases h; exact hP

/-- A `getState` followed by a computation that keeps `P` from the state it
    read. -/
theorem getState_bind {α : Type} {f : MachineState → Sem α}
    (hf : ∀ s0 r s', P s0 → Sem.run (f s0) s0 = .ok (r, s') → P s') :
    Sem.Keeps P (Sem.getState >>= f) := by
  intro s r s' hP h
  exact hf s r s' hP h

theorem lookupValue (id : ValueId) : Sem.Keeps P (Sem.lookupValue id) := by
  unfold Sem.lookupValue
  refine bind getState (fun st => ?_)
  split
  · exact pure' _
  · exact throwTypeError _

/-- `bindFresh` keeps every predicate that ignores the SSA locals. -/
theorem bindFresh (v : Value) (hP : ∀ s, P s → P (s.bindValue v).2) :
    Sem.Keeps P (Sem.bindFresh v) := by
  intro s r s' hs h
  rw [bindFresh_run] at h
  cases h
  exact hP s hs

end Sem.Keeps

/-- The borrow operand rule reads the state and changes nothing. -/
theorem keeps_borrowOperand (P : MachineState → Prop) (op : String) (v : Value) :
    Sem.Keeps P (borrowOperand op v) := by
  unfold borrowOperand
  refine Sem.Keeps.bind Sem.Keeps.getState (fun st => ?_)
  split
  · exact Sem.Keeps.pure' _
  · split
    · exact Sem.Keeps.throwUB _
    · exact Sem.Keeps.throwUB _
  · exact Sem.Keeps.throwUB _
  · exact Sem.Keeps.throwTypeError _

/-- `getPermission` reads the state and changes nothing. -/
theorem keeps_getPermission (P : MachineState → Prop) (id : AllocId) :
    Sem.Keeps P (getPermission id) := by
  unfold getPermission
  refine Sem.Keeps.bind Sem.Keeps.getState (fun st => ?_)
  split
  · exact Sem.Keeps.pure' _
  · exact Sem.Keeps.throwUB _

/-- The ARC operand rule reads the state and changes nothing. -/
theorem keeps_getAllocIdFromPtrARC (P : MachineState → Prop) (v : Value) :
    Sem.Keeps P (getAllocIdFromPtrARC v) := by
  unfold getAllocIdFromPtrARC
  refine Sem.Keeps.bind Sem.Keeps.getState (fun st => ?_)
  split
  · split
    · split
      · exact Sem.Keeps.pure' _
      · exact Sem.Keeps.throwUB _
    · exact Sem.Keeps.throwUB _
  · split
    · exact Sem.Keeps.throwUB _
    · exact Sem.Keeps.throwUB _
  · exact Sem.Keeps.throwUB _
  · exact Sem.Keeps.throwTypeError _

/-- `requireArcRef` reads the state and changes nothing. -/
theorem keeps_requireArcRef (P : MachineState → Prop) (id : AllocId) :
    Sem.Keeps P (requireArcRef id) := by
  unfold requireArcRef
  refine Sem.Keeps.bind Sem.Keeps.getState (fun st => ?_)
  split
  · exact Sem.Keeps.pure' _
  · exact Sem.Keeps.throwUB _
  · exact Sem.Keeps.throwUB _

/-- The ARC object-base rule reads the state and changes nothing. -/
theorem keeps_requireObjectBase (P : MachineState → Prop) (op : String) (v : Value)
    (id : AllocId) : Sem.Keeps P (requireObjectBase op v id) := by
  unfold requireObjectBase
  refine Sem.Keeps.bind Sem.Keeps.getState (fun st => ?_)
  split
  · split
    · exact Sem.Keeps.pure' _
    · exact Sem.Keeps.throwUB _
  · exact Sem.Keeps.throwUB _

-- =================================================================
-- Borrow stack discipline
-- =================================================================

/-- The borrow stack invariant: every shared borrow permission has
    a positive count. A count of 0 is an error state that should
    never be reached through well-formed borrow/endBorrow sequences. -/
def borrow_stack_valid (s : MachineState) : Prop :=
  forall allocId : AllocId,
    match s.permissions.get allocId with
    | some (.sharedBorrow n) => n > 0
    | _ => True

/-- `borrow_stack_valid` reads only the permissions. -/
private theorem keeps_bindFresh_bsv (v : Value) :
    Sem.Keeps borrow_stack_valid (Sem.bindFresh v) :=
  Sem.Keeps.bindFresh v (fun _ hs => hs)

/-- Setting one permission to a state the invariant admits keeps it. -/
private theorem keeps_setPermission_bsv (id : AllocId) (p : Permission)
    (hp : match p with | .sharedBorrow n => n > 0 | _ => True) :
    Sem.Keeps borrow_stack_valid (setPermission id p) := by
  intro s r s' hP h
  simp only [Sem.run, setPermission, Sem.modifyState, StateT.run, StateT.bind,
    StateT.get, StateT.set, bind, pure, StateT.pure, Except.pure, Except.bind] at h
  cases h
  intro aid
  simp only [PermissionMap.set, PermissionMap.get]
  by_cases hh : aid == id
  · simp [hh]
    cases p with
    | sharedBorrow n => exact hp
    | _ => trivial
  · simp [hh]; exact hP aid

/-- Borrowing preserves the borrow stack invariant. A `Borrow` either moves
    no permission (a fat pointer, or an operand outside its allocation's
    requested bytes) or moves its provenance allocation to `sharedBorrow 1` /
    `sharedBorrow (n + 1)`. -/
theorem borrow_preserves_stack (ptrId : ValueId) (s : MachineState)
    (hValid : borrow_stack_valid s)
    (result : ValueId × MachineState)
    (hOk : Sem.run (semBorrow ptrId) s = .ok result) :
    borrow_stack_valid result.snd := by
  have hKeep : Sem.Keeps borrow_stack_valid (semBorrow ptrId) := by
    unfold semBorrow
    refine Sem.Keeps.bind (Sem.Keeps.lookupValue _) (fun v => ?_)
    split
    · exact keeps_bindFresh_bsv _
    · refine Sem.Keeps.bind (keeps_borrowOperand _ _ _) (fun t => ?_)
      split
      · exact keeps_bindFresh_bsv _
      · refine Sem.Keeps.bind (keeps_getPermission _ _) (fun perm => ?_)
        split
        · exact Sem.Keeps.bind (keeps_setPermission_bsv _ _ (by show 1 > 0; omega))
            (fun _ => keeps_bindFresh_bsv _)
        · exact Sem.Keeps.bind (keeps_setPermission_bsv _ _ (by simp))
            (fun _ => keeps_bindFresh_bsv _)
        · exact Sem.Keeps.throwUB _
  exact hKeep s result.1 result.2 hValid hOk

/-- BorrowMut preserves the borrow stack invariant. -/
theorem borrow_mut_preserves_stack (ptrId : ValueId) (s : MachineState)
    (hValid : borrow_stack_valid s)
    (result : ValueId × MachineState)
    (hOk : Sem.run (semBorrowMut ptrId) s = .ok result) :
    borrow_stack_valid result.snd := by
  have hKeep : Sem.Keeps borrow_stack_valid (semBorrowMut ptrId) := by
    unfold semBorrowMut
    refine Sem.Keeps.bind (Sem.Keeps.lookupValue _) (fun v => ?_)
    split
    · exact keeps_bindFresh_bsv _
    · refine Sem.Keeps.bind (keeps_borrowOperand _ _ _) (fun t => ?_)
      split
      · exact keeps_bindFresh_bsv _
      · refine Sem.Keeps.bind (keeps_getPermission _ _) (fun perm => ?_)
        split
        · exact Sem.Keeps.bind (keeps_setPermission_bsv _ _ trivial)
            (fun _ => keeps_bindFresh_bsv _)
        · exact Sem.Keeps.throwUB _
  exact hKeep s result.1 result.2 hValid hOk

/-- EndBorrow preserves the borrow stack invariant. -/
theorem end_borrow_preserves_stack (ptrId : ValueId) (s : MachineState)
    (hValid : borrow_stack_valid s)
    (result : Unit × MachineState)
    (hOk : Sem.run (semEndBorrow ptrId) s = .ok result) :
    borrow_stack_valid result.snd := by
  have hKeep : Sem.Keeps borrow_stack_valid (semEndBorrow ptrId) := by
    unfold semEndBorrow
    refine Sem.Keeps.bind (Sem.Keeps.lookupValue _) (fun v => ?_)
    refine Sem.Keeps.bind Sem.Keeps.getState (fun st => ?_)
    split
    · exact Sem.Keeps.pure' _
    · refine Sem.Keeps.bind (keeps_getPermission _ _) (fun perm => ?_)
      split
      · split
        · exact Sem.Keeps.throwUB _
        · exact keeps_setPermission_bsv _ _ trivial
        · exact keeps_setPermission_bsv _ _ (by show _ > 0; omega)
      · exact keeps_setPermission_bsv _ _ trivial
      · exact Sem.Keeps.throwUB _
  exact hKeep s result.1 result.2 hValid hOk

/-- Borrow round-trip: borrowing and then ending preserves the original
    permission. Combined with borrow_preserves_stack, this shows that
    well-nested borrow sequences maintain the invariant. -/
theorem borrow_endBorrow_roundtrip_permission (perm : Permission)
    (hOwned : perm = Permission.owned) :
    endBorrowPermission (borrowPermission perm) = perm := by
  subst hOwned
  simp [borrowPermission, endBorrowPermission]

-- =================================================================
-- ARC soundness
-- =================================================================

/-- The ARC invariant: every allocation with arcRef permission has
    a positive reference count. -/
def arc_sound (s : MachineState) : Prop :=
  forall allocId : AllocId,
    match s.permissions.get allocId with
    | some .arcRef =>
      match s.refCounts allocId with
      | some n => n > 0
      | none => False
    | _ => True

/-- arc_sound is preserved when we update refCounts with setRefCount,
    provided the new count is positive for the target allocId. -/
private theorem arc_sound_setRefCount
    (s : MachineState) (targetId : AllocId) (newCount : Nat)
    (hSound : arc_sound s)
    (hPos : newCount > 0) :
    arc_sound { s with refCounts := setRefCount s.refCounts targetId newCount } := by
  intro aid
  unfold arc_sound at hSound
  simp only [PermissionMap.get, setRefCount]
  by_cases h : aid == targetId
  · -- aid == targetId: new refcount is newCount (positive)
    simp only [h, ite_true]
    cases s.permissions aid with
    | none => trivial
    | some perm =>
      cases perm with
      | arcRef => exact hPos
      | _ => trivial
  · -- aid ≠ targetId: refcount unchanged
    simp only [h, ite_false]
    exact hSound aid

/-- arc_sound is preserved when we clear the permission for an allocId
    and zero its refcount. After clearPermission, permissions.get returns
    none, so the arc_sound match gives True. -/
private theorem arc_sound_clearPermission
    (s : MachineState) (targetId : AllocId) (mem' : Memory)
    (hSound : arc_sound s) :
    arc_sound { s with
      memory := mem'
      permissions := clearPermission s.permissions targetId
      refCounts := setRefCount s.refCounts targetId 0 } := by
  intro aid
  unfold arc_sound at hSound
  simp only [PermissionMap.get, clearPermission, setRefCount]
  by_cases h : aid == targetId
  · simp only [h, ite_true]
  · simp only [h, ite_false]; exact hSound aid

/-- Retain preserves the ARC invariant.
    Retain increments the reference count, so if it was positive before,
    it is still positive after. -/
theorem retain_preserves_arc_sound (ptrId : ValueId) (s : MachineState)
    (hSound : arc_sound s)
    (result : Unit × MachineState)
    (hOk : Sem.run (semRetain ptrId) s = .ok result) :
    arc_sound result.snd := by
  have hKeep : Sem.Keeps arc_sound (semRetain ptrId) := by
    unfold semRetain
    refine Sem.Keeps.bind (Sem.Keeps.lookupValue _) (fun v => ?_)
    refine Sem.Keeps.bind (keeps_getAllocIdFromPtrARC _ _) (fun id => ?_)
    refine Sem.Keeps.bind (keeps_requireArcRef _ _) (fun _ => ?_)
    refine Sem.Keeps.bind (keeps_requireObjectBase _ _ _ _) (fun _ => ?_)
    refine Sem.Keeps.getState_bind (fun s0 r s' hs h => ?_)
    simp only [Sem.run, sr_set] at h
    cases h
    exact arc_sound_setRefCount s0 id _ hs (by omega)
  exact hKeep s result.1 result.2 hSound hOk

/-- Release preserves the ARC invariant. -/
theorem release_preserves_arc_sound (ptrId : ValueId) (s : MachineState)
    (hSound : arc_sound s)
    (result : Unit × MachineState)
    (hOk : Sem.run (semRelease ptrId) s = .ok result) :
    arc_sound result.snd := by
  have hKeep : Sem.Keeps arc_sound (semRelease ptrId) := by
    unfold semRelease
    refine Sem.Keeps.bind (Sem.Keeps.lookupValue _) (fun v => ?_)
    refine Sem.Keeps.bind (keeps_getAllocIdFromPtrARC _ _) (fun id => ?_)
    refine Sem.Keeps.bind (keeps_requireArcRef _ _) (fun _ => ?_)
    refine Sem.Keeps.bind (keeps_requireObjectBase _ _ _ _) (fun _ => ?_)
    refine Sem.Keeps.getState_bind (fun s0 r s' hs h => ?_)
    simp only [Sem.run] at h
    revert h
    generalize getRefCount s0.refCounts id = count
    intro h
    match count, h with
    | 0, h => cases h
    | 1, h =>
      unfold deallocARC at h
      rw [sr_bind, sr_get] at h
      simp only [Except.bind] at h
      rw [sr_ite] at h
      split at h
      · cases h
      · rw [sr_set] at h
        cases h
        exact arc_sound_clearPermission s0 id _ hs
    | n + 2, h =>
      rw [sr_set] at h
      cases h
      exact arc_sound_setRefCount s0 id _ hs (by omega)
  exact hKeep s result.1 result.2 hSound hOk

-- =================================================================
-- Alloca progress
-- =================================================================

/-- Every type with a byte size has a power-of-two natural alignment, so an
    `Alloca` / `HeapAlloc` with no declared alignment never fails its
    alignment check. -/
theorem byteAlign_isPow2 (ty : Ty) (hTy : ty.byteSize ≠ none) :
    isPow2 (ty.byteAlign.getD 1) = true := by
  cases ty <;> try rfl
  case Vector count elemTy =>
    simp only [Ty.byteAlign]
    split
    · rfl
    · cases elemTy <;> rfl

/-- A power-of-two declared-or-natural alignment passes the placement check. -/
theorem placementAlign_ok (op : String) (ty : Ty) (align : Option Nat) (s : MachineState)
    (h : isPow2 (align.getD (ty.byteAlign.getD 1)) = true) :
    StateT.run (Sem.placementAlign op ty align) s = .ok (align.getD (ty.byteAlign.getD 1), s) := by
  unfold Sem.placementAlign Sem.declaredOrNaturalAlign
  simp only [Ty.byteAlignFor]
  simp only [h, if_true]
  rfl

/-- Lifting a pure checked memory operation does not change machine state. -/
theorem sr_memoryExcept {α : Type} (result : Except SemError α) (s : MachineState) :
    StateT.run (Sem.fromMemoryExcept result) s =
      result.map (fun value => (value, s)) := by
  cases result <;> rfl

/-- Allocation progress for an admitted source declaration and finite memory
    request. Each premise names an independent dispatcher/layout/word/capacity
    check. The old unbounded-64 theorem was false for an exhausted allocator.
    No signedness is inferred from an untyped integer carrier. -/
theorem alloca_progress (layoutOf : MemoryLayoutQuery) (reader : IntegerOperandReader)
    (ty : Ty) (countId : Option ValueId) (align : Option Nat) (model : ByteModel)
    (s : MachineState) (layout : MemoryTypeLayout) (count size alignment : Nat)
    (hLayout : layoutOf ty = .ok layout)
    (hCount : (countId = none ∧ count = 1) ∨
      ∃ id value integer, countId = some id ∧ s.lookupValue id = some value ∧
        reader id value = .ok integer ∧ checkedWord64Operand "Alloca" true integer = .ok count)
    (hSize : checkedWord64Mul "Alloca" layout.size count = .ok size)
    (hAlign : checkedMemoryAlign "Alloca" layout.alignment align = .ok alignment)
    (hCapacity : checkWordAllocation model s.memory size alignment 0 = .ok ()) :
    ∃ result, Sem.run (semAllocaUsing layoutOf reader ty countId align model) s = .ok result := by
  unfold semAllocaUsing semAllocateUsing
  rcases hCount with ⟨rfl, rfl⟩ | ⟨id, value, integer, rfl, hv, hr, hc⟩
  · simp only [pure_bind, hLayout, hSize, hAlign, Sem.run, sr_bind, sr_memoryExcept,
      sr_pure, sr_get, Except.map, Except.bind, hCapacity, sr_set, Bool.false_eq_true,
      ↓reduceIte]
    exact ⟨_, rfl⟩
  · simp only [Sem.run, sr_bind, sr_lookup, hv, Except.bind, sr_pure, hLayout,
      sr_memoryExcept, Except.map, hr, hc, hSize, hAlign, sr_get, hCapacity, sr_set,
      Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, rfl⟩

-- =================================================================
-- Memory safety: Load/Store interaction
-- =================================================================

/-- Byte-level load-after-store: writing encoded bytes and reading them
    back produces the original encoded bytes.

    This is the core byte-level property that underpins load-after-store
    safety. It is fully proved using writeBytes_readBytes_general from
    MemoryProps. -/
theorem load_after_store_bytes (mem : Memory) (addr : Addr) (ty : Ty) (v : Value)
    (encoded : List UInt8) (_hEnc : encodeValueAt ty v = .ok encoded) :
    (mem.writeBytes addr encoded).readBytes addr encoded.length = some encoded :=
  writeBytes_readBytes_general mem addr encoded

/-- Byte-level load-after-store with type decoding: writing encoded bytes,
    reading them back, and decoding (in the written memory, where a loaded
    pointer recovers its provenance) recovers the original decode result.
    Stated over the TYPED codec (`encodeValueAt` / `decodeValueAt`) every
    memory access uses, floats included (WS2.23). -/
theorem load_after_store_decode (mem : Memory) (addr : Addr) (ty : Ty)
    (v : Value) (encoded : List UInt8)
    (_hEnc : encodeValueAt ty v = .ok encoded)
    (byteSize : Nat) (_hBS : ty.byteSize = some byteSize)
    (hLen : encoded.length = byteSize) :
    exists bytes, (mem.writeBytes addr encoded).readBytes addr byteSize = some bytes
      /\ decodeValueAt (mem.writeBytes addr encoded) ty bytes
        = decodeValueAt (mem.writeBytes addr encoded) ty encoded := by
  have hRead := writeBytes_readBytes_general mem addr encoded
  rw [hLen] at hRead
  exact ⟨encoded, hRead, rfl⟩

-- The access operand rule, characterized.

/-- `Memory.lookup` returns an allocation with the id it was asked for. -/
theorem Memory.lookup_id {mem : Memory} {id : AllocId} {a : Allocation}
    (h : mem.lookup id = some a) : a.id = id := by
  unfold Memory.lookup at h
  have := find?_some_pred h
  simpa using this

/-- `Memory.lookup` returns a member of the allocation list. -/
theorem Memory.lookup_mem {mem : Memory} {id : AllocId} {a : Allocation}
    (h : mem.lookup id = some a) : a ∈ mem.allocations := by
  unfold Memory.lookup at h
  exact mem_of_find?_some h

/-- Writing bytes leaves the allocation table, hence every lookup, alone. -/
@[simp] theorem Memory.lookup_writeBytes (mem : Memory) (addr : Addr) (data : List UInt8)
    (id : AllocId) : (mem.writeBytes addr data).lookup id = mem.lookup id := rfl

/-- The pointer check (`Sem.expectPointer`, the interpreter's
    `expect_pointer`): a successful run leaves the state alone and the operand
    is a provenance pointer. -/
theorem expectPointer_ok_inv (op : String) (v : Value) (s s' : MachineState)
    (p : Addr × AllocId) (h : StateT.run (Sem.expectPointer op v) s = .ok (p, s')) :
    s' = s ∧ v = .ptr p.1 (some p.2) := by
  unfold Sem.expectPointer at h
  match v, h with
  | .ptr addr (some id), h =>
    rw [sr_pure] at h
    cases h
    exact ⟨rfl, rfl⟩
  | .ptr addr none, h =>
    rw [sr_ite] at h
    split at h <;> cases h
  | .nullPtr, h => cases h
  | .int .., h | .float .., h | .bool .., h | .aggregate .., h | .vector .., h | .frame .., h
  | .set .., h | .sequence .., h | .record .., h | .closure .., h | .typedClosure .., h | .fatPtr .., h
  | .partial .., h | .undef .., h | .uninit, h => cases h

/-- A provenance pointer passes the pointer check unchanged. -/
theorem expectPointer_ptr (op : String) (a : Addr) (id : AllocId) (s : MachineState) :
    StateT.run (Sem.expectPointer op (.ptr a (some id))) s = .ok ((a, id), s) := rfl

/-- The access check (`Sem.checkedAccess`, the interpreter's
    `checked_access`): a successful run leaves the state alone and the address
    lies, aligned, inside the LIVE allocation `id` names. -/
theorem checkedAccess_ok_inv (op : String) (addr : Addr) (id : AllocId) (size align : Nat)
    (s s' : MachineState) (a : Addr)
    (h : StateT.run (Sem.checkedAccess op addr id size align) s = .ok (a, s')) :
    s' = s ∧ a = addr ∧ ∃ alloc, s.memory.lookup id = some alloc ∧
      alloc.alive = true ∧ (align = 0 ∨ addr % align = 0) ∧
      alloc.base ≤ addr ∧ addr - alloc.base + size ≤ alloc.size := by
  unfold Sem.checkedAccess at h
  simp only [Sem.checkTargetRange, pure_bind] at h
  rw [sr_bind, sr_get] at h
  simp only [Except.bind] at h
  rcases hl : s.memory.lookup id with _ | alloc
  · rw [hl, sr_throwUB] at h; cases h
  · rw [hl] at h
    simp only [] at h
    rw [sr_ite] at h
    split at h
    · cases h
    · rename_i hAlive
      rw [sr_ite] at h
      split at h
      · cases h
      · rename_i hAl
        rw [sr_ite] at h
        split at h
        · cases h
        · rename_i hIn
          rw [sr_pure] at h
          cases h
          have hb : ¬ addr < alloc.base := by intro hh; apply hIn; simp [hh]
          have he : ¬ (addr - alloc.base + size > alloc.size) := by
            intro hh; apply hIn; simp [hh]
          refine ⟨rfl, rfl, alloc, rfl, by simpa using hAlive, ?_, ?_, ?_⟩
          · by_cases h0 : align = 0
            · exact Or.inl h0
            · right; simp [h0] at hAl; exact hAl
          · exact Nat.le_of_not_lt hb
          · exact Nat.le_of_not_lt he

/-- The converse: an address inside, and aligned for, a live allocation passes
    the access check without touching the state. -/
theorem checkedAccess_ok_of (op : String) (size align : Nat) (s : MachineState)
    (a : Addr) (id : AllocId) (alloc : Allocation)
    (hl : s.memory.lookup id = some alloc) (hAlive : alloc.alive = true)
    (hAl : align = 0 ∨ a % align = 0) (hBase : alloc.base ≤ a)
    (hEnd : a - alloc.base + size ≤ alloc.size) :
    StateT.run (Sem.checkedAccess op a id size align) s = .ok (a, s) := by
  unfold Sem.checkedAccess
  simp only [Sem.checkTargetRange, pure_bind]
  have h2 : (align != 0 && a % align != 0) = false := by
    rcases hAl with h | h <;> simp [h]
  have h3 : (decide (a < alloc.base) || decide (a - alloc.base + size > alloc.size)) = false := by
    have h3a : ¬ a < alloc.base := Nat.not_lt_of_le hBase
    have h3b : ¬ (a - alloc.base + size > alloc.size) := Nat.not_lt_of_le hEnd
    simp [h3a, h3b]
  simp only [sr_bind, sr_get, Except.bind, hl, sr_ite, hAlive, h2, h3, Bool.not_true,
    Bool.false_eq_true, if_false, sr_pure]

/-- **The access operand rule** (`Sem.accessAddr`): a successful access check
    leaves the state alone and names an address inside the LIVE allocation the
    pointer was derived from — never a neighbour. The interpreter's
    `expect_pointer` + `checked_access`. -/
theorem semAccess_names_provenance (op : String) (v : Value) (size align : Nat)
    (s s' : MachineState) (a : Addr)
    (h : StateT.run (Sem.accessAddr op v size align) s = .ok (a, s')) :
    s' = s ∧ ∃ id alloc, v = .ptr a (some id) ∧ s.memory.lookup id = some alloc ∧
      alloc.alive = true ∧ (align = 0 ∨ a % align = 0) ∧
      alloc.base ≤ a ∧ a - alloc.base + size ≤ alloc.size := by
  unfold Sem.accessAddr at h
  rw [sr_bind] at h
  rcases hp : StateT.run (Sem.expectPointer op v) s with e | ⟨⟨addr, id⟩, s1⟩
  · rw [hp] at h; cases h
  obtain ⟨hs1, hv⟩ := expectPointer_ok_inv op v s s1 (addr, id) hp
  subst s1
  rw [hp] at h
  simp only [Except.bind] at h
  obtain ⟨hs', ha, alloc, hl, hAlive, hAl, hBase, hEnd⟩ :=
    checkedAccess_ok_inv op addr id size align s s' a h
  subst hs' ha
  exact ⟨rfl, id, alloc, hv, hl, hAlive, hAl, hBase, hEnd⟩

/-- The converse: a pointer derived from a live allocation, aligned and in
    bounds, passes the access check without touching the state. -/
theorem accessAddr_ok_of (op : String) (size align : Nat) (s : MachineState)
    (a : Addr) (id : AllocId) (alloc : Allocation)
    (hl : s.memory.lookup id = some alloc) (hAlive : alloc.alive = true)
    (hAl : align = 0 ∨ a % align = 0) (hBase : alloc.base ≤ a)
    (hEnd : a - alloc.base + size ≤ alloc.size) :
    StateT.run (Sem.accessAddr op (.ptr a (some id)) size align) s = .ok (a, s) := by
  unfold Sem.accessAddr
  rw [sr_bind, expectPointer_ptr]
  exact checkedAccess_ok_of op size align s a id alloc hl hAlive hAl hBase hEnd

/-- A successful alignment check leaves the state alone and yields the
    declared-or-natural alignment, a power of two. -/
theorem accessAlign_ok_inv (op : String) (ty : Ty) (align : Option Nat) (s s' : MachineState)
    (al : Nat) (h : StateT.run (Sem.accessAlign op ty align) s = .ok (al, s')) :
    s' = s ∧ al = align.getD (ty.byteAlign.getD 1) ∧ isPow2 al = true := by
  unfold Sem.accessAlign Sem.declaredOrNaturalAlign at h
  simp only at h
  split at h
  · rename_i hp
    simp only [sr_pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, hp⟩
  · cases h

/-- A power-of-two declared-or-natural alignment passes the check. -/
theorem accessAlign_ok (op : String) (ty : Ty) (align : Option Nat) (s : MachineState)
    (h : isPow2 (align.getD (ty.byteAlign.getD 1)) = true) :
    StateT.run (Sem.accessAlign op ty align) s = .ok (align.getD (ty.byteAlign.getD 1), s) := by
  unfold Sem.accessAlign Sem.declaredOrNaturalAlign
  simp only [Ty.byteAlignFor]
  simp only [h, if_true]
  rfl

/-- A successful poison inspection is read-only. -/
theorem rejectPartial_ok_state (op : String) (value : Value) (s s' : MachineState)
    (unit : Unit) (h : StateT.run (Sem.rejectPartial value op) s = .ok (unit, s')) :
    s' = s := by
  cases value <;> first | (cases h; rfl) | (cases h)

/-- A successful pure alignment check gives the selected alignment and its
    u64/power-of-two guards. -/
theorem checkedMemoryAlign_ok_inv (op : String) (natural : Nat) (declared : Option Nat)
    (alignment : Nat) (h : checkedMemoryAlign op natural declared = .ok alignment) :
    alignment = declared.getD natural ∧ alignment ≤ word64Max ∧ isPow2 alignment = true := by
  unfold checkedMemoryAlign at h
  dsimp only at h
  split at h
  · rename_i good
    simp only [Bool.and_eq_true, decide_eq_true_eq] at good
    cases h
    exact ⟨rfl, good.1, good.2⟩
  · contradiction

set_option maxHeartbeats 4000000 in
/-- Successful non-poison stores expose the original operands, complete
    scalar layout, provenance, alignment, access bounds and exact byte write.
    The shared held-value core publishes no private SSA values. -/
theorem semStore_writes (ty : Ty) (ptrId valId : ValueId)
    (s s1 : MachineState)
    (hNotPoison : ∀ v, s.lookupValue valId = some v → v.isPoison = false)
    (hOk : Sem.run (semStore ty ptrId valId) s = .ok ((), s1)) :
    ∃ (a : Nat) (id : AllocId) (alloc : Allocation) (bs : Nat) (val : Value)
        (enc : List UInt8),
      s.lookupValue ptrId = some (.ptr a (some id)) ∧
      s.memory.lookup id = some alloc ∧ alloc.alive = true ∧
      isPow2 (ty.byteAlign.getD 1) = true ∧ a % (ty.byteAlign.getD 1) = 0 ∧
      alloc.base ≤ a ∧ a - alloc.base + bs ≤ alloc.size ∧
      ty.byteSize = some bs ∧ s.lookupValue valId = some val ∧
      encodeValueAt ty val = .ok enc ∧ enc.length = bs ∧
      s1 = { s with memory := s.memory.writeBytes a enc } := by
  unfold semStore semStoreUsing at hOk <;> try contradiction
  simp only [Sem.run, sr_bind, sr_lookup] at hOk <;> try contradiction
  rcases hp : s.lookupValue ptrId with _ | pointer
  · simp only [hp, Except.bind] at hOk <;> try contradiction
  simp only [hp, Except.bind, sr_bind, sr_lookup] at hOk <;> try contradiction
  rcases hv : s.lookupValue valId with _ | value
  · simp only [hv, Except.bind] at hOk <;> try contradiction
  simp only [hv, Except.bind] at hOk <;> try contradiction
  unfold semStoreValueUsing at hOk <;> try contradiction
  simp only [sr_bind] at hOk <;> try contradiction
  cases hre : StateT.run (Sem.rejectPartial pointer "Store") s with
  | error error => simp only [hre, Except.bind] at hOk <;> try contradiction
  | ok pair =>
    rcases pair with ⟨unit, state⟩
    have same := rejectPartial_ok_state _ _ _ _ _ hre
    subst state
    simp only [hre, Except.bind] at hOk <;> try contradiction
    rcases hptr : StateT.run (Sem.expectPointer "Store" pointer) s with e | ⟨⟨pa, id⟩, sp⟩
    · simp only [hptr, Except.bind] at hOk <;> try contradiction
    obtain ⟨hsp, hPtr⟩ := expectPointer_ok_inv _ _ _ _ _ hptr
    subst sp
    simp only [hptr, Except.bind] at hOk <;> try contradiction
    cases hbs : ty.byteSize with
    | none =>
      simp only [scalarMemoryLayout, Ty.byteSizeFor, hbs, sr_memoryExcept,
        Except.map, Except.bind] at hOk <;> try contradiction
    | some bs =>
      simp only [scalarMemoryLayout_of_byteSize ty bs hbs, sr_memoryExcept,
        Except.map, Except.bind] at hOk <;> try contradiction
      cases hal : checkedMemoryAlign "Store" (ty.byteAlign.getD 1) none with
      | error error => simp only [hal, sr_memoryExcept, Except.map, Except.bind] at hOk <;> try contradiction
      | ok al =>
        obtain ⟨hAlEq, _, hPow⟩ := checkedMemoryAlign_ok_inv _ _ _ _ hal
        simp only [hal, sr_memoryExcept, Except.map, Except.bind] at hOk <;> try contradiction
        rcases hacc : StateT.run (Sem.checkedAccess "Store" pa id bs al) s with e | ⟨a, sa⟩
        · simp only [hacc, Except.bind] at hOk <;> try contradiction
        obtain ⟨hsa, hapa, alloc, hl, hAlive, hAl, hBase, hEnd⟩ :=
          checkedAccess_ok_inv _ _ _ _ _ _ _ _ hacc
        subst sa
        subst hapa
        subst hPtr
        simp only [hacc, Except.bind, sr_bind, sr_get, hNotPoison value hv,
          Bool.false_eq_true, ↓reduceIte, encodeMemoryAt, fatPtrStoreValueValidFor] at hOk <;> try contradiction
        split at hOk
        · simp only [sr_bind, sr_throwTE, Except.bind] at hOk <;> try contradiction
        cases hwords : checkPointerImageWords .le64 value with
        | error error =>
          simp only [hwords, Except.bind, sr_bind, sr_pure, sr_throw] at hOk <;> try contradiction
        | ok unit =>
          simp only [hwords, Except.bind] at hOk <;> try contradiction
          rcases hev : encodeValueAt ty value with error | enc
          · simp only [hev, sr_bind, sr_pure, sr_throw, Except.bind] at hOk <;> try contradiction
          simp only [hev, sr_bind, sr_pure, sr_throwTE, sr_modify, sr_ite, Except.bind] at hOk <;> try contradiction
          split at hOk
          · exact absurd hOk (by simp)
          rename_i hlen
          rw [Except.ok.injEq, Prod.mk.injEq] at hOk <;> try contradiction
          obtain ⟨_, hOk⟩ := hOk
          simp only [Option.getD_none] at hAlEq
          subst hAlEq
          have aligned : a % (ty.byteAlign.getD 1) = 0 := by
            rcases hAl with h0 | h0
            · rw [h0] at hPow; contradiction
            · exact h0
          exact ⟨a, id, alloc, bs, value, enc, rfl, hl, hAlive, hPow, aligned,
            hBase, hEnd, rfl, rfl, hev, by simpa using hlen, hOk.symm⟩

/-- Store changes only its byte memory image; registers, permissions and
    reference counts are preserved. -/
theorem semStore_characterize (ty : Ty) (ptrId valId : ValueId) (s s1 : MachineState)
    (hNotPoison : ∀ v, s.lookupValue valId = some v → v.isPoison = false)
    (hOk : Sem.run (semStore ty ptrId valId) s = .ok ((), s1)) :
    ∃ (addr : Addr) (encoded : List UInt8),
      s1.memory = s.memory.writeBytes addr encoded ∧ s1.locals = s.locals ∧
      s1.permissions = s.permissions ∧ s1.refCounts = s.refCounts ∧
      s1.nextValueId = s.nextValueId := by
  obtain ⟨a, id, alloc, bs, value, enc, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ :=
    semStore_writes ty ptrId valId s s1 hNotPoison hOk
  exact ⟨a, enc, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- Program-level load-after-store: storing a value and then loading it
    back through the same pointer recovers a value equal to the decode of
    the original encoding, in the memory the store left.

    Proved via `semStore_writes` (the exact store characterization) to
    pin the written bytes, the address and the allocation the pointer was
    derived from, then peeling `semLoad` on the post-store state: the store
    left the allocation table alone (`Memory.lookup_writeBytes`), so the load
    passes the same access check (`accessAddr_ok_of`), and the byte-level
    round-trip is `writeBytes_readBytes_general`. -/
theorem load_after_store_program (ty : Ty) (ptrId valId : ValueId)
    (s : MachineState) (s1 : MachineState) (s2 : MachineState)
    (v : Value) (resultId : ValueId)
    (_hByteSize : ty.byteSize != none)
    (hStore : Sem.run (semStore ty ptrId valId) s = .ok ((), s1))
    (hLoad : Sem.run (semLoad ty ptrId) s1 = .ok (resultId, s2))
    (hLookup : s.lookupValue valId = some v)
    -- Non-poison value: the copy-propagates-poison store path has no
    -- `encodeValueAt`/`writeBytes` round-trip (it writes the raw image), so the
    -- typed store→load round-trip this theorem states is stated for real values.
    (hvNotPoison : v.isPoison = false)
    (encoded : List UInt8)
    (hEncode : encodeValueAt ty v = .ok encoded) :
    exists v', s2.lookupValue resultId = some v' /\
      decodeValueAt s1.memory ty encoded = .ok v' := by
  have hNP : ∀ v', s.lookupValue valId = some v' → v'.isPoison = false := by
    intro v' hv'
    exact (Option.some.inj (hv'.symm.trans hLookup)) ▸ hvNotPoison
  obtain ⟨a, id, alloc, bs, val, enc, hp, hl, hAlive, hPow, hAl, hBase, hEnd, hbs, hv, hev,
      hlen, hs1⟩ := semStore_writes ty ptrId valId s s1 hNP hStore
  have hvv : val = v := Option.some.inj (hv.symm.trans hLookup)
  subst hvv
  have hee : enc = encoded := by
    rw [hev] at hEncode; exact Except.ok.inj hEncode
  subst hee
  subst hs1
  have hp' : ({s with memory := s.memory.writeBytes a enc} : MachineState).lookupValue ptrId
      = some (.ptr a (some id)) := hp
  have hread : ({s with memory := s.memory.writeBytes a enc} : MachineState).memory.readBytes a bs
      = some enc := by
    rw [← hlen]; exact writeBytes_readBytes_general s.memory a enc
  have hacc := checkedAccess_ok_of "Load" bs ((none : Option Nat).getD (ty.byteAlign.getD 1))
    ({s with memory := s.memory.writeBytes a enc} : MachineState) a id alloc
    (by simpa using hl) hAlive (Or.inr hAl) hBase hEnd
  have hal := accessAlign_ok "Load" ty none
    ({s with memory := s.memory.writeBytes a enc} : MachineState) hPow
  unfold semLoad semLoadUsing semLoadValueUsing at hLoad <;> try contradiction
  simp only [Ty.byteSizeFor, decodeMemoryAt, isPartialLoadTyFor] at hLoad <;> try contradiction
  simp only [Sem.run, sr_bind, sr_lookup, hp', Except.bind, Sem.rejectPartial, expectPointer_ptr, hbs,
    sr_pure] at hLoad <;> try contradiction
  rw [hal] at hLoad <;> try contradiction
  simp only [Except.bind] at hLoad <;> try contradiction
  rw [hacc] at hLoad <;> try contradiction
  simp only [Except.bind, sr_bind, sr_get, hread] at hLoad <;> try contradiction
  rcases hdec : decodeValueAt (s.memory.writeBytes a enc) ty enc with e | v2
  · simp only [hdec, sr_throw] at hLoad <;> cases hLoad
  simp only [hdec] at hLoad <;> try contradiction
  have hLoad2 : Sem.run (Sem.bindFresh v2)
      ({s with memory := s.memory.writeBytes a enc} : MachineState) = .ok (resultId, s2) := hLoad
  rw [bindFresh_run, Except.ok.injEq] at hLoad2
  have hres : resultId
      = (({s with memory := s.memory.writeBytes a enc} : MachineState).bindValue v2).1 := by
    rw [hLoad2]
  have hs2 : s2
      = (({s with memory := s.memory.writeBytes a enc} : MachineState).bindValue v2).2 := by
    rw [hLoad2]
  refine ⟨v2, ?_, rfl⟩
  rw [hres, hs2]
  simp [MachineState.lookupValue, MachineState.bindValue, ValueMap.get, ValueMap.set]

-- =================================================================
-- Dealloc lifecycle (B2): dead-marking and double-free UB
-- =================================================================

/-- `find?` over a `map`: the image of the first element whose image passes. -/
theorem find?_map_alloc {α β : Type _} (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).find? p = (l.find? (fun a => p (f a))).map f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.find?_cons]
    cases p (f x) <;> simp [ih]

set_option maxHeartbeats 4000000 in
/-- **`semDealloc` frees its provenance** (B2 dead-marking half): a successful
    `semDealloc` went through a pointer derived from a LIVE allocation, at
    exactly that allocation's base, whose recorded permission allows
    deallocation (`Permission.canDealloc` — owned or rawPtr; borrows and ARC
    refs cannot reach the success path), and the result state is the input
    state with exactly that allocation marked `alive := false` and its
    permission and refcount entries cleared. It never frees a neighbour that
    starts at the same address: the allocation is named by provenance.
    Locals, byte store, and the allocator counters are pinned unchanged by
    the final-state equation. -/
theorem semDealloc_marks_dead (ptrId : ValueId) (s s1 : MachineState)
    (hOk : Sem.run (semDealloc ptrId) s = .ok ((), s1)) :
    exists (addr : Addr) (alloc : Allocation) (perm : Permission),
      s.lookupValue ptrId = some (.ptr addr (some alloc.id)) ∧
      s.memory.lookup alloc.id = some alloc ∧
      alloc.alive = true ∧
      alloc.base = addr ∧
      s.permissions.get alloc.id = some perm ∧
      perm.canDealloc = true ∧
      s1 = { s with
        memory := { s.memory with
          allocations := s.memory.allocations.map fun a =>
            if a.id == alloc.id then { a with alive := false } else a }
        permissions := clearPermissionAt s.permissions alloc.id
        refCounts := clearRefCountAt s.refCounts alloc.id } ∧
      { alloc with alive := false } ∈ s1.memory.allocations ∧
      s1.permissions.get alloc.id = none ∧
      s1.refCounts alloc.id = none := by
  unfold semDealloc at hOk <;> try contradiction
  simp only [Sem.run, sr_bind, sr_lookup] at hOk <;> try contradiction
  rcases hp : s.lookupValue ptrId with _ | ptrVal
  · simp only [hp, Except.bind] at hOk <;> try contradiction
  simp only [hp, Except.bind] at hOk <;> try contradiction
  cases ptrVal with
  | ptr addr prov =>
    cases prov with
    | none =>
      simp only [sr_ite, sr_throwUB] at hOk <;> try contradiction
      split at hOk <;> cases hOk
    | some id =>
      simp only [sr_pure, Except.bind, sr_bind, sr_get] at hOk <;> try contradiction
      rcases hl : s.memory.lookup id with _ | alloc
      · simp only [hl, sr_throwUB, Except.bind] at hOk <;> cases hOk
      have hid : alloc.id = id := Memory.lookup_id hl
      subst hid
      simp only [hl, sr_pure, Except.bind, sr_bind, sr_ite, sr_throwUB] at hOk <;> try contradiction
      split at hOk
      · first | cases hOk | exact hOk.elim
      rename_i hBase
      try simp only [sr_pure, Except.bind, sr_bind, sr_ite, sr_throwUB] at hOk <;> try contradiction
      split at hOk
      · first | cases hOk | exact hOk.elim
      rename_i hAlive
      try simp only [sr_pure, Except.bind] at hOk <;> try contradiction
      rcases hPerm : s.permissions.get alloc.id with _ | perm
      · simp only [hPerm, sr_throwUB] at hOk <;> cases hOk
      simp only [hPerm, sr_ite, sr_throwUB, sr_set] at hOk <;> try contradiction
      split at hOk
      · first | cases hOk | exact hOk.elim
      rename_i hND
      have hCD : perm.canDealloc = true := by
        revert hND; cases perm.canDealloc <;> simp
      rw [Except.ok.injEq, Prod.mk.injEq] at hOk <;> try contradiction
      obtain ⟨-, hOk⟩ := hOk
      have hMem : alloc ∈ s.memory.allocations := Memory.lookup_mem hl
      refine ⟨addr, alloc, perm, rfl, hl, by simpa using hAlive, by simp at hBase; exact hBase.symm,
        hPerm, hCD, hOk.symm, ?_, ?_, ?_⟩
      · rw [← hOk]
        first
        | have := List.mem_map_of_mem
            (fun a => if a.id == alloc.id then { a with alive := false } else a) hMem
          simpa using this
        | have := List.mem_map_of_mem (f := fun (a : Allocation) =>
            if a.id == alloc.id then { a with alive := false } else a) hMem
          simpa using this
      · rw [← hOk]
        simp [clearPermissionAt, PermissionMap.get]
      · rw [← hOk]
        simp [clearRefCountAt]
  | nullPtr => simp only [sr_throwUB] at hOk <;> cases hOk
  | _ => simp only [sr_throwTE] at hOk <;> cases hOk

set_option maxHeartbeats 4000000 in
/-- Dealloc lifecycle, double-free half (B2): after a successful `semDealloc`,
    running `semDealloc` again through the same pointer is UB — the first run
    marked the allocation the pointer was derived from dead, and the second
    names the SAME allocation (by provenance) and finds it dead. No hypothesis
    on the other allocations is needed: before provenance this theorem had to
    assume live allocations have pairwise-distinct bases, because a free by
    base address could land on a zero-size neighbour sharing the base. -/
theorem semDealloc_twice_is_ub (ptrId : ValueId) (s s1 : MachineState)
    (hOk : Sem.run (semDealloc ptrId) s = .ok ((), s1)) :
    Sem.run (semDealloc ptrId) s1 =
      .error (.ub "Dealloc: allocation is already dead (double free)") := by
  obtain ⟨addr, alloc, _, hp, hl, _, hBase, -, -, hs1, -, -, -⟩ :=
    semDealloc_marks_dead ptrId s s1 hOk
  have hp1 : s1.lookupValue ptrId = some (.ptr addr (some alloc.id)) := by
    rw [hs1]; exact hp
  have hl1 : s1.memory.lookup alloc.id = some { alloc with alive := false } := by
    rw [hs1]
    simp only [Memory.lookup]
    rw [find?_map_alloc]
    have hl' : s.memory.allocations.find? (fun a => a.id == alloc.id) = some alloc := hl
    have hcongr : (fun a : Allocation =>
        (if a.id == alloc.id then { a with alive := false } else a).id == alloc.id)
        = (fun a => a.id == alloc.id) := by
      funext a
      by_cases h : (a.id == alloc.id) = true <;> simp [h]
    rw [hcongr, hl']
    simp
  have hB : (addr != alloc.base) = false := by simp [hBase]
  unfold semDealloc
  simp only [Sem.run, sr_bind, sr_lookup, hp1, Except.bind, sr_pure, sr_get, hl1, sr_ite,
    hB, Bool.false_eq_true, if_false, sr_throwUB]
  rfl

-- =================================================================
-- Non-aliasing at program level
-- =================================================================

/-- Two allocations from different alloca calls never overlap. -/
theorem distinct_alloca_non_aliasing (s : MachineState)
    (hWf : well_formed_memory s) :
    forall a1 a2 : Allocation,
      a1 ∈ s.memory.allocations -> a2 ∈ s.memory.allocations ->
      a1.alive -> a2.alive -> a1.id != a2.id ->
      a1.base + a1.size <= a2.base \/ a2.base + a2.size <= a1.base := by
  exact hWf.2.1

-- =================================================================
-- Permission safety at program level
-- =================================================================

/-- A well-formed state with Owned permission allows both load and store. -/
theorem owned_allows_load_store (allocId : AllocId) (s : MachineState)
    (_hPerm : s.permissions.get allocId = some Permission.owned) :
    Permission.canRead Permission.owned = true /\
    Permission.canWrite Permission.owned = true := by
  simp [Permission.canRead, Permission.canWrite]

/-- A SharedBorrow permission allows load but not store. -/
theorem shared_borrow_allows_load_only (allocId : AllocId) (n : Nat)
    (s : MachineState)
    (_hPerm : s.permissions.get allocId = some (Permission.sharedBorrow n)) :
    Permission.canRead (Permission.sharedBorrow n) = true /\
    Permission.canWrite (Permission.sharedBorrow n) = false := by
  simp [Permission.canRead, Permission.canWrite]

-- =================================================================
-- Heap lifetime: double free / use-after-free / ARC underflow are UB
-- =================================================================

/-!
These theorems ratify the memory-lifetime UB rules of
docs/ub-numerics-policy.md §6 against the executable Lean semantics: a
freed allocation is terminally dead — re-freeing it, accessing it, or
touching its refcount is `SemError.ub`. The statements pin the error
*constructor* (`.ub`), not the diagnostic string, mirroring the stable
error codes locked by `ExecutableFixtures.lean`
(`dealloc_twice_ub_code_stable`, `load_after_dealloc_ub_code_stable`,
`release_after_last_release_ub_code_stable`) and by the Rust reference
interpreter tests (`use_after_dealloc_reports_undefined_behavior_code`
in interpret.rs; the heap-lifetime tests in
crates/trust-ir-build/tests/b2_heapalloc.rs).
-/

/-- Double free is UB, concrete-program instance: allocate, dealloc, dealloc
    again — the second `semDealloc` finds no live allocation at the base
    address and raises undefined behavior. (The general inversion form is
    `semDealloc_twice_is_ub` above; this `rfl` instance is the executable
    witness the policy doc cites alongside the interpreter tests.) -/
theorem semDealloc_twice_is_ub_example :
    ∃ msg,
      Sem.run (do
          let p ← semAlloca .I32 none
          semDealloc p
          semDealloc p)
        MachineState.empty = .error (.ub msg) :=
  ⟨_, rfl⟩

/-- Use-after-free is UB: a `Load` from a deallocated allocation fails the
    liveness (`alive`) bounds check and raises undefined behavior. -/
theorem semLoad_after_dealloc_is_ub :
    ∃ msg,
      Sem.run (do
          let p ← semAlloca .I32 none
          semDealloc p
          let _ ← semLoad .I32 p
          pure ())
        MachineState.empty = .error (.ub msg) :=
  ⟨_, rfl⟩

/-- A live ARC allocation holding its last reference, as set up by the
    Swift-side runtime: `arcRef` permission and refcount 1. -/
private def arcLastRefProgramState : MachineState :=
  let (addr, mem) := Memory.empty.alloc 4 4 heapUsableSlack .swiftHeap
  { MachineState.empty with
    memory      := mem
    permissions := PermissionMap.empty.set (AllocId.mk 0) .arcRef
    refCounts   := setRefCount RefCountMap.empty (AllocId.mk 0) 1
    locals      := ValueMap.empty.set (ValueId.mk 0) (.ptr addr (some (AllocId.mk 0)))
    nextValueId := 1 }

/-- ARC refcount underflow (the ARC double free) is UB: the `Release` that
    drops the last reference frees the allocation, and a second `Release`
    finds no live allocation — matching the interpreter's
    "Release: reference count underflow (double free)" / freed-allocation
    checks. -/
theorem semRelease_after_last_release_is_ub :
    ∃ msg,
      Sem.run (do
          semRelease (ValueId.mk 0)
          semRelease (ValueId.mk 0))
        arcLastRefProgramState = .error (.ub msg) :=
  ⟨_, rfl⟩

/-- Positive control for the lifetime theorems: the first dealloc of a live
    owned allocation is NOT an error (so the UB above is caused by the
    second free, not by a defect in the setup). -/
theorem semDealloc_once_ok :
    ∃ post,
      Sem.run (do
          let p ← semAlloca .I32 none
          semDealloc p)
        MachineState.empty = .ok ((), post) :=
  ⟨_, rfl⟩

-- =================================================================
-- A reference-counted cell is released by `Release`, never by `Dealloc`
-- =================================================================

/-!
The one meaning of `Dealloc` on a reference-counted cell, shared by the
reference interpreter, this model and the Clean backend-TV heap fragment
(docs/SPEC_RATIFICATIONS.md, "A reference-counted cell is released by
`Release`, never by `Dealloc`"). `semHeapAlloc` gives a `SwiftHeap` /
`CleanHeap` cell the `arcRef` permission with refcount 1, and
`Permission.canDealloc .arcRef = false` (`arcRef_forbids_dealloc`), so
`semDealloc` of such a cell is undefined behaviour. The cell is released by
the `semRelease` that takes its count to zero (`deallocARC`). No semantics
changes here: these theorems state what the model already executes, and the
interpreter's `MemoryState::dealloc` now refuses the same cell (Rust twin:
`dealloc_of_a_reference_counted_cell_is_undefined_behavior` in interpret.rs;
both engines: `release_discipline_agrees_across_engines` in
crates/trust-ir-conformance/tests/lean_exec_differential.rs).
-/

set_option maxHeartbeats 4000000 in
/-- `Dealloc` of ANY live allocation held under the `arcRef` permission —
    every `SwiftHeap` / `CleanHeap` cell `semHeapAlloc` creates — is UB with
    the permission diagnostic: the pointer is derived from the allocation and
    sits at its base, and `Permission.canDealloc .arcRef = false` stops
    `semDealloc` before it marks anything dead. -/
theorem semDealloc_arcRef_is_ub (ptrId : ValueId) (s : MachineState)
    (addr : Addr) (alloc : Allocation)
    (hp : s.lookupValue ptrId = some (.ptr addr (some alloc.id)))
    (hFind : s.memory.lookup alloc.id = some alloc)
    (hBase : alloc.base = addr) (hAlive : alloc.alive = true)
    (hPerm : s.permissions.get alloc.id = some .arcRef) :
    Sem.run (semDealloc ptrId) s =
      .error (.ub "Dealloc: permission does not allow deallocation") := by
  have hB : (addr != alloc.base) = false := by simp [hBase]
  have hA : (!alloc.alive) = false := by simp [hAlive]
  unfold semDealloc
  simp only [Sem.run, sr_bind, sr_lookup, hp, Except.bind, sr_pure, sr_get, hFind, sr_ite,
    hB, hA, Bool.false_eq_true, if_false, hPerm, Permission.canDealloc, sr_throwUB]
  rfl

/-- Concrete instance, `CleanHeap`: allocate a Clean Perceus cell and free
    it with `Dealloc` — undefined behaviour (the interpreter's twin is the
    `clean_backend_tv_certified_heap_body_executes_to_the_certified_value`
    Dealloc twin and the `clean_heap_alloc_dealloc_is_ub_stable` fixture). -/
theorem semDealloc_cleanHeap_is_ub_example :
    Sem.run (do
        let p ← semHeapAlloc .I32 none .CleanHeap
        semDealloc p)
      MachineState.empty =
      .error (.ub "Dealloc: permission does not allow deallocation") :=
  rfl

/-- Concrete instance, `SwiftHeap`: the same rule for the Swift ARC heap. -/
theorem semDealloc_swiftHeap_is_ub_example :
    Sem.run (do
        let p ← semHeapAlloc .I32 none .SwiftHeap
        semDealloc p)
      MachineState.empty =
      .error (.ub "Dealloc: permission does not allow deallocation") :=
  rfl

/-- The positive twin, the SCALAR analogue of the shape a
    `clean_backend_tv` heap certificate certifies: allocate a `CleanHeap`
    `I32` cell, store 7, load it back, and release the cell with `Release`
    (count 1 → 0, which frees it). The run succeeds with the loaded value.
    It is one concrete example, not a theorem over Fragment-4 bodies, and it
    is not their shape: a Fragment-4 cell is aggregate-typed (a struct or
    array). Actual decoded execution now uses source-owned aggregate layouts,
    checked by `aggregate_reference_counted_cells_agree_across_engines` in
    crates/trust-ir-conformance/tests/lean_exec_differential.rs. This theorem
    still concerns the bare scalar helpers and this one concrete example. -/
theorem semRelease_cleanHeap_after_store_load_ok_example :
    (match Sem.run (do
        let p ← semHeapAlloc .I32 none .CleanHeap
        let c ← Sem.bindFresh (.int 32 7)
        semStore .I32 p c
        let r ← semLoad .I32 p
        semRelease p
        Sem.lookupValue r) MachineState.empty with
      | .ok (v, _) => some v
      | .error _ => none) = some (.int 32 7) :=
  rfl

-- =================================================================
-- An ARC operation counts only a reference-counted cell
-- =================================================================

/-!
The one meaning of `Retain` / `Release` / `IsUnique` on an allocation that
is not reference-counted (docs/SPEC_RATIFICATIONS.md, "An ARC operation
counts only a reference-counted cell"): undefined behaviour. Each of the
three resolves its operand to the allocation it was DERIVED from — its
provenance, which must be known and live (`getAllocIdFromPtrARC`) — and then
requires the `arcRef` permission of that allocation (`requireArcRef`).

What is proved here, and what is not:
* `requireArcRef_non_arcRef_is_ub` and the three general theorems are stated
  for the live provenance allocation with a permission OTHER than `arcRef`
  (including none), at any offset.
* That every non-reference-counted allocation holds such a permission is NOT
  a theorem. It follows from reading the allocation sites: `semAlloca`,
  `semGlobalAddr`, its module-context twin `semGlobalAddrWithCtx` and the
  `SeqMap` element cell (both in `Semantics/Eval.lean`) grant `owned`, and
  `semHeapAlloc` grants `arcRef` only when `AllocOrigin.isRefCounted`
  (`SwiftHeap` / `CleanHeap`) and `owned` otherwise. The four concrete
  instances below witness it once per non-reference-counted region.
* `retain_one_past_rustHeap_is_ub_and_spares_neighbour` decides the
  one-past-the-end shape whose provenance is not reference-counted: UB, at
  the allocation the pointer was derived from. An RC cell reached at a
  nonzero offset is UB too, by the object-base rule (SPEC clause 3,
  `semRetain_interior_is_ub` and its twins below).

No semantics changes here: these theorems state what the model already
executes. The interpreter's `arc_allocation_mut` / `is_unique` now refuse the
same allocations by their recorded origin (Rust twin:
`arc_operation_on_a_non_reference_counted_allocation_is_undefined_behavior`
in interpret.rs; both engines: `release_discipline_agrees_across_engines`
and `arc_on_a_global_reservation_agrees_across_engines` in
crates/trust-ir-conformance/tests/lean_exec_differential.rs).
-/

/-- `requireArcRef` refuses every permission state other than `arcRef` —
    `owned`, `uniqueBorrow`, `sharedBorrow n`, `rawPtr`, or no permission at
    all — as undefined behaviour. -/
theorem requireArcRef_non_arcRef_is_ub (allocId : AllocId) (s : MachineState)
    (hPerm : s.permissions.get allocId ≠ some .arcRef) :
    ∃ msg, Sem.run (requireArcRef allocId) s = .error (.ub msg) := by
  unfold requireArcRef
  simp only [Sem.run, sr_bind, sr_get, Except.bind]
  cases h : s.permissions.get allocId with
  | none => exact ⟨_, by simp only [sr_throwUB]; rfl⟩
  | some p =>
    cases p with
    | arcRef => exact absurd h hPerm
    | _ => exact ⟨_, by simp only [sr_throwUB]; rfl⟩

/-- The ARC operand lookup of a pointer derived from a live allocation
    returns that allocation, at any offset, and leaves the state unchanged. -/
private theorem getAllocIdFromPtrARC_found (s : MachineState) (addr : Addr) (id : AllocId)
    (alloc : Allocation) (hFind : s.memory.lookup id = some alloc)
    (hAlive : alloc.alive = true) :
    StateT.run (getAllocIdFromPtrARC (.ptr addr (some id))) s = .ok (id, s) := by
  trustIrCompilerProof {
  unfold getAllocIdFromPtrARC
  simp only [sr_bind, sr_get, Except.bind, hFind, hAlive, if_true, sr_pure]
  } {
  dsimp only [getAllocIdFromPtrARC, Sem.getState, StateT.run, Bind.bind,
    StateT.bind, StateT.get, Except.bind, Pure.pure, StateT.pure, Except.pure]
  rw [hFind]
  simp only [hAlive, if_true] <;> rfl
  }

/-- `Retain` through a pointer derived from a live allocation whose permission
    is not `arcRef` is undefined behaviour. -/
theorem semRetain_non_arcRef_is_ub (ptrId : ValueId) (s : MachineState)
    (addr : Addr) (id : AllocId) (alloc : Allocation)
    (hp : s.lookupValue ptrId = some (.ptr addr (some id)))
    (hFind : s.memory.lookup id = some alloc) (hAlive : alloc.alive = true)
    (hPerm : s.permissions.get id ≠ some .arcRef) :
    ∃ msg, Sem.run (semRetain ptrId) s = .error (.ub msg) := by
  obtain ⟨msg, hmsg⟩ := requireArcRef_non_arcRef_is_ub id s hPerm
  simp only [Sem.run] at hmsg
  refine ⟨msg, ?_⟩
  unfold semRetain
  simp only [Sem.run, sr_bind, sr_lookup, hp, Except.bind,
    getAllocIdFromPtrARC_found s addr id alloc hFind hAlive, hmsg]

/-- `Release` through a pointer derived from a live allocation whose
    permission is not `arcRef` is undefined behaviour: it neither decrements
    nor frees. -/
theorem semRelease_non_arcRef_is_ub (ptrId : ValueId) (s : MachineState)
    (addr : Addr) (id : AllocId) (alloc : Allocation)
    (hp : s.lookupValue ptrId = some (.ptr addr (some id)))
    (hFind : s.memory.lookup id = some alloc) (hAlive : alloc.alive = true)
    (hPerm : s.permissions.get id ≠ some .arcRef) :
    ∃ msg, Sem.run (semRelease ptrId) s = .error (.ub msg) := by
  obtain ⟨msg, hmsg⟩ := requireArcRef_non_arcRef_is_ub id s hPerm
  simp only [Sem.run] at hmsg
  refine ⟨msg, ?_⟩
  unfold semRelease
  simp only [Sem.run, sr_bind, sr_lookup, hp, Except.bind,
    getAllocIdFromPtrARC_found s addr id alloc hFind hAlive, hmsg]

/-- `IsUnique` through a pointer derived from a live allocation whose
    permission is not `arcRef` is undefined behaviour: it answers nothing. -/
theorem semIsUnique_non_arcRef_is_ub (ptrId : ValueId) (s : MachineState)
    (addr : Addr) (id : AllocId) (alloc : Allocation)
    (hp : s.lookupValue ptrId = some (.ptr addr (some id)))
    (hFind : s.memory.lookup id = some alloc) (hAlive : alloc.alive = true)
    (hPerm : s.permissions.get id ≠ some .arcRef) :
    ∃ msg, Sem.run (semIsUnique ptrId) s = .error (.ub msg) := by
  obtain ⟨msg, hmsg⟩ := requireArcRef_non_arcRef_is_ub id s hPerm
  simp only [Sem.run] at hmsg
  refine ⟨msg, ?_⟩
  unfold semIsUnique
  simp only [Sem.run, sr_bind, sr_lookup, hp, Except.bind,
    getAllocIdFromPtrARC_found s addr id alloc hFind hAlive, hmsg]

/-- Concrete instance, a stack `Alloca`: `Retain` of the slot is UB (the
    diagnostic names the `owned` permission `semAlloca` grants; the statement
    pins the `.ub` constructor, as the lifetime theorems above do). -/
theorem semRetain_alloca_is_ub_example :
    ∃ msg,
      Sem.run (do
          let p ← semAlloca .I32 none
          semRetain p)
        MachineState.empty = .error (.ub msg) :=
  ⟨_, rfl⟩

/-- Concrete instance, a `RustHeap` cell: `Release` of it is UB (it is freed by
    its allocator's free, which the format spells as a call). -/
theorem semRelease_rustHeap_is_ub_example :
    ∃ msg,
      Sem.run (do
          let p ← semHeapAlloc .I32 none .RustHeap
          semRelease p)
        MachineState.empty = .error (.ub msg) :=
  ⟨_, rfl⟩

/-- Concrete instance, a `CMalloc` cell: `IsUnique` of it is UB. -/
theorem semIsUnique_cMalloc_is_ub_example :
    ∃ msg,
      Sem.run (do
          let p ← semHeapAlloc .I32 none .CMalloc
          semIsUnique p)
        MachineState.empty = .error (.ub msg) :=
  ⟨_, rfl⟩

/-- Concrete instance, a global's reservation: `Retain` of the address
    `semGlobalAddr` reserves is UB. -/
theorem semRetain_globalAddr_is_ub_example :
    ∃ msg,
      Sem.run (do
          let g ← semGlobalAddr ⟨0⟩
          semRetain g)
        MachineState.empty = .error (.ub msg) :=
  ⟨_, rfl⟩

-- Closed kernel reduction includes the full machine record. Use the
-- same scoped budget as adjacent ground memory witnesses.
set_option maxHeartbeats 4000000 in
/-- The one-past-the-end ARC operand whose PROVENANCE is not reference-counted
    is UB, and spares the cell after it (decided: SPEC "A pointer operand
    names the allocation it was derived from" with "An ARC operation counts
    only a reference-counted cell"). A `RustHeap` `I32` cell `a` followed by
    a `CleanHeap` `I32` cell `b`: `Retain` through `gep i32 a [1]` names `a` —
    the pointer it was derived from — whose `owned` permission
    `requireArcRef` refuses. It never reaches `b`, whose count stays 1. The
    reference interpreter refuses the same operand as "not a
    reference-counted cell"; the cell `RustHeapThenCleanHeap` of
    `arc_operand_provenance_agrees_across_engines` in
    crates/trust-ir-conformance/tests/lean_exec_differential.rs. Before Lean
    had provenance it resolved the operand by address to `b` and counted it
    (1 → 2): the replaced theorem `retain_one_past_rustHeap_counts_neighbour`. -/
theorem retain_one_past_rustHeap_is_ub_and_spares_neighbour :
    (∃ msg, Sem.run (do
        let a ← semHeapAlloc .I32 none .RustHeap
        let _b ← semHeapAlloc .I32 none .CleanHeap
        let one ← Sem.bindFresh (.int 64 1)
        let q ← semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 a [one]
        semRetain q) MachineState.empty = .error (.ub msg)) ∧
    (match Sem.run (do
        let a ← semHeapAlloc .I32 none .RustHeap
        let _b ← semHeapAlloc .I32 none .CleanHeap
        let one ← Sem.bindFresh (.int 64 1)
        let q ← semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 a [one]
        Sem.lookupValue q) MachineState.empty with
      | .ok (v, post) => some (v, getRefCount post.refCounts (AllocId.mk 1))
      | .error _ => none) = some (.ptr 1028 (some (AllocId.mk 0)), 1) :=
  ⟨⟨_, by
      simp only [semGEPUsing, semGEPValuesUsing, pure_bind, bind_assoc]
      rfl⟩, by
    simp only [semGEPUsing, semGEPValuesUsing, pure_bind, bind_assoc]
    rfl⟩

-- =================================================================
-- An ARC operand names its cell's object base (clause 3)
-- =================================================================

/-!
SPEC "An ARC operation counts only a reference-counted cell", clause 3,
decided 2026-09-30: `Retain` / `Release` / `IsUnique` are defined only
through a pointer at offset 0 of the reference-counted cell it was derived
from — the object base the pinned runtime reads its header at
(`requireObjectBase`, after `requireArcRef`). Any other offset is undefined
behaviour, on the instruction path and the host path alike (the
interpreter's `InterpretPointer::is_object_base`). The general theorems are
stated for every state; the instances are the shapes the shrink-only ledger
`arc_operand_offset_shapes_stay_as_measured` held before this ruling, which
both engines counted (now `arc_operand_provenance_agrees_across_engines`).
-/

/-- `requireArcRef` of an `arcRef` allocation passes and changes nothing. -/
private theorem requireArcRef_arcRef_ok (s : MachineState) (id : AllocId)
    (hPerm : s.permissions.get id = some .arcRef) :
    StateT.run (requireArcRef id) s = .ok ((), s) := by
  unfold requireArcRef
  simp only [sr_bind, sr_get, Except.bind, hPerm, sr_pure]

/-- The object-base check of a pointer at an address other than its cell's
    base is undefined behaviour. -/
theorem requireObjectBase_off_base_is_ub (op : String) (s : MachineState) (addr : Addr)
    (p : Option AllocId) (id : AllocId) (alloc : Allocation)
    (hFind : s.memory.lookup id = some alloc) (hOff : addr ≠ alloc.base) :
    ∃ msg, StateT.run (requireObjectBase op (.ptr addr p) id) s = .error (.ub msg) := by
  have hb : (addr == alloc.base) = false := by simpa using hOff
  unfold requireObjectBase
  simp only [sr_bind, sr_get, Except.bind, hFind, sr_ite, hb, Bool.false_eq_true, if_false,
    sr_throwUB]
  exact ⟨_, rfl⟩

/-- **`Retain` off its cell's object base is undefined behaviour**, for every
    state: through a pointer derived from a live `arcRef` cell at any address
    but the cell's base, `Retain` faults before it counts anything. -/
theorem semRetain_interior_is_ub (ptrId : ValueId) (s : MachineState)
    (addr : Addr) (id : AllocId) (alloc : Allocation)
    (hp : s.lookupValue ptrId = some (.ptr addr (some id)))
    (hFind : s.memory.lookup id = some alloc) (hAlive : alloc.alive = true)
    (hPerm : s.permissions.get id = some .arcRef) (hOff : addr ≠ alloc.base) :
    ∃ msg, Sem.run (semRetain ptrId) s = .error (.ub msg) := by
  obtain ⟨msg, hmsg⟩ := requireObjectBase_off_base_is_ub "Retain" s addr (some id) id alloc
    hFind hOff
  refine ⟨msg, ?_⟩
  unfold semRetain
  simp only [Sem.run, sr_bind, sr_lookup, hp, Except.bind,
    getAllocIdFromPtrARC_found s addr id alloc hFind hAlive,
    requireArcRef_arcRef_ok s id hPerm, hmsg]

/-- **`Release` off its cell's object base is undefined behaviour**: it
    neither decrements nor frees. -/
theorem semRelease_interior_is_ub (ptrId : ValueId) (s : MachineState)
    (addr : Addr) (id : AllocId) (alloc : Allocation)
    (hp : s.lookupValue ptrId = some (.ptr addr (some id)))
    (hFind : s.memory.lookup id = some alloc) (hAlive : alloc.alive = true)
    (hPerm : s.permissions.get id = some .arcRef) (hOff : addr ≠ alloc.base) :
    ∃ msg, Sem.run (semRelease ptrId) s = .error (.ub msg) := by
  obtain ⟨msg, hmsg⟩ := requireObjectBase_off_base_is_ub "Release" s addr (some id) id alloc
    hFind hOff
  refine ⟨msg, ?_⟩
  unfold semRelease
  simp only [Sem.run, sr_bind, sr_lookup, hp, Except.bind,
    getAllocIdFromPtrARC_found s addr id alloc hFind hAlive,
    requireArcRef_arcRef_ok s id hPerm, hmsg]

/-- **`IsUnique` off its cell's object base is undefined behaviour**: it
    answers nothing. -/
theorem semIsUnique_interior_is_ub (ptrId : ValueId) (s : MachineState)
    (addr : Addr) (id : AllocId) (alloc : Allocation)
    (hp : s.lookupValue ptrId = some (.ptr addr (some id)))
    (hFind : s.memory.lookup id = some alloc) (hAlive : alloc.alive = true)
    (hPerm : s.permissions.get id = some .arcRef) (hOff : addr ≠ alloc.base) :
    ∃ msg, Sem.run (semIsUnique ptrId) s = .error (.ub msg) := by
  obtain ⟨msg, hmsg⟩ := requireObjectBase_off_base_is_ub "IsUnique" s addr (some id) id alloc
    hFind hOff
  refine ⟨msg, ?_⟩
  unfold semIsUnique
  simp only [Sem.run, sr_bind, sr_lookup, hp, Except.bind,
    getAllocIdFromPtrARC_found s addr id alloc hFind hAlive,
    requireArcRef_arcRef_ok s id hPerm, hmsg]

/-- Instance, the interior pointer (the ledger's former control
    `InteriorControl`): `Retain` through `gep i32 a [1]` of a `CleanHeap` `I64`
    cell, four bytes inside it, is undefined behaviour naming the offset. -/
theorem retain_interior_of_cleanHeap_is_ub :
    Sem.run (do
        let a ← semHeapAlloc .I64 none .CleanHeap
        let one ← Sem.bindFresh (.int 64 1)
        let q ← semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 a [one]
        semRetain q) MachineState.empty =
      .error (.ub "Retain: pointer is at offset 4 of its cell, not at the object base a runtime object pointer names") := by
  trustIrReduce

/-- Instance, one past the end (`LoneCleanHeap`): `Release` through
    `gep i32 a [1]` of a `CleanHeap` `I32` cell is undefined behaviour. -/
theorem release_one_past_cleanHeap_is_ub :
    ∃ msg, Sem.run (do
        let a ← semHeapAlloc .I32 none .CleanHeap
        let one ← Sem.bindFresh (.int 64 1)
        let q ← semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 a [one]
        semRelease q) MachineState.empty = .error (.ub msg) :=
  ⟨_, rfl⟩

-- Share the two checked allocation transitions before reducing the ARC
-- witness. This retains the ordinary reduction budget as memory gains
-- additional state that every allocation must preserve.
private def cleanI32Allocation (before : MachineState) : ValueId × MachineState :=
  let id : AllocId := ⟨before.memory.nextAllocId⟩
  let (address, memory) := before.memory.alloc 4 4 heapUsableSlack .cleanHeap
  let allocated : MachineState :=
    { before with
      memory := memory
      permissions := before.permissions.set id .arcRef
      refCounts := fun key => if key == id then some 1 else before.refCounts key }
  allocated.bindValue (.ptr address (some id))

private theorem cleanI32Allocation_empty :
    StateT.run (semHeapAlloc .I32 none .CleanHeap) MachineState.empty =
      .ok (cleanI32Allocation MachineState.empty) := rfl

private theorem cleanI32Allocation_second :
    StateT.run (semHeapAlloc .I32 none .CleanHeap) (cleanI32Allocation MachineState.empty).2 =
      .ok (cleanI32Allocation (cleanI32Allocation MachineState.empty).2) := rfl

/-- Instance, past the heap slack tail (`RetainPastSlackOfRcCell`, probe
    p19): two `CleanHeap` `I32` cells `a`, `b`; `IsUnique` through
    `gep i32 a [5]`, twenty bytes past `a`'s base — `b`'s base in the
    reference placement — is undefined behaviour at `a`, never an answer
    about `b`. -/
theorem isUnique_past_slack_of_cleanHeap_is_ub :
    ∃ msg, Sem.run (do
        let a ← semHeapAlloc .I32 none .CleanHeap
        let _b ← semHeapAlloc .I32 none .CleanHeap
        let five ← Sem.bindFresh (.int 64 5)
        let q ← semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 a [five]
        semIsUnique q) MachineState.empty = .error (.ub msg) :=
  ⟨_, by
    simp only [Sem.run, sr_bind, cleanI32Allocation_empty, cleanI32Allocation_second,
      sr_bindFresh, Except.bind]
    simp only [semGEPUsing, semGEPValuesUsing, pure_bind, bind_assoc]
    rfl⟩

/-- The positive twin: the same three operations at the cell's base run
    (count 1 → 2 → unique? no → 1 → unique). -/
theorem arc_at_object_base_ok_example :
    (match Sem.run (do
        let a ← semHeapAlloc .I32 none .CleanHeap
        semRetain a
        let u ← semIsUnique a
        semRelease a
        let u' ← semIsUnique a
        let x ← Sem.lookupValue u
        let y ← Sem.lookupValue u'
        pure (x, y)) MachineState.empty with
      | .ok (r, _) => some r
      | .error _ => none) = some (.bool false, .bool true) :=
  rfl

-- =================================================================
-- Freeing an allocation under a live borrow
-- =================================================================

/-!
The one meaning of `Dealloc` of an allocation under a live borrow
(docs/SPEC_RATIFICATIONS.md, "Freeing an allocation under a live borrow is
undefined behaviour"): undefined behaviour. `semBorrow` / `semBorrowMut` move
the allocation the operand was DERIVED from — while the operand lies inside
the bytes that live allocation requested (`Memory.borrowTarget`) — from
`owned` to `sharedBorrow n` / `uniqueBorrow`, `semEndBorrow` moves it back by
the same rule, and `semDealloc` refuses both borrow states
(`Permission.canDealloc`).

What is proved here, and what is not:
* `semDealloc_borrowed_is_ub` is stated for the allocation the freed pointer
  was derived from, at its base, whose permission is a borrow state.
* `semBorrow_frame` / `semBorrowMut_frame` / `semEndBorrow_frame` state, for
  every state, that only the operand's `borrowTarget` allocation's
  permission moves; `semBorrow_outside_requested_is_identity` and
  `semEndBorrow_outside_requested_is_noop` that an operand outside the
  requested bytes moves nothing.
* `borrow_one_past_moves_no_permission_and_neighbour_frees` and
  `double_endBorrow_one_past_keeps_neighbour_borrow` decide the first two
  families of the SPEC section's clause 2, in the reference model's
  placement.

No semantics changes here: these theorems state what the model already
executes. The interpreter's `MemoryState::dealloc` now refuses the same free
by a per-allocation live-borrow count (Rust twin:
`dealloc_under_a_live_borrow_is_undefined_behavior` in interpret.rs; both
engines: `borrow_liveness_at_dealloc_agrees_across_engines` in
crates/trust-ir-conformance/tests/lean_exec_differential.rs).
-/

set_option maxHeartbeats 4000000 in
/-- `Dealloc` of a live allocation held under a live borrow — a
    `sharedBorrow n` or `uniqueBorrow` permission, what `semBorrow` /
    `semBorrowMut` leave until the matching `semEndBorrow` — is UB with the
    permission diagnostic: the pointer is derived from the allocation and sits
    at its base, and `Permission.canDealloc` is false for both borrow states,
    so `semDealloc` stops before it marks anything dead. -/
theorem semDealloc_borrowed_is_ub (ptrId : ValueId) (s : MachineState)
    (addr : Addr) (alloc : Allocation) (perm : Permission)
    (hp : s.lookupValue ptrId = some (.ptr addr (some alloc.id)))
    (hFind : s.memory.lookup alloc.id = some alloc)
    (hBase : alloc.base = addr) (hAlive : alloc.alive = true)
    (hPerm : s.permissions.get alloc.id = some perm)
    (hBorrowed : perm = .uniqueBorrow ∨ ∃ n, perm = .sharedBorrow n) :
    Sem.run (semDealloc ptrId) s =
      .error (.ub "Dealloc: permission does not allow deallocation") := by
  have hB : (addr != alloc.base) = false := by simp [hBase]
  have hA : (!alloc.alive) = false := by simp [hAlive]
  rcases hBorrowed with h | ⟨n, h⟩ <;> subst h <;>
  · unfold semDealloc
    simp only [Sem.run, sr_bind, sr_lookup, hp, Except.bind, sr_pure, sr_get, hFind, sr_ite,
      hB, hA, Bool.false_eq_true, if_false, hPerm, Permission.canDealloc, sr_throwUB]
    rfl

/-- Concrete instance, shared: `Alloca`, `Borrow`, then `Dealloc` with the
    borrow live is UB. -/
theorem semDealloc_under_borrow_is_ub_example :
    Sem.run (do
        let p ← semAlloca .I32 none
        let _ ← semBorrow p
        semDealloc p)
      MachineState.empty =
      .error (.ub "Dealloc: permission does not allow deallocation") :=
  rfl

/-- Concrete instance, unique: `Alloca`, `BorrowMut`, then `Dealloc` with it
    live is UB. -/
theorem semDealloc_under_borrowMut_is_ub_example :
    Sem.run (do
        let p ← semAlloca .I32 none
        let _ ← semBorrowMut p
        semDealloc p)
      MachineState.empty =
      .error (.ub "Dealloc: permission does not allow deallocation") :=
  rfl

/-- Concrete instance, interior: a borrow of an interior pointer of an `I64`
    slot (`gep i32 p [1]`, four bytes in) forbids freeing the slot at its
    base. -/
theorem semDealloc_under_interior_borrow_is_ub_example :
    Sem.run (do
        let p ← semAlloca .I64 none
        let one ← Sem.bindFresh (.int 64 1)
        let q ← semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 p [one]
        let _ ← semBorrow q
        semDealloc p)
      MachineState.empty =
      .error (.ub "Dealloc: permission does not allow deallocation") :=
  rfl

/-- Concrete instance: two shared borrows, one ended; the other still
    forbids the free. -/
theorem semDealloc_one_of_two_borrows_live_is_ub_example :
    Sem.run (do
        let p ← semAlloca .I32 none
        let b ← semBorrow p
        let _ ← semBorrow p
        semEndBorrow b
        semDealloc p)
      MachineState.empty =
      .error (.ub "Dealloc: permission does not allow deallocation") :=
  rfl

/-- The positive twin: two shared borrows, both ended, then `Dealloc`
    succeeds. -/
theorem semDealloc_after_every_endBorrow_ok_example :
    (match Sem.run (do
        let p ← semAlloca .I32 none
        let b ← semBorrow p
        let c ← semBorrow p
        semEndBorrow b
        semEndBorrow c
        semDealloc p) MachineState.empty with
      | .ok _ => true
      | .error _ => false) = true :=
  rfl

-- Closed kernel reduction includes the full machine record. Use the
-- same scoped budget as adjacent ground memory witnesses.
set_option maxHeartbeats 4000000 in
/-- Family (a) of the SPEC section's clause 2, decided. After two `I32` slots
    `a`, `b` (placed back to back, `b` at `a + 4`), a `Borrow` of
    `gep i32 a [1]` — one past `a`'s end — names `a`, its provenance, and lies
    outside the bytes `a` requested, so it moves no permission; the free of
    `b` runs. The reference interpreter gives the same verdict
    (`PastEndBorrowFreesNeighbour` of `borrow_operand_provenance_agrees_across_engines`
    in crates/trust-ir-conformance/tests/lean_exec_differential.rs). Before
    Lean had provenance it resolved the operand by address to `b` and refused
    the free: the replaced theorem `borrow_one_past_names_neighbour_dealloc_is_ub`. -/
theorem borrow_one_past_moves_no_permission_and_neighbour_frees :
    (match Sem.run (do
        let a ← semAlloca .I32 none
        let b ← semAlloca .I32 none
        let one ← Sem.bindFresh (.int 64 1)
        let q ← semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 a [one]
        let _ ← semBorrow q
        let pa ← getPermission ⟨0⟩
        let pb ← getPermission ⟨1⟩
        semDealloc b
        pure (pa, pb)) MachineState.empty with
      | .ok (perms, _) => some perms
      | .error _ => none) = some (.owned, .owned) :=
  rfl

set_option maxHeartbeats 4000000 in
/-- Family (b) of the SPEC section's clause 2, decided. With `b` borrowed, a
    borrow of `gep i32 a [1]` names `a` and moves nothing, so ENDING it twice
    ends nothing either: `b`'s own borrow stays live and the free of `b` is
    undefined behaviour. The reference interpreter gives the same verdict
    (`PastEndEndedTwiceNeighbourLive` of
    `borrow_operand_provenance_agrees_across_engines`). Before Lean had
    provenance both ends landed on `b` and the free ran: the replaced theorem
    `double_endBorrow_one_past_ends_neighbour_borrow`. -/
theorem double_endBorrow_one_past_keeps_neighbour_borrow :
    Sem.run (do
        let a ← semAlloca .I32 none
        let b ← semAlloca .I32 none
        let _ ← semBorrow b
        let one ← Sem.bindFresh (.int 64 1)
        let q ← semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 a [one]
        let pp ← semBorrow q
        semEndBorrow pp
        semEndBorrow pp
        semDealloc b) MachineState.empty =
      .error (.ub "Dealloc: permission does not allow deallocation") :=
  by
    simp only [semGEPUsing, semGEPValuesUsing, pure_bind, bind_assoc]
    trustIrReduce

-- =================================================================
-- Provenance: every pointer operand names the allocation it was derived from
-- =================================================================

/-!
The general theorems of SPEC "A pointer operand names the allocation it was
derived from", stated for EVERY state: each instruction that consumes a
pointer moves, reads or frees only the allocation its operand rule names,
never a neighbour (`semAccess_names_provenance` above is the access rule).
The concrete theorems after them are the decided cells of the differential's
provenance tables (`crates/trust-ir-conformance/tests/lean_exec_differential.rs`),
computed in the reference placement (`Memory.alloc`); placement itself is a
property of the two reference models, not a format rule.
-/

theorem PermissionMap.get_set_ne (pm : PermissionMap) (id id' : AllocId) (p : Permission)
    (h : id' ≠ id) : (pm.set id p).get id' = pm.get id' := by
  simp [PermissionMap.set, PermissionMap.get, h]

/-- The borrow operand rule, characterized: it reads the state, changes
    nothing, and answers `endBorrowTarget` of the operand. -/
theorem borrowOperand_ok_inv (op : String) (v : Value) (s s' : MachineState)
    (t : Option AllocId) (h : StateT.run (borrowOperand op v) s = .ok (t, s')) :
    s' = s ∧ t = endBorrowTarget s.memory v := by
  unfold borrowOperand at h
  rw [sr_bind, sr_get] at h
  simp only [Except.bind] at h
  match v, h with
  | .ptr addr (some id), h =>
    rw [sr_pure] at h; cases h; exact ⟨rfl, rfl⟩
  | .ptr addr none, h =>
    rw [sr_ite] at h; split at h <;> cases h
  | .nullPtr, h => cases h
  | .int .., h | .float .., h | .bool .., h | .aggregate .., h | .vector .., h | .frame .., h
  | .set .., h | .sequence .., h | .record .., h | .closure .., h | .typedClosure .., h | .fatPtr .., h
  | .partial .., h | .undef .., h | .uninit, h => cases h

theorem getPermission_ok_inv (id : AllocId) (s s' : MachineState) (p : Permission)
    (h : StateT.run (getPermission id) s = .ok (p, s')) :
    s' = s ∧ s.permissions.get id = some p := by
  unfold getPermission at h
  rw [sr_bind, sr_get] at h
  simp only [Except.bind] at h
  split at h
  · rename_i perm hperm
    rw [sr_pure] at h; cases h; exact ⟨rfl, hperm⟩
  · cases h

theorem sr_setPermission (id : AllocId) (p : Permission) (s : MachineState) :
    StateT.run (setPermission id p) s = .ok ((), { s with permissions := s.permissions.set id p }) :=
  rfl

/-- **`Borrow` moves only its operand's target.** A successful `Borrow`
    changes no memory, no reference count and no global, and no permission
    but that of the allocation its operand names by the borrow operand rule
    (`endBorrowTarget`: a thin provenance pointer inside the live
    allocation's requested bytes) — never a neighbour's. -/
theorem semBorrow_frame (ptrId : ValueId) (s s' : MachineState) (r : ValueId)
    (h : Sem.run (semBorrow ptrId) s = .ok (r, s')) :
    s'.memory = s.memory ∧ s'.refCounts = s.refCounts ∧ s'.globals = s.globals ∧
    ∃ v, s.lookupValue ptrId = some v ∧
      ∀ id, endBorrowTarget s.memory v ≠ some id → s'.permissions.get id = s.permissions.get id := by
  unfold semBorrow at h
  simp only [Sem.run, sr_bind, sr_lookup] at h
  rcases hv : s.lookupValue ptrId with _ | v
  · rw [hv] at h; cases h
  rw [hv] at h
  simp only [Except.bind] at h
  split at h
  · rw [sr_bindFresh] at h
    cases h
    exact ⟨rfl, rfl, rfl, _, rfl, fun _ _ => rfl⟩
  · rw [sr_bind] at h
    rcases hb : StateT.run (borrowOperand "Borrow" v) s with e | ⟨t, s1⟩
    · rw [hb] at h; cases h
    obtain ⟨hs1, ht⟩ := borrowOperand_ok_inv _ _ _ _ _ hb
    subst s1
    rw [hb] at h
    simp only [Except.bind] at h
    split at h
    · rw [sr_bindFresh] at h
      cases h
      exact ⟨rfl, rfl, rfl, _, rfl, fun _ _ => rfl⟩
    · rename_i allocId
      rw [sr_bind] at h
      rcases hg : StateT.run (getPermission allocId) s with e | ⟨perm, s2⟩
      · rw [hg] at h; cases h
      obtain ⟨hs2, -⟩ := getPermission_ok_inv _ _ _ _ hg
      subst s2
      rw [hg] at h
      simp only [Except.bind] at h
      have hframe : ∀ (p : Permission) id, endBorrowTarget s.memory v ≠ some id →
          (s.permissions.set allocId p).get id = s.permissions.get id := by
        intro p id hid
        apply PermissionMap.get_set_ne
        intro heq; subst heq; exact hid ht.symm
      split at h
      · rw [sr_bind, sr_setPermission] at h
        simp only [Except.bind] at h
        rw [sr_bindFresh] at h
        cases h
        exact ⟨rfl, rfl, rfl, _, rfl, hframe _⟩
      · rw [sr_bind, sr_setPermission] at h
        simp only [Except.bind] at h
        rw [sr_bindFresh] at h
        cases h
        exact ⟨rfl, rfl, rfl, _, rfl, hframe _⟩
      · cases h


/-- **`BorrowMut` moves only its operand's target** (as `semBorrow_frame`). -/
theorem semBorrowMut_frame (ptrId : ValueId) (s s' : MachineState) (r : ValueId)
    (h : Sem.run (semBorrowMut ptrId) s = .ok (r, s')) :
    s'.memory = s.memory ∧ s'.refCounts = s.refCounts ∧ s'.globals = s.globals ∧
    ∃ v, s.lookupValue ptrId = some v ∧
      ∀ id, endBorrowTarget s.memory v ≠ some id → s'.permissions.get id = s.permissions.get id := by
  unfold semBorrowMut at h
  simp only [Sem.run, sr_bind, sr_lookup] at h
  rcases hv : s.lookupValue ptrId with _ | v
  · rw [hv] at h; cases h
  rw [hv] at h
  simp only [Except.bind] at h
  split at h
  · rw [sr_bindFresh] at h
    cases h
    exact ⟨rfl, rfl, rfl, _, rfl, fun _ _ => rfl⟩
  · rw [sr_bind] at h
    rcases hb : StateT.run (borrowOperand "Borrow" v) s with e | ⟨t, s1⟩
    · rw [hb] at h; cases h
    obtain ⟨hs1, ht⟩ := borrowOperand_ok_inv _ _ _ _ _ hb
    subst s1
    rw [hb] at h
    simp only [Except.bind] at h
    split at h
    · rw [sr_bindFresh] at h
      cases h
      exact ⟨rfl, rfl, rfl, _, rfl, fun _ _ => rfl⟩
    · rename_i allocId
      rw [sr_bind] at h
      rcases hg : StateT.run (getPermission allocId) s with e | ⟨perm, s2⟩
      · rw [hg] at h; cases h
      obtain ⟨hs2, -⟩ := getPermission_ok_inv _ _ _ _ hg
      subst s2
      rw [hg] at h
      simp only [Except.bind] at h
      split at h
      · rw [sr_bind, sr_setPermission] at h
        simp only [Except.bind] at h
        rw [sr_bindFresh] at h
        cases h
        refine ⟨rfl, rfl, rfl, _, rfl, fun id hid => ?_⟩
        apply PermissionMap.get_set_ne
        intro heq; subst heq; exact hid ht.symm
      · cases h

/-- **`EndBorrow` moves only its operand's target**: no memory, reference
    count, global or SSA value changes, and no permission but that of the
    allocation `endBorrowTarget` names. -/
theorem semEndBorrow_frame (ptrId : ValueId) (s s' : MachineState)
    (h : Sem.run (semEndBorrow ptrId) s = .ok ((), s')) :
    s'.memory = s.memory ∧ s'.refCounts = s.refCounts ∧ s'.globals = s.globals ∧
    s'.locals = s.locals ∧
    ∃ v, s.lookupValue ptrId = some v ∧
      ∀ id, endBorrowTarget s.memory v ≠ some id → s'.permissions.get id = s.permissions.get id := by
  unfold semEndBorrow at h
  simp only [Sem.run, sr_bind, sr_lookup] at h
  rcases hv : s.lookupValue ptrId with _ | v
  · rw [hv] at h; cases h
  rw [hv] at h
  simp only [Except.bind, sr_bind, sr_get] at h
  split at h
  · rw [sr_pure] at h; cases h
    exact ⟨rfl, rfl, rfl, rfl, _, rfl, fun _ _ => rfl⟩
  · rename_i allocId ht
    rw [sr_bind] at h
    rcases hg : StateT.run (getPermission allocId) s with e | ⟨perm, s2⟩
    · rw [hg] at h; cases h
    obtain ⟨hs2, -⟩ := getPermission_ok_inv _ _ _ _ hg
    subst s2
    rw [hg] at h
    simp only [Except.bind] at h
    have hframe : ∀ (p : Permission) id, endBorrowTarget s.memory v ≠ some id →
        (s.permissions.set allocId p).get id = s.permissions.get id := by
      intro p id hid
      apply PermissionMap.get_set_ne
      intro heq; subst heq; exact hid ht
    split at h
    · split at h
      · cases h
      · rw [sr_setPermission] at h; cases h
        exact ⟨rfl, rfl, rfl, rfl, _, rfl, hframe _⟩
      · rw [sr_setPermission] at h; cases h
        exact ⟨rfl, rfl, rfl, rfl, _, rfl, hframe _⟩
    · rw [sr_setPermission] at h; cases h
      exact ⟨rfl, rfl, rfl, rfl, _, rfl, hframe _⟩
    · cases h

/-- A thin provenance pointer outside its allocation's requested bytes — one
    past the end, in the heap slack tail, in a zero-size or freed allocation —
    is passed through by `Borrow`, which moves nothing at all. -/
theorem semBorrow_outside_requested_is_identity (ptrId : ValueId) (s : MachineState)
    (a : Addr) (id : AllocId)
    (hp : s.lookupValue ptrId = some (.ptr a (some id)))
    (hOut : s.memory.borrowTarget a id = none) :
    Sem.run (semBorrow ptrId) s = .ok (s.bindValue (.ptr a (some id))) := by
  unfold semBorrow
  simp only [Sem.run, sr_bind, sr_lookup, hp, Except.bind]
  unfold borrowOperand
  simp only [sr_bind, sr_get, Except.bind, sr_pure, hOut]
  rfl

/-- The `EndBorrow` twin: an operand outside its allocation's requested
    bytes ends nothing and leaves the state exactly as it was. -/
theorem semEndBorrow_outside_requested_is_noop (ptrId : ValueId) (s : MachineState)
    (v : Value) (hp : s.lookupValue ptrId = some v)
    (hOut : endBorrowTarget s.memory v = none) :
    Sem.run (semEndBorrow ptrId) s = .ok ((), s) := by
  unfold semEndBorrow
  simp only [Sem.run, sr_bind, sr_lookup, hp, Except.bind, sr_get, hOut, sr_pure]

/-- The ARC operand rule, characterized: it reads the state, changes
    nothing, and answers the provenance of a pointer whose allocation is
    known and live. -/
theorem getAllocIdFromPtrARC_ok_inv (v : Value) (s s' : MachineState) (id : AllocId)
    (h : StateT.run (getAllocIdFromPtrARC v) s = .ok (id, s')) :
    s' = s ∧ ∃ a alloc, v = .ptr a (some id) ∧ s.memory.lookup id = some alloc ∧
      alloc.alive = true := by
  unfold getAllocIdFromPtrARC at h
  rw [sr_bind, sr_get] at h
  simp only [Except.bind] at h
  match v, h with
  | .ptr addr (some pid), h =>
    simp only [] at h
    rcases hl : s.memory.lookup pid with _ | alloc
    · rw [hl, sr_throwUB] at h; cases h
    · rw [hl] at h
      simp only [] at h
      rw [sr_ite] at h
      split at h
      · rename_i hAlive
        rw [sr_pure] at h; cases h
        exact ⟨rfl, addr, alloc, rfl, hl, hAlive⟩
      · cases h
  | .ptr addr none, h =>
    simp only [] at h
    rw [sr_ite] at h; split at h <;> cases h
  | .nullPtr, h => cases h
  | .int .., h | .float .., h | .bool .., h | .aggregate .., h | .vector .., h | .frame .., h
  | .set .., h | .sequence .., h | .record .., h | .closure .., h | .typedClosure .., h | .fatPtr .., h
  | .partial .., h | .undef .., h | .uninit, h => cases h

theorem requireArcRef_ok_inv (id : AllocId) (s s' : MachineState) (u : Unit)
    (h : StateT.run (requireArcRef id) s = .ok (u, s')) :
    s' = s ∧ s.permissions.get id = some .arcRef := by
  unfold requireArcRef at h
  rw [sr_bind, sr_get] at h
  simp only [Except.bind] at h
  split at h
  · rename_i hp; rw [sr_pure] at h; cases h; exact ⟨rfl, hp⟩
  · cases h
  · cases h

/-- A successful object-base check changed nothing, and its operand is a
    pointer at the base of the allocation it names. -/
theorem requireObjectBase_ok_inv (op : String) (v : Value) (id : AllocId)
    (s s' : MachineState) (u : Unit)
    (h : StateT.run (requireObjectBase op v id) s = .ok (u, s')) :
    s' = s ∧ ∃ addr p alloc, v = .ptr addr p ∧ s.memory.lookup id = some alloc ∧
      addr = alloc.base := by
  unfold requireObjectBase at h
  rw [sr_bind, sr_get] at h
  simp only [Except.bind] at h
  rcases hl : s.memory.lookup id with _ | alloc
  · rw [hl] at h
    cases v <;> cases h
  · rw [hl] at h
    cases v <;> try cases h
    rename_i addr p
    simp only [] at h
    rw [sr_ite] at h
    split at h
    · rename_i hb
      rw [sr_pure] at h; cases h
      exact ⟨rfl, addr, p, alloc, rfl, rfl, by simpa using hb⟩
    · cases h

/-- **`Retain` counts only its provenance.** A successful `Retain` went
    through a pointer derived from a live `arcRef` allocation `id`, and
    changes no memory, permission, SSA value or global, and no reference count
    but `id`'s. -/
theorem semRetain_frame (ptrId : ValueId) (s s' : MachineState)
    (h : Sem.run (semRetain ptrId) s = .ok ((), s')) :
    ∃ a id, s.lookupValue ptrId = some (.ptr a (some id)) ∧
      s'.memory = s.memory ∧ s'.permissions = s.permissions ∧ s'.locals = s.locals ∧
      s'.globals = s.globals ∧ ∀ id', id' ≠ id → s'.refCounts id' = s.refCounts id' := by
  unfold semRetain at h
  simp only [Sem.run, sr_bind, sr_lookup] at h
  rcases hv : s.lookupValue ptrId with _ | v
  · rw [hv] at h; cases h
  rw [hv] at h
  simp only [Except.bind] at h
  rcases hg : StateT.run (getAllocIdFromPtrARC v) s with e | ⟨id, s1⟩
  · rw [hg] at h; cases h
  obtain ⟨hs1, a, alloc, rfl, -, -⟩ := getAllocIdFromPtrARC_ok_inv _ _ _ _ hg
  subst s1
  rw [hg] at h
  simp only [Except.bind] at h
  rcases hr : StateT.run (requireArcRef id) s with e | ⟨u, s2⟩
  · rw [hr] at h; cases h
  obtain ⟨hs2, -⟩ := requireArcRef_ok_inv _ _ _ _ hr
  subst s2
  rw [hr] at h
  simp only [Except.bind] at h
  rcases hb : StateT.run (requireObjectBase _ _ id) s with e | ⟨u', s3⟩
  · rw [hb] at h; cases h
  obtain ⟨hs3, -⟩ := requireObjectBase_ok_inv _ _ _ _ _ _ hb
  subst s3
  rw [hb] at h
  simp only [Except.bind, sr_get, sr_set] at h
  cases h
  refine ⟨a, id, rfl, rfl, rfl, rfl, rfl, fun id' hne => ?_⟩
  simp [setRefCount, hne]

/-- **`IsUnique` reads only its provenance**: it changes no memory,
    permission, reference count or global. -/
theorem semIsUnique_frame (ptrId : ValueId) (s s' : MachineState) (r : ValueId)
    (h : Sem.run (semIsUnique ptrId) s = .ok (r, s')) :
    ∃ a id, s.lookupValue ptrId = some (.ptr a (some id)) ∧
      s'.memory = s.memory ∧ s'.permissions = s.permissions ∧ s'.refCounts = s.refCounts ∧
      s'.globals = s.globals := by
  unfold semIsUnique at h
  simp only [Sem.run, sr_bind, sr_lookup] at h
  rcases hv : s.lookupValue ptrId with _ | v
  · rw [hv] at h; cases h
  rw [hv] at h
  simp only [Except.bind] at h
  rcases hg : StateT.run (getAllocIdFromPtrARC v) s with e | ⟨id, s1⟩
  · rw [hg] at h; cases h
  obtain ⟨hs1, a, alloc, rfl, -, -⟩ := getAllocIdFromPtrARC_ok_inv _ _ _ _ hg
  subst s1
  rw [hg] at h
  simp only [Except.bind] at h
  rcases hr : StateT.run (requireArcRef id) s with e | ⟨u, s2⟩
  · rw [hr] at h; cases h
  obtain ⟨hs2, -⟩ := requireArcRef_ok_inv _ _ _ _ hr
  subst s2
  rw [hr] at h
  simp only [Except.bind] at h
  rcases hb : StateT.run (requireObjectBase _ _ id) s with e | ⟨u', s3⟩
  · rw [hb] at h; cases h
  obtain ⟨hs3, -⟩ := requireObjectBase_ok_inv _ _ _ _ _ _ hb
  subst s3
  rw [hb] at h
  simp only [Except.bind, sr_get, sr_bindFresh] at h
  cases h
  exact ⟨a, id, rfl, rfl, rfl, rfl, rfl⟩

/-- **`Release` touches only its provenance.** A successful `Release` went
    through a pointer derived from a live `arcRef` allocation `id`; every
    other allocation keeps its record, permission and reference count, the
    bytes and SSA values are unchanged. -/
theorem semRelease_frame (ptrId : ValueId) (s s' : MachineState)
    (h : Sem.run (semRelease ptrId) s = .ok ((), s')) :
    ∃ a id, s.lookupValue ptrId = some (.ptr a (some id)) ∧
      s'.memory.bytes = s.memory.bytes ∧ s'.locals = s.locals ∧ s'.globals = s.globals ∧
      ∀ id', id' ≠ id →
        s'.memory.lookup id' = s.memory.lookup id' ∧
        s'.permissions.get id' = s.permissions.get id' ∧
        s'.refCounts id' = s.refCounts id' := by
  unfold semRelease at h
  simp only [Sem.run, sr_bind, sr_lookup] at h
  rcases hv : s.lookupValue ptrId with _ | v
  · rw [hv] at h; cases h
  rw [hv] at h
  simp only [Except.bind] at h
  rcases hg : StateT.run (getAllocIdFromPtrARC v) s with e | ⟨id, s1⟩
  · rw [hg] at h; cases h
  obtain ⟨hs1, a, alloc, rfl, -, -⟩ := getAllocIdFromPtrARC_ok_inv _ _ _ _ hg
  subst s1
  rw [hg] at h
  simp only [Except.bind] at h
  rcases hr : StateT.run (requireArcRef id) s with e | ⟨u, s2⟩
  · rw [hr] at h; cases h
  obtain ⟨hs2, -⟩ := requireArcRef_ok_inv _ _ _ _ hr
  subst s2
  rw [hr] at h
  simp only [Except.bind] at h
  rcases hb : StateT.run (requireObjectBase _ _ id) s with e | ⟨u', s3⟩
  · rw [hb] at h; cases h
  obtain ⟨hs3, -⟩ := requireObjectBase_ok_inv _ _ _ _ _ _ hb
  subst s3
  rw [hb] at h
  simp only [Except.bind, sr_get] at h
  refine ⟨a, id, rfl, ?_⟩
  revert h
  generalize getRefCount s.refCounts id = count
  intro h
  match count, h with
  | 0, h => cases h
  | 1, h =>
    unfold deallocARC at h
    rw [sr_bind, sr_get] at h
    simp only [Except.bind] at h
    rw [sr_ite] at h
    split at h
    · cases h
    · rw [sr_set] at h; cases h
      refine ⟨rfl, rfl, rfl, fun id' hne => ⟨?_, ?_, ?_⟩⟩
      · simp only [Memory.lookup]
        rw [find?_map_alloc]
        have hcongr : (fun x : Allocation =>
            (if x.id == id then { x with alive := false } else x).id == id')
            = (fun x => x.id == id') := by
          funext x; by_cases hx : (x.id == id) = true <;> simp [hx]
        rw [hcongr]
        cases hf : s.memory.allocations.find? (fun x => x.id == id') with
        | none => rfl
        | some b =>
          have hb := find?_some_pred hf
          simp only [beq_iff_eq] at hb
          have hbid : b.id ≠ id := by rw [hb]; exact hne
          simp [hbid]
      · simp [clearPermission, PermissionMap.get, hne]
      · simp [setRefCount, hne]
  | n + 2, h =>
    rw [sr_set] at h; cases h
    exact ⟨rfl, rfl, rfl, fun id' hne => ⟨rfl, rfl, by simp [setRefCount, hne]⟩⟩

/-- **`Dealloc` frees its provenance, and only it.** A successful `Dealloc`
    names the allocation its pointer was derived from, at that allocation's
    base, marks exactly it dead, and leaves every other allocation's record
    as it was — even one that starts at the same address. -/
theorem semDealloc_frees_its_provenance (ptrId : ValueId) (s s' : MachineState)
    (h : Sem.run (semDealloc ptrId) s = .ok ((), s')) :
    ∃ alloc : Allocation, s.lookupValue ptrId = some (.ptr alloc.base (some alloc.id)) ∧
      s'.memory.lookup alloc.id = some { alloc with alive := false } ∧
      ∀ id', id' ≠ alloc.id → s'.memory.lookup id' = s.memory.lookup id' := by
  obtain ⟨addr, alloc, _, hp, hl, -, hBase, -, -, hs', -, -, -⟩ :=
    semDealloc_marks_dead ptrId s s' h
  subst hBase
  refine ⟨alloc, hp, ?_, fun id' hne => ?_⟩
  · rw [hs']
    simp only [Memory.lookup]
    rw [find?_map_alloc]
    have hcongr : (fun x : Allocation =>
        (if x.id == alloc.id then { x with alive := false } else x).id == alloc.id)
        = (fun x => x.id == alloc.id) := by
      funext x; by_cases hx : (x.id == alloc.id) = true <;> simp [hx]
    rw [hcongr]
    have hl' : s.memory.allocations.find? (fun x => x.id == alloc.id) = some alloc := hl
    rw [hl']
    simp
  · rw [hs']
    simp only [Memory.lookup]
    rw [find?_map_alloc]
    have hcongr : (fun x : Allocation =>
        (if x.id == alloc.id then { x with alive := false } else x).id == id')
        = (fun x => x.id == id') := by
      funext x; by_cases hx : (x.id == alloc.id) = true <;> simp [hx]
    rw [hcongr]
    cases hf : s.memory.allocations.find? (fun x => x.id == id') with
    | none => rfl
    | some b =>
      have hb := find?_some_pred hf
      simp only [beq_iff_eq] at hb
      have hbid : b.id ≠ alloc.id := by rw [hb]; exact hne
      simp [hbid]

/-- **The integer-to-address conversion** (`Sem.addrOfInt`, the
    interpreter's `int.as_unsigned()` + `u64::try_from`): a successful
    conversion is the unsigned value of the integer at its source width, it is
    below 2^64, and the state is untouched. -/
theorem addrOfInt_lt_two_pow_64 (op : String) (w : Nat) (v : Int) (s s' : MachineState)
    (a : Nat) (h : StateT.run (Sem.addrOfInt op w v) s = .ok (a, s')) :
    a = (v % 2 ^ w).toNat ∧ a < 2 ^ 64 ∧ s' = s := by
  unfold Sem.addrOfInt at h
  simp only [] at h
  rw [sr_ite] at h
  split at h
  · rename_i hlt; rw [sr_pure] at h; cases h; exact ⟨rfl, hlt, rfl⟩
  · cases h


-- -----------------------------------------------------------------
-- Concrete instances: the decided cells
-- -----------------------------------------------------------------

-- Name the concrete allocation transitions before reducing the remaining
-- memory operations. This shares their checked execution and keeps the
-- closed witnesses within the ordinary kernel reduction budget.
private def stackAllocationResult (before : MachineState) (size alignment : Nat) :
    ValueId × MachineState :=
  let id := AllocId.mk before.memory.nextAllocId
  let (address, memory) := before.memory.alloc size alignment 0 .rustStack
  let allocated : MachineState :=
    { before with
      memory := memory
      permissions := before.permissions.set id .owned }
  allocated.bindValue (.ptr address (some id))

private theorem alloca32_empty : StateT.run (semAlloca .I32 none) MachineState.empty =
    .ok (stackAllocationResult MachineState.empty 4 4) := rfl
private theorem alloca64_empty : StateT.run (semAlloca .I64 none) MachineState.empty =
    .ok (stackAllocationResult MachineState.empty 8 8) := rfl
private theorem alloca32_second :
    StateT.run (semAlloca .I32 none) (stackAllocationResult MachineState.empty 4 4).2 =
    .ok (stackAllocationResult (stackAllocationResult MachineState.empty 4 4).2 4 4) := rfl

/-- Family (c) of the SPEC borrow section's clause 2, decided: an address
    computed through an integer recovers the allocation of the ONE layout.
    `a = alloca i8`, `b = alloca i32`, `c = alloca i32`; the reference
    placement aligns `b` to 4, so `inttoptr(ptrtoint a + 5)` is address 1029,
    inside `b` = [1028, 1032), and recovers `b`'s provenance — as in the
    interpreter (`IntToPtrAcrossLayouts`). -/
theorem inttoptr_resolves_in_the_one_layout :
    (match Sem.run (do
        let a ← semAlloca .I8 none
        let _b ← semAlloca .I32 none
        let _c ← semAlloca .I32 none
        let ai ← semCast .PtrToInt .Ptr .U64 a
        let five ← Sem.bindFresh (.int 64 5)
        let sum ← semBinOp .Add .U64 ai five
        let q ← semCast .IntToPtr .U64 .Ptr sum
        Sem.lookupValue q) MachineState.empty with
      | .ok (v, _) => some v
      | .error _ => none) = some (.ptr 1029 (some ⟨1⟩)) := by
  trustIrReduce

/-- Family (d) of the SPEC borrow section's clause 2, decided: `Dealloc` of a
    zero-size slot frees THAT slot, not the borrowed allocation placed after
    it. The slot's bump makes the next base differ, and the free is named by
    provenance anyway; `b`'s borrow stays live. -/
theorem dealloc_zero_size_frees_itself :
    (match Sem.run (do
        let z ← semAlloca .Unit none
        let b ← semAlloca .I32 none
        let _ ← semBorrow b
        semDealloc z
        let pb ← getPermission ⟨1⟩
        let s ← Sem.getState
        pure (pb, (s.memory.lookup ⟨0⟩).map (·.alive), (s.memory.lookup ⟨1⟩).map (·.alive)))
        MachineState.empty with
      | .ok (r, _) => some r
      | .error _ => none) = some (.sharedBorrow 1, some false, some true) :=
  rfl

-- Closed kernel reduction includes the full machine record. Use the
-- same scoped budget as adjacent ground memory witnesses.
set_option maxHeartbeats 4000000 in
/-- `Dealloc` of a pointer one past the end of an `i32` slot is UB — it names
    that slot, at an offset other than its base — and never frees the slot
    placed at that address (probe p14). -/
theorem dealloc_one_past_end_is_ub :
    ∃ msg, Sem.run (do
        let a ← semAlloca .I32 none
        let _b ← semAlloca .I32 none
        let one ← Sem.bindFresh (.int 64 1)
        let q ← semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 a [one]
        semDealloc q) MachineState.empty = .error (.ub msg) :=
  ⟨_, by
    simp only [semGEPUsing, semGEPValuesUsing, pure_bind, bind_assoc]
    rfl⟩

set_option maxHeartbeats 4000000 in
/-- An `i32` slot placed after a byte slot is 4-aligned by the reference
    placement, so a store and load with a declared `align 4` succeed (probe
    p04; a packed allocator put it at 1025 and refused the access). -/
theorem aligned_store_after_byte_local_ok :
    (match Sem.run (do
        let _ ← semAlloca .I8 none
        let p ← semAlloca .I32 none
        let seven ← Sem.bindFresh (.int 32 7)
        semStore .I32 p seven false (some 4)
        let r ← semLoad .I32 p false (some 4)
        Sem.lookupValue r) MachineState.empty with
      | .ok (v, _) => some v
      | .error _ => none) = some (.int 32 7) :=
  rfl

set_option maxHeartbeats 4000000 in
/-- A load one past the end of an `i32` slot is UB, even with another slot
    placed right there: the access is checked against the allocation the
    pointer was derived from (probe p02). -/
theorem load_one_past_end_is_ub :
    ∃ msg, Sem.run (do
        let a ← semAlloca .I32 none
        let b ← semAlloca .I32 none
        let seven ← Sem.bindFresh (.int 32 7)
        semStore .I32 b seven
        let one ← Sem.bindFresh (.int 64 1)
        let q ← semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I32 a [one]
        let _ ← semLoad .I32 q
        pure ()) MachineState.empty = .error (.ub msg) :=
  ⟨_, by
    simp only [Sem.run, sr_bind, alloca32_empty, alloca64_empty, alloca32_second, Except.bind]
    simp only [semGEPUsing, semGEPValuesUsing, pure_bind, bind_assoc]
    rfl⟩

/-- An access with no declared alignment checks the type's NATURAL one: an
    `i32` load at `a + 1` of an `i64` slot is UB (cell c04). -/
theorem load_misaligned_without_declared_align_is_ub :
    ∃ msg, Sem.run (do
        let a ← semAlloca .I64 none
        let zero ← Sem.bindFresh (.int 64 0)
        semStore .I64 a zero
        let one ← Sem.bindFresh (.int 64 1)
        let q ← semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I8 a [one]
        let _ ← semLoad .I32 q
        pure ()) MachineState.empty = .error (.ub msg) :=
  ⟨_, by
    simp only [Sem.run, sr_bind, alloca32_empty, alloca64_empty, alloca32_second, Except.bind]
    simp only [semGEPUsing, semGEPValuesUsing, pure_bind, bind_assoc]
    rfl⟩

set_option maxHeartbeats 16000000 in
/-- Pointer arithmetic keeps a no-provenance pointer one: a `GEP` from a
    dangling pointer that lands inside an allocation does not acquire it, and
    a load through it is UB (cell c06). -/
theorem gep_keeps_no_provenance :
    (match Sem.run (do
        let a ← semAlloca .I32 none
        let ai ← semCast .PtrToInt .Ptr .U64 a
        let four ← Sem.bindFresh (.int 64 4)
        let below ← semBinOp .Sub .U64 ai four
        let d ← semCast .IntToPtr .U64 .Ptr below
        let q ← semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I8 d [four]
        Sem.lookupValue q) MachineState.empty with
      | .ok (v, _) => some v
      | .error _ => none) = some (.ptr 1024 none) ∧
    ∃ msg, Sem.run (do
        let a ← semAlloca .I32 none
        let seven ← Sem.bindFresh (.int 32 7)
        semStore .I32 a seven
        let ai ← semCast .PtrToInt .Ptr .U64 a
        let four ← Sem.bindFresh (.int 64 4)
        let below ← semBinOp .Sub .U64 ai four
        let d ← semCast .IntToPtr .U64 .Ptr below
        let q ← semGEPUsing (scalarMemoryLayout .le64) (fun _ => typedIntegerValue .le64 .I64) .I8 d [four]
        let _ ← semLoad .I32 q
        pure ()) MachineState.empty = .error (.ub msg) := by
  constructor
  · trustIrReduce
  · refine ⟨"Load: pointer value 1024 has no allocation provenance", ?_⟩
    simp only [Sem.run, sr_bind]
    trustIrReduce

/-- A negative signed integer becomes a LARGE address, never the null
    pointer: `inttoptr i64 -8` is the no-provenance pointer at 2^64 - 8, and
    `ptrtoint` gives that address back (cell c01). -/
theorem inttoptr_negative_is_dangling_not_null :
    (match Sem.run (do
        let m ← Sem.bindFresh (.int 64 (-8))
        let p ← semCast .IntToPtr .I64 .Ptr m
        Sem.lookupValue p) MachineState.empty with
      | .ok (v, _) => some v
      | .error _ => none) = some (.ptr (2 ^ 64 - 8) none) :=
  rfl


-- =================================================================
-- Fat-pointer trio: Sem-level round trip (B3 depth ledger)
-- =================================================================

/-- SSA ids other than the freshly bound one read through `bindValue`
    unchanged. -/
private theorem lookupValue_bindValue_ne (st : MachineState) (v : Value)
    (id : ValueId) (h : id.index ≠ st.nextValueId) :
    (st.bindValue v).snd.lookupValue id = st.lookupValue id := by
  have hne : (id == ValueId.mk st.nextValueId) = false := by
    first
    | refine (beq_eq_false_iff_ne _ _).mpr ?_
    | refine beq_eq_false_iff_ne.mpr ?_
    intro hEq
    exact h (congrArg ValueId.index hEq)
  simp [MachineState.bindValue, MachineState.lookupValue, ValueMap.get,
    ValueMap.set, hne]

/-- Reading back the SSA value `bindValue` just bound. -/
private theorem lookupValue_bindValue_self (st : MachineState) (v : Value) :
    (st.bindValue v).snd.lookupValue (st.bindValue v).fst = some v := by
  simp [MachineState.bindValue, MachineState.lookupValue, ValueMap.get,
    ValueMap.set]

/-- **Fat-pointer round trip, Sem level (B3 depth ledger "Fat-pointer
    values").** Running the instruction sequence

        d ← PtrData    fatptr<kind> p
        m ← PtrMetadata fatptr<kind> p
        r ← PtrFromParts fatptr<kind> d m

    from ANY state in which `p` holds a fat-pointer value `.fatPtr data
    prov metadata` succeeds and binds `r` to the IDENTICAL value — the
    decompose/recombine round trip at the operational layer, on top of the
    value-level `fatPtr_roundTrip_value` / `fatPtrFromParts_data_metadata`
    (Proofs/MemoryProps.lean).

    Hypotheses, honestly stated:
    * `hLive`: `p` is an already-allocated SSA id (`index < nextValueId`),
      so the three fresh result binds cannot shadow it — the standing SSA
      well-formedness invariant of the evaluator;
    * `hNull`: a null data lane carries no provenance, which every fat
      pointer the semantics constructs keeps (`fatPtrFromPartsValue`,
      `Memory.resolveDecoded`);
    * `hMeta`: the stored metadata inhabits the kind's declared metadata
      type (`U64` length / `Ptr` vtable at the model's 64-bit width) — the
      same guard `PtrFromParts` enforces on injection, so any `.fatPtr`
      the semantics itself constructed satisfies it. -/
theorem semFatPtr_roundTrip (kind : FatPtrKind) (data : Nat) (prov : Option AllocId)
    (metadata : Value) (ptrId : ValueId) (s : MachineState)
    (hP : s.lookupValue ptrId = some (.fatPtr data prov metadata))
    (hNull : data = 0 → prov = none)
    (hLive : ptrId.index < s.nextValueId)
    (hMeta : metadataInhabits kind.metadataTy metadata = true) :
    ∃ (resultId : ValueId) (sEnd : MachineState),
      Sem.run (do
          let dataId ← semPtrData (.FatPtr kind) ptrId
          let metaId ← semPtrMetadata (.FatPtr kind) kind.metadataTy ptrId
          semPtrFromParts (.FatPtr kind) kind.metadataTy dataId metaId) s
        = .ok (resultId, sEnd)
      ∧ sEnd.lookupValue resultId = some (.fatPtr data prov metadata) := by
  -- Reflexivity of the static metadata-type check (structural, so it
  -- reduces per kind).
  have hmt : metadataTyMatches kind.metadataTy kind = true := by
    cases kind <;> rfl
  have hValid :
      fatPtrStoreValueValid (.FatPtr kind) (.fatPtr data prov metadata) = true := by
    exact hMeta
  let dataLane : Value := fatPtrDataLane data prov
  have hRebuild :
      fatPtrFromPartsValue dataLane metadata = some (.fatPtr data prov metadata) := by
    cases data with
    | zero => rw [hNull rfl]; rfl
    | succ _ => rfl
  -- Intermediate ids and states.
  let dId : ValueId := ValueId.mk s.nextValueId
  let s1 : MachineState := (s.bindValue dataLane).snd
  let mId : ValueId := ValueId.mk s1.nextValueId
  let s2 : MachineState := (s1.bindValue metadata).snd
  let rId : ValueId := ValueId.mk s2.nextValueId
  let s3 : MachineState := (s2.bindValue (.fatPtr data prov metadata)).snd
  -- Step 1: PtrData projects the data lane onto the fresh id dId.
  have h1 : Sem.run (semPtrData (.FatPtr kind) ptrId) s = .ok (dId, s1) := by
    unfold semPtrData
    simp only [fatPtrStoreValueValidFor]
    simp only [Sem.run, sr_bind, sr_lookup, hP, hValid, Bool.not_true,
      Bool.false_eq_true, if_false, fatPtrDataValue, Except.bind]
    exact bindFresh_run dataLane s
  -- The original binding survives the fresh bind (hLive).
  have hP1 : s1.lookupValue ptrId = some (.fatPtr data prov metadata) := by
    rw [show s1 = (s.bindValue dataLane).snd from rfl,
      lookupValue_bindValue_ne s dataLane ptrId (Nat.ne_of_lt hLive)]
    exact hP
  -- Step 2: PtrMetadata projects the metadata lane onto the fresh id mId.
  have h2 : Sem.run (semPtrMetadata (.FatPtr kind) kind.metadataTy ptrId) s1
      = .ok (mId, s2) := by
    unfold semPtrMetadata
    simp only [metadataTyMatchesFor, fatPtrStoreValueValidFor]
    simp only [Sem.run, hmt, Bool.not_true, Bool.false_eq_true, if_false,
      sr_bind, sr_lookup, hP1, hValid, fatPtrMetadataValue, Except.bind]
    exact bindFresh_run metadata s1
  -- Lookups in s2: the freshly bound metadata, and the surviving data lane.
  have hM2 : s2.lookupValue mId = some metadata :=
    lookupValue_bindValue_self s1 metadata
  have hD2 : s2.lookupValue dId = some dataLane := by
    rw [show s2 = (s1.bindValue metadata).snd from rfl,
      lookupValue_bindValue_ne s1 metadata dId
        (Nat.ne_of_lt (Nat.lt_succ_self s.nextValueId))]
    exact lookupValue_bindValue_self s dataLane
  have hDataDefined : ∀ op, Sem.rejectPartial dataLane op = pure () := by
    intro op
    cases data <;> rfl
  have hMetadataDefined : ∀ op, Sem.rejectPartial metadata op = pure () := by
    intro op
    cases metadata <;> try rfl
    all_goals cases kind <;> simp [metadataInhabits, FatPtrKind.metadataTy] at hMeta
  -- Step 3: PtrFromParts recombines the lanes onto the fresh id rId.
  have h3 : Sem.run (semPtrFromParts (.FatPtr kind) kind.metadataTy dId mId) s2
      = .ok (rId, s3) := by
    unfold semPtrFromParts
    simp only [metadataTyMatchesFor, metadataInhabitsFor]
    simp only [Sem.run, hmt, Bool.not_true, Bool.false_eq_true, if_false,
      sr_bind, sr_lookup, hM2, hMeta, hD2, hRebuild, Except.bind,
      hDataDefined, hMetadataDefined, sr_pure]
    exact bindFresh_run (.fatPtr data prov metadata) s2
  -- Compose the three runs and read the result back.
  refine ⟨rId, s3, ?_, ?_⟩
  · rw [Sem.run_bind, h1]
    simp only [Except.bind]
    rw [Sem.run_bind, h2]
    simp only [Except.bind]
    exact h3
  · exact lookupValue_bindValue_self s2 (.fatPtr data prov metadata)

-- =================================================================
-- Future work
-- =================================================================

/-
## Theorems for subsequent phases

1. **Full memory safety for well-typed programs:**
   If a program is well-typed (all memory accesses are through valid
   pointers with appropriate permissions), then no UB error is produced.
   This requires the full typing judgment from Phase 6.

2. **Separation logic frame rule:**
   If a computation only accesses allocations in a footprint F, then
   the rest of memory is preserved. This enables modular reasoning.

3. **Temporal safety:**
   No use-after-free: once an allocation is freed, no subsequent
   load/store can access it. This follows from the alive check in
   semLoad/semStore combined with the deallocation marking.

4. **Spatial safety:**
   No out-of-bounds access: all loads/stores are within the bounds of
   the allocation their pointer was derived from (`semAccess_names_provenance`).
-/

end TrustIr

#trustIrAxiomsExact TrustIr.semDealloc_twice_is_ub_example == []
#trustIrAxiomsExact TrustIr.semRelease_after_last_release_is_ub == []
#trustIrAxiomsExact TrustIr.semDealloc_cleanHeap_is_ub_example == []
#trustIrAxiomsExact TrustIr.semDealloc_swiftHeap_is_ub_example == []
#trustIrAxiomsExact TrustIr.requireArcRef_non_arcRef_is_ub == []
#trustIrAxiomsExact TrustIr.semRetain_alloca_is_ub_example == []
#trustIrAxiomsExact TrustIr.semRelease_rustHeap_is_ub_example == []
#trustIrAxiomsExact TrustIr.semIsUnique_cMalloc_is_ub_example == []
#trustIrAxiomsExact TrustIr.semRetain_globalAddr_is_ub_example == []
#trustIrAxiomsExact TrustIr.arc_at_object_base_ok_example == []
#trustIrAxiomsExact TrustIr.semDealloc_under_borrow_is_ub_example == []
#trustIrAxiomsExact TrustIr.semDealloc_under_borrowMut_is_ub_example == []
#trustIrAxiomsExact TrustIr.semDealloc_one_of_two_borrows_live_is_ub_example == []
#trustIrAxiomsExact TrustIr.semDealloc_after_every_endBorrow_ok_example == []

#trustIrAxiomsExact TrustIr.semRetain_non_arcRef_is_ub == [propext]
#trustIrAxiomsExact TrustIr.semRelease_non_arcRef_is_ub == [propext]
#trustIrAxiomsExact TrustIr.semIsUnique_non_arcRef_is_ub == [propext]
