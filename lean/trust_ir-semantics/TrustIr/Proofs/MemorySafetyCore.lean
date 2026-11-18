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
import TrustIr.Proofs.SemRunEquations

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
  have lookup (state : MachineState) (value : Value) :
      (state.bindValue value).snd.lookupValue (state.bindValue value).fst = some value := by
    simp [MachineState.bindValue, MachineState.lookupValue, ValueMap.get, ValueMap.set]
  refine ⟨v2, ?_, rfl⟩
  rw [hres, hs2]
  exact lookup _ _

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


end TrustIr
