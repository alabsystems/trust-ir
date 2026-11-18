-- Copyright 2026 Andrew Yates | Apache-2.0
import TrustIr.Proofs.MemorySafetyCore

namespace TrustIr

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

-- Ground fixture transitions, each separately kernel-convertible. These
-- definitions describe the existing operations' results, not a new evaluator.
private def lifetimeStack32 : ValueId × MachineState :=
  let before := MachineState.empty
  let id := AllocId.mk before.memory.nextAllocId
  let (address, memory) := before.memory.alloc 4 4 0 .rustStack
  let allocated : MachineState :=
    { before with memory := memory, permissions := before.permissions.set id .owned }
  allocated.bindValue (.ptr address (some id))

private def lifetimeFreed32 : MachineState :=
  let before := lifetimeStack32.2
  let id := AllocId.mk 0
  let allocations := before.memory.allocations.map
    (fun allocation => if allocation.id == id then { allocation with alive := false } else allocation)
  let memory := { before.memory with allocations := allocations }
  { before with
    memory := memory
    permissions := clearPermissionAt before.permissions id
    refCounts := clearRefCountAt before.refCounts id }

private theorem lifetimeStack32_run :
    StateT.run (semAlloca .I32 none) MachineState.empty = .ok lifetimeStack32 := rfl

private theorem lifetimeFree32_run :
    StateT.run (semDealloc lifetimeStack32.1) lifetimeStack32.2 =
      .ok ((), lifetimeFreed32) := rfl

private theorem lifetimeFree32_again_run :
    StateT.run (semDealloc lifetimeStack32.1) lifetimeFreed32 =
      .error (.ub "Dealloc: allocation is already dead (double free)") := rfl

private theorem lifetimeLoad32_afterFree_run :
    StateT.run (semLoad .I32 lifetimeStack32.1) lifetimeFreed32 =
      .error (.ub "Load: use after dealloc") := rfl

#trustIrAxiomsExact lifetimeStack32_run == []
#trustIrAxiomsExact lifetimeFree32_run == []
#trustIrAxiomsExact lifetimeFree32_again_run == []
#print axioms lifetimeLoad32_afterFree_run
#trustIrAxioms lifetimeLoad32_afterFree_run <= [propext, Classical.choice, Quot.sound]

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
  ⟨_, by
    trustIrCompilerProof {
      rfl
    } {
      change StateT.run (semAlloca .I32 none >>= fun ptr =>
        semDealloc ptr >>= fun _ => semDealloc ptr) MachineState.empty = _
      rw [sr_bind, lifetimeStack32_run]
      change StateT.run (semDealloc lifetimeStack32.1 >>= fun _ =>
        semDealloc lifetimeStack32.1) lifetimeStack32.2 = _
      rw [sr_bind, lifetimeFree32_run]
      exact lifetimeFree32_again_run
    }⟩

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
  ⟨_, by
    trustIrCompilerProof {
      rfl
    } {
      change StateT.run (semAlloca .I32 none >>= fun ptr =>
        semDealloc ptr >>= fun _ => semLoad .I32 ptr >>= fun _ => pure ())
        MachineState.empty = _
      rw [sr_bind, lifetimeStack32_run]
      change StateT.run (semDealloc lifetimeStack32.1 >>= fun _ =>
        semLoad .I32 lifetimeStack32.1 >>= fun _ => pure ()) lifetimeStack32.2 = _
      rw [sr_bind, lifetimeFree32_run]
      change StateT.run (semLoad .I32 lifetimeStack32.1 >>= fun _ => pure ())
        lifetimeFreed32 = _
      rw [sr_bind, lifetimeLoad32_afterFree_run]
      all_goals rfl
    }⟩

-- Closed allocator fixtures: each run theorem isolates exactly one operation.
private def lifetimeHeap32 (origin : AllocOrigin) : ValueId × MachineState :=
  let before := MachineState.empty
  let id := AllocId.mk before.memory.nextAllocId
  let (address, memory) := before.memory.alloc 4 4 heapUsableSlack origin.toAllocationOrigin
  let allocated : MachineState :=
    if origin.isRefCounted then
      { before with memory := memory, permissions := before.permissions.set id .arcRef, refCounts := fun key => if key == id then some 1 else before.refCounts key }
    else
      { before with memory := memory, permissions := before.permissions.set id .owned }
  allocated.bindValue (.ptr address (some id))

private theorem lifetimeCleanHeap32_run :
    StateT.run (semHeapAlloc .I32 none .CleanHeap) MachineState.empty =
      .ok (lifetimeHeap32 .CleanHeap) := rfl

private theorem lifetimeSwiftHeap32_run :
    StateT.run (semHeapAlloc .I32 none .SwiftHeap) MachineState.empty =
      .ok (lifetimeHeap32 .SwiftHeap) := rfl

private theorem lifetimeRustHeap32_run :
    StateT.run (semHeapAlloc .I32 none .RustHeap) MachineState.empty =
      .ok (lifetimeHeap32 .RustHeap) := rfl

private theorem lifetimeCMalloc32_run :
    StateT.run (semHeapAlloc .I32 none .CMalloc) MachineState.empty =
      .ok (lifetimeHeap32 .CMalloc) := rfl

private theorem lifetimeCleanHeap32_dealloc :
    StateT.run (semDealloc (lifetimeHeap32 .CleanHeap).1) (lifetimeHeap32 .CleanHeap).2 =
      .error (.ub "Dealloc: permission does not allow deallocation") := rfl

private theorem lifetimeSwiftHeap32_dealloc :
    StateT.run (semDealloc (lifetimeHeap32 .SwiftHeap).1) (lifetimeHeap32 .SwiftHeap).2 =
      .error (.ub "Dealloc: permission does not allow deallocation") := rfl

private theorem lifetimeStack32_retain :
    StateT.run (semRetain lifetimeStack32.1) lifetimeStack32.2 =
      .error (.ub (trustIrStringBuild s!"ARC operation requires arcRef permission, found {repr Permission.owned}")) := rfl

private theorem lifetimeRustHeap32_release :
    StateT.run (semRelease (lifetimeHeap32 .RustHeap).1) (lifetimeHeap32 .RustHeap).2 =
      .error (.ub (trustIrStringBuild s!"ARC operation requires arcRef permission, found {repr Permission.owned}")) := rfl

private theorem lifetimeCMalloc32_unique :
    StateT.run (semIsUnique (lifetimeHeap32 .CMalloc).1) (lifetimeHeap32 .CMalloc).2 =
      .error (.ub (trustIrStringBuild s!"ARC operation requires arcRef permission, found {repr Permission.owned}")) := rfl

#trustIrAxiomsExact lifetimeCleanHeap32_run == []
#trustIrAxiomsExact lifetimeSwiftHeap32_run == []
#trustIrAxiomsExact lifetimeRustHeap32_run == []
#trustIrAxiomsExact lifetimeCMalloc32_run == []
#trustIrAxiomsExact lifetimeCleanHeap32_dealloc == []
#trustIrAxiomsExact lifetimeSwiftHeap32_dealloc == []
#trustIrAxiomsExact lifetimeStack32_retain == []
#trustIrAxiomsExact lifetimeRustHeap32_release == []
#trustIrAxiomsExact lifetimeCMalloc32_unique == []

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

private def lifetimeArcReleased : MachineState :=
  let before := arcLastRefProgramState
  let id := AllocId.mk 0
  let allocations := before.memory.allocations.map
    (fun allocation => if allocation.id == id then { allocation with alive := false } else allocation)
  { before with
    memory := { before.memory with allocations := allocations }
    permissions := clearPermission before.permissions id
    refCounts := setRefCount before.refCounts id 0 }

private theorem lifetimeArcRelease_run :
    StateT.run (semRelease (ValueId.mk 0)) arcLastRefProgramState =
      .ok ((), lifetimeArcReleased) := rfl

private theorem lifetimeArcRelease_again_run :
    StateT.run (semRelease (ValueId.mk 0)) lifetimeArcReleased =
      .error (.ub (trustIrStringBuild s!"ARC pointer references a freed allocation: {(Memory.empty.alloc 4 4 heapUsableSlack .swiftHeap).1}")) := rfl

#trustIrAxiomsExact lifetimeArcRelease_run == []
#trustIrAxiomsExact lifetimeArcRelease_again_run == []

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
  ⟨_, by
    trustIrCompilerProof {
      rfl
    } {
      change StateT.run (semRelease (ValueId.mk 0) >>= fun _ =>
        semRelease (ValueId.mk 0)) arcLastRefProgramState = _
      rw [sr_bind, lifetimeArcRelease_run]
      change StateT.run (semRelease (ValueId.mk 0)) lifetimeArcReleased = _
      exact lifetimeArcRelease_again_run
    }⟩

/-- Positive control for the lifetime theorems: the first dealloc of a live
    owned allocation is NOT an error (so the UB above is caused by the
    second free, not by a defect in the setup). -/
theorem semDealloc_once_ok :
    ∃ post,
      Sem.run (do
          let p ← semAlloca .I32 none
          semDealloc p)
        MachineState.empty = .ok ((), post) :=
  ⟨_, by
    trustIrCompilerProof {
      rfl
    } {
      change StateT.run (semAlloca .I32 none >>= fun ptr => semDealloc ptr)
        MachineState.empty = _
      rw [sr_bind, lifetimeStack32_run]
      change StateT.run (semDealloc lifetimeStack32.1) lifetimeStack32.2 = _
      exact lifetimeFree32_run
    }⟩

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
  by
    trustIrCompilerProof {
      rfl
    } {
      change StateT.run (semHeapAlloc .I32 none .CleanHeap >>= fun ptr =>
        semDealloc ptr) MachineState.empty = _
      rw [sr_bind, lifetimeCleanHeap32_run]
      change StateT.run (semDealloc (lifetimeHeap32 .CleanHeap).1)
        (lifetimeHeap32 .CleanHeap).2 = _
      exact lifetimeCleanHeap32_dealloc
    }

/-- Concrete instance, `SwiftHeap`: the same rule for the Swift ARC heap. -/
theorem semDealloc_swiftHeap_is_ub_example :
    Sem.run (do
        let p ← semHeapAlloc .I32 none .SwiftHeap
        semDealloc p)
      MachineState.empty =
      .error (.ub "Dealloc: permission does not allow deallocation") :=
  by
    trustIrCompilerProof {
      rfl
    } {
      change StateT.run (semHeapAlloc .I32 none .SwiftHeap >>= fun ptr =>
        semDealloc ptr) MachineState.empty = _
      rw [sr_bind, lifetimeSwiftHeap32_run]
      change StateT.run (semDealloc (lifetimeHeap32 .SwiftHeap).1)
        (lifetimeHeap32 .SwiftHeap).2 = _
      exact lifetimeSwiftHeap32_dealloc
    }

private def lifetimeClean7_constant : ValueId × MachineState :=
  (lifetimeHeap32 .CleanHeap).2.bindValue (.int 32 7)

private def lifetimeClean7_stored : MachineState :=
  let before := lifetimeClean7_constant.2
  let address := (Memory.empty.alloc 4 4 heapUsableSlack .cleanHeap).1
  { before with memory := before.memory.writeBytes address [7, 0, 0, 0] }

private def lifetimeClean7_loaded : ValueId × MachineState :=
  lifetimeClean7_stored.bindValue (.int 32 7)

private def lifetimeClean7_released : MachineState :=
  let before := lifetimeClean7_loaded.2
  let id := AllocId.mk 0
  let allocations := before.memory.allocations.map
    (fun allocation => if allocation.id == id then { allocation with alive := false } else allocation)
  { before with
    memory := { before.memory with allocations := allocations }
    permissions := clearPermission before.permissions id
    refCounts := setRefCount before.refCounts id 0 }

private theorem lifetimeClean7_constant_run :
    StateT.run (Sem.bindFresh (.int 32 7)) (lifetimeHeap32 .CleanHeap).2 =
      .ok lifetimeClean7_constant := rfl

private theorem lifetimeClean7_store_run :
    StateT.run (semStore .I32 (lifetimeHeap32 .CleanHeap).1 lifetimeClean7_constant.1)
      lifetimeClean7_constant.2 = .ok ((), lifetimeClean7_stored) := rfl

private theorem lifetimeClean7_load_run :
    StateT.run (semLoad .I32 (lifetimeHeap32 .CleanHeap).1) lifetimeClean7_stored =
      .ok lifetimeClean7_loaded := rfl

private theorem lifetimeClean7_release_run :
    StateT.run (semRelease (lifetimeHeap32 .CleanHeap).1) lifetimeClean7_loaded.2 =
      .ok ((), lifetimeClean7_released) := rfl

private theorem lifetimeClean7_lookup_run :
    StateT.run (Sem.lookupValue lifetimeClean7_loaded.1) lifetimeClean7_released =
      .ok (.int 32 7, lifetimeClean7_released) := rfl

#trustIrAxiomsExact lifetimeClean7_constant_run == []
#print axioms lifetimeClean7_store_run
#trustIrAxioms lifetimeClean7_store_run <= [propext, Classical.choice, Quot.sound]
#print axioms lifetimeClean7_load_run
#trustIrAxioms lifetimeClean7_load_run <= [propext, Classical.choice, Quot.sound]
#trustIrAxiomsExact lifetimeClean7_release_run == []
#trustIrAxiomsExact lifetimeClean7_lookup_run == []

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
  by
    trustIrCompilerProof {
      rfl
    } {
      change (match StateT.run (semHeapAlloc .I32 none .CleanHeap >>= fun ptr =>
        Sem.bindFresh (.int 32 7) >>= fun constant => semStore .I32 ptr constant >>= fun _ =>
        semLoad .I32 ptr >>= fun loaded => semRelease ptr >>= fun _ =>
        Sem.lookupValue loaded) MachineState.empty with
        | .ok (value, _) => some value | .error _ => none) = some (.int 32 7)
      rw [sr_bind, lifetimeCleanHeap32_run]
      change (match StateT.run (Sem.bindFresh (.int 32 7) >>= fun constant =>
        semStore .I32 (lifetimeHeap32 .CleanHeap).1 constant >>= fun _ =>
        semLoad .I32 (lifetimeHeap32 .CleanHeap).1 >>= fun loaded =>
        semRelease (lifetimeHeap32 .CleanHeap).1 >>= fun _ => Sem.lookupValue loaded)
        (lifetimeHeap32 .CleanHeap).2 with
        | .ok (value, _) => some value | .error _ => none) = some (.int 32 7)
      rw [sr_bind, lifetimeClean7_constant_run]
      change (match StateT.run (semStore .I32 (lifetimeHeap32 .CleanHeap).1
        lifetimeClean7_constant.1 >>= fun _ => semLoad .I32 (lifetimeHeap32 .CleanHeap).1 >>=
        fun loaded => semRelease (lifetimeHeap32 .CleanHeap).1 >>= fun _ => Sem.lookupValue loaded)
        lifetimeClean7_constant.2 with
        | .ok (value, _) => some value | .error _ => none) = some (.int 32 7)
      rw [sr_bind, lifetimeClean7_store_run]
      change (match StateT.run (semLoad .I32 (lifetimeHeap32 .CleanHeap).1 >>= fun loaded =>
        semRelease (lifetimeHeap32 .CleanHeap).1 >>= fun _ => Sem.lookupValue loaded)
        lifetimeClean7_stored with
        | .ok (value, _) => some value | .error _ => none) = some (.int 32 7)
      rw [sr_bind, lifetimeClean7_load_run]
      change (match StateT.run (semRelease (lifetimeHeap32 .CleanHeap).1 >>= fun _ =>
        Sem.lookupValue lifetimeClean7_loaded.1) lifetimeClean7_loaded.2 with
        | .ok (value, _) => some value | .error _ => none) = some (.int 32 7)
      rw [sr_bind, lifetimeClean7_release_run]
      change (match StateT.run (Sem.lookupValue lifetimeClean7_loaded.1) lifetimeClean7_released with
        | .ok (value, _) => some value | .error _ => none) = some (.int 32 7)
      rw [lifetimeClean7_lookup_run]
    }

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
  ⟨_, by
    trustIrCompilerProof {
      rfl
    } {
      change StateT.run (semAlloca .I32 none >>= fun ptr => semRetain ptr)
        MachineState.empty = _
      rw [sr_bind, lifetimeStack32_run]
      change StateT.run (semRetain lifetimeStack32.1) lifetimeStack32.2 = _
      exact lifetimeStack32_retain
    }⟩

/-- Concrete instance, a `RustHeap` cell: `Release` of it is UB (it is freed by
    its allocator's free, which the format spells as a call). -/
theorem semRelease_rustHeap_is_ub_example :
    ∃ msg,
      Sem.run (do
          let p ← semHeapAlloc .I32 none .RustHeap
          semRelease p)
        MachineState.empty = .error (.ub msg) :=
  ⟨_, by
    trustIrCompilerProof {
      rfl
    } {
      change StateT.run (semHeapAlloc .I32 none .RustHeap >>= fun ptr =>
        semRelease ptr) MachineState.empty = _
      rw [sr_bind, lifetimeRustHeap32_run]
      change StateT.run (semRelease (lifetimeHeap32 .RustHeap).1)
        (lifetimeHeap32 .RustHeap).2 = _
      exact lifetimeRustHeap32_release
    }⟩

/-- Concrete instance, a `CMalloc` cell: `IsUnique` of it is UB. -/
theorem semIsUnique_cMalloc_is_ub_example :
    ∃ msg,
      Sem.run (do
          let p ← semHeapAlloc .I32 none .CMalloc
          semIsUnique p)
        MachineState.empty = .error (.ub msg) :=
  ⟨_, by
    trustIrCompilerProof {
      rfl
    } {
      change StateT.run (semHeapAlloc .I32 none .CMalloc >>= fun ptr =>
        semIsUnique ptr) MachineState.empty = _
      rw [sr_bind, lifetimeCMalloc32_run]
      change StateT.run (semIsUnique (lifetimeHeap32 .CMalloc).1)
        (lifetimeHeap32 .CMalloc).2 = _
      exact lifetimeCMalloc32_unique
    }⟩

private def lifetimeGlobal0 : ValueId × MachineState :=
  let before := MachineState.empty
  let (address, memory) := before.memory.alloc 1 globalSectionAlign 0 .rustHeap
  let id := AllocId.mk before.memory.nextAllocId
  let allocated : MachineState :=
    { before with
      memory := memory
      permissions := before.permissions.set id .owned
      globals := (GlobalId.mk 0, address, id) :: before.globals }
  allocated.bindValue (.ptr address (some id))

private theorem lifetimeGlobal0_run :
    StateT.run (semGlobalAddr (GlobalId.mk 0)) MachineState.empty =
      .ok lifetimeGlobal0 := rfl

private theorem lifetimeGlobal0_retain :
    StateT.run (semRetain lifetimeGlobal0.1) lifetimeGlobal0.2 =
      .error (.ub (trustIrStringBuild s!"ARC operation requires arcRef permission, found {repr Permission.owned}")) := rfl

#trustIrAxiomsExact lifetimeGlobal0_run == []
#trustIrAxiomsExact lifetimeGlobal0_retain == []

/-- Concrete instance, a global's reservation: `Retain` of the address
    `semGlobalAddr` reserves is UB. -/
theorem semRetain_globalAddr_is_ub_example :
    ∃ msg,
      Sem.run (do
          let g ← semGlobalAddr ⟨0⟩
          semRetain g)
        MachineState.empty = .error (.ub msg) :=
  ⟨_, by
    trustIrCompilerProof {
      rfl
    } {
      change StateT.run (semGlobalAddr (GlobalId.mk 0) >>= fun ptr => semRetain ptr)
        MachineState.empty = _
      rw [sr_bind, lifetimeGlobal0_run]
      change StateT.run (semRetain lifetimeGlobal0.1) lifetimeGlobal0.2 = _
      exact lifetimeGlobal0_retain
    }⟩

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
      trustIrCompilerProof {
        rfl
      } {
        trustIrReduce
      }⟩, by
    simp only [semGEPUsing, semGEPValuesUsing, pure_bind, bind_assoc]
    trustIrCompilerProof {
      rfl
    } {
      trustIrReduce
    }⟩

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
  ⟨_, by
    trustIrCompilerProof {
      rfl
    } {
      trustIrReduce
    }⟩

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
      .ok (cleanI32Allocation MachineState.empty) := by
        trustIrCompilerProof {
          rfl
        } {
          rfl
        }

private theorem cleanI32Allocation_second :
    StateT.run (semHeapAlloc .I32 none .CleanHeap) (cleanI32Allocation MachineState.empty).2 =
      .ok (cleanI32Allocation (cleanI32Allocation MachineState.empty).2) := by
        trustIrCompilerProof {
          rfl
        } {
          rfl
        }

#trustIrAxiomsExact cleanI32Allocation_empty == []
#trustIrAxiomsExact cleanI32Allocation_second == []

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
    trustIrCompilerProof {
      rfl
    } {
      trustIrReduce
    }⟩

private def lifetimeArcBase_retained : MachineState :=
  let before := (lifetimeHeap32 .CleanHeap).2
  { before with refCounts := setRefCount before.refCounts (AllocId.mk 0) 2 }

private def lifetimeArcBase_notUnique : ValueId × MachineState :=
  lifetimeArcBase_retained.bindValue (.bool false)

private def lifetimeArcBase_released : MachineState :=
  let before := lifetimeArcBase_notUnique.2
  { before with refCounts := setRefCount before.refCounts (AllocId.mk 0) 1 }

private def lifetimeArcBase_unique : ValueId × MachineState :=
  lifetimeArcBase_released.bindValue (.bool true)

private theorem lifetimeArcBase_retain_run :
    StateT.run (semRetain (lifetimeHeap32 .CleanHeap).1) (lifetimeHeap32 .CleanHeap).2 =
      .ok ((), lifetimeArcBase_retained) := rfl

private theorem lifetimeArcBase_notUnique_run :
    StateT.run (semIsUnique (lifetimeHeap32 .CleanHeap).1) lifetimeArcBase_retained =
      .ok lifetimeArcBase_notUnique := rfl

private theorem lifetimeArcBase_release_run :
    StateT.run (semRelease (lifetimeHeap32 .CleanHeap).1) lifetimeArcBase_notUnique.2 =
      .ok ((), lifetimeArcBase_released) := rfl

private theorem lifetimeArcBase_unique_run :
    StateT.run (semIsUnique (lifetimeHeap32 .CleanHeap).1) lifetimeArcBase_released =
      .ok lifetimeArcBase_unique := rfl

private theorem lifetimeArcBase_lookups_run :
    StateT.run (do
      let first ← Sem.lookupValue lifetimeArcBase_notUnique.1
      let second ← Sem.lookupValue lifetimeArcBase_unique.1
      pure (first, second) : Sem (Value × Value)) lifetimeArcBase_unique.2 =
      .ok ((.bool false, .bool true), lifetimeArcBase_unique.2) := rfl

#trustIrAxiomsExact lifetimeArcBase_retain_run == []
#trustIrAxiomsExact lifetimeArcBase_notUnique_run == []
#trustIrAxiomsExact lifetimeArcBase_release_run == []
#trustIrAxiomsExact lifetimeArcBase_unique_run == []
#trustIrAxiomsExact lifetimeArcBase_lookups_run == []

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
  by
    trustIrCompilerProof {
      rfl
    } {
      change (match StateT.run (semHeapAlloc .I32 none .CleanHeap >>= fun ptr =>
        semRetain ptr >>= fun _ => semIsUnique ptr >>= fun first =>
        semRelease ptr >>= fun _ => semIsUnique ptr >>= fun second =>
        Sem.lookupValue first >>= fun x => Sem.lookupValue second >>= fun y => pure (x, y))
        MachineState.empty with | .ok (value, _) => some value | .error _ => none) =
        some (.bool false, .bool true)
      rw [sr_bind, lifetimeCleanHeap32_run]
      change (match StateT.run (semRetain (lifetimeHeap32 .CleanHeap).1 >>= fun _ =>
        semIsUnique (lifetimeHeap32 .CleanHeap).1 >>= fun first =>
        semRelease (lifetimeHeap32 .CleanHeap).1 >>= fun _ =>
        semIsUnique (lifetimeHeap32 .CleanHeap).1 >>= fun second =>
        Sem.lookupValue first >>= fun x => Sem.lookupValue second >>= fun y => pure (x, y))
        (lifetimeHeap32 .CleanHeap).2 with | .ok (value, _) => some value | .error _ => none) =
        some (.bool false, .bool true)
      rw [sr_bind, lifetimeArcBase_retain_run]
      change (match StateT.run (semIsUnique (lifetimeHeap32 .CleanHeap).1 >>= fun first =>
        semRelease (lifetimeHeap32 .CleanHeap).1 >>= fun _ =>
        semIsUnique (lifetimeHeap32 .CleanHeap).1 >>= fun second =>
        Sem.lookupValue first >>= fun x => Sem.lookupValue second >>= fun y => pure (x, y))
        lifetimeArcBase_retained with | .ok (value, _) => some value | .error _ => none) =
        some (.bool false, .bool true)
      rw [sr_bind, lifetimeArcBase_notUnique_run]
      change (match StateT.run (semRelease (lifetimeHeap32 .CleanHeap).1 >>= fun _ =>
        semIsUnique (lifetimeHeap32 .CleanHeap).1 >>= fun second =>
        Sem.lookupValue lifetimeArcBase_notUnique.1 >>= fun x =>
        Sem.lookupValue second >>= fun y => pure (x, y)) lifetimeArcBase_notUnique.2 with
        | .ok (value, _) => some value | .error _ => none) = some (.bool false, .bool true)
      rw [sr_bind, lifetimeArcBase_release_run]
      change (match StateT.run (semIsUnique (lifetimeHeap32 .CleanHeap).1 >>= fun second =>
        Sem.lookupValue lifetimeArcBase_notUnique.1 >>= fun x =>
        Sem.lookupValue second >>= fun y => pure (x, y)) lifetimeArcBase_released with
        | .ok (value, _) => some value | .error _ => none) = some (.bool false, .bool true)
      rw [sr_bind, lifetimeArcBase_unique_run]
      change (match StateT.run (do
        let first ← Sem.lookupValue lifetimeArcBase_notUnique.1
        let second ← Sem.lookupValue lifetimeArcBase_unique.1
        pure (first, second) : Sem (Value × Value)) lifetimeArcBase_unique.2 with
        | .ok (value, _) => some value | .error _ => none) = some (.bool false, .bool true)
      rw [lifetimeArcBase_lookups_run]
    }

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

-- Shared stack-borrow fixtures retain actual locals and fresh value identifiers.
private def lifetimeBorrow32 (before : MachineState) (permission : Permission) : ValueId × MachineState :=
  let changed : MachineState := { before with permissions := before.permissions.set (AllocId.mk 0) permission }
  let address := (Memory.empty.alloc 4 4 0 .rustStack).1
  changed.bindValue (.ptr address (some (AllocId.mk 0)))

private def lifetimeBorrow32_first : ValueId × MachineState :=
  lifetimeBorrow32 lifetimeStack32.2 (.sharedBorrow 1)

private def lifetimeBorrow32_second : ValueId × MachineState :=
  lifetimeBorrow32 lifetimeBorrow32_first.2 (.sharedBorrow 2)

private def lifetimeBorrow32_unique : ValueId × MachineState :=
  lifetimeBorrow32 lifetimeStack32.2 .uniqueBorrow

private def lifetimeBorrow32_oneEnded : MachineState :=
  { lifetimeBorrow32_second.2 with permissions := lifetimeBorrow32_second.2.permissions.set (AllocId.mk 0) (.sharedBorrow 1) }

private def lifetimeBorrow32_bothEnded : MachineState :=
  { lifetimeBorrow32_oneEnded with permissions := lifetimeBorrow32_oneEnded.permissions.set (AllocId.mk 0) .owned }

private def lifetimeBorrow32_freed : MachineState :=
  let before := lifetimeBorrow32_bothEnded
  let id := AllocId.mk 0
  let allocations := before.memory.allocations.map
    (fun allocation => if allocation.id == id then { allocation with alive := false } else allocation)
  { before with
    memory := { before.memory with allocations := allocations }
    permissions := clearPermissionAt before.permissions id
    refCounts := clearRefCountAt before.refCounts id }

private theorem lifetimeBorrow32_first_run :
    StateT.run (semBorrow lifetimeStack32.1) lifetimeStack32.2 =
      .ok lifetimeBorrow32_first := rfl

private theorem lifetimeBorrow32_second_run :
    StateT.run (semBorrow lifetimeStack32.1) lifetimeBorrow32_first.2 =
      .ok lifetimeBorrow32_second := rfl

private theorem lifetimeBorrow32_unique_run :
    StateT.run (semBorrowMut lifetimeStack32.1) lifetimeStack32.2 =
      .ok lifetimeBorrow32_unique := rfl

private theorem lifetimeBorrow32_shared_dealloc :
    StateT.run (semDealloc lifetimeStack32.1) lifetimeBorrow32_first.2 =
      .error (.ub "Dealloc: permission does not allow deallocation") := rfl

private theorem lifetimeBorrow32_unique_dealloc :
    StateT.run (semDealloc lifetimeStack32.1) lifetimeBorrow32_unique.2 =
      .error (.ub "Dealloc: permission does not allow deallocation") := rfl

private theorem lifetimeBorrow32_oneEnded_dealloc :
    StateT.run (semDealloc lifetimeStack32.1) lifetimeBorrow32_oneEnded =
      .error (.ub "Dealloc: permission does not allow deallocation") := rfl

private theorem lifetimeBorrow32_endFirst_run :
    StateT.run (semEndBorrow lifetimeBorrow32_first.1) lifetimeBorrow32_second.2 =
      .ok ((), lifetimeBorrow32_oneEnded) := rfl

private theorem lifetimeBorrow32_endSecond_run :
    StateT.run (semEndBorrow lifetimeBorrow32_second.1) lifetimeBorrow32_oneEnded =
      .ok ((), lifetimeBorrow32_bothEnded) := rfl

private theorem lifetimeBorrow32_freed_run :
    StateT.run (semDealloc lifetimeStack32.1) lifetimeBorrow32_bothEnded =
      .ok ((), lifetimeBorrow32_freed) := rfl

#trustIrAxiomsExact lifetimeBorrow32_first_run == []
#trustIrAxiomsExact lifetimeBorrow32_second_run == []
#trustIrAxiomsExact lifetimeBorrow32_unique_run == []
#trustIrAxiomsExact lifetimeBorrow32_shared_dealloc == []
#trustIrAxiomsExact lifetimeBorrow32_unique_dealloc == []
#trustIrAxiomsExact lifetimeBorrow32_oneEnded_dealloc == []
#trustIrAxiomsExact lifetimeBorrow32_endFirst_run == []
#trustIrAxiomsExact lifetimeBorrow32_endSecond_run == []
#trustIrAxiomsExact lifetimeBorrow32_freed_run == []

/-- Concrete instance, shared: `Alloca`, `Borrow`, then `Dealloc` with the
    borrow live is UB. -/
theorem semDealloc_under_borrow_is_ub_example :
    Sem.run (do
        let p ← semAlloca .I32 none
        let _ ← semBorrow p
        semDealloc p)
      MachineState.empty =
      .error (.ub "Dealloc: permission does not allow deallocation") :=
  by
    trustIrCompilerProof {
      rfl
    } {
      change StateT.run (semAlloca .I32 none >>= fun ptr =>
        semBorrow ptr >>= fun _ => semDealloc ptr) MachineState.empty = _
      rw [sr_bind, lifetimeStack32_run]
      change StateT.run (semBorrow lifetimeStack32.1 >>= fun _ =>
        semDealloc lifetimeStack32.1) lifetimeStack32.2 = _
      rw [sr_bind, lifetimeBorrow32_first_run]
      change StateT.run (semDealloc lifetimeStack32.1) lifetimeBorrow32_first.2 = _
      exact lifetimeBorrow32_shared_dealloc
    }

/-- Concrete instance, unique: `Alloca`, `BorrowMut`, then `Dealloc` with it
    live is UB. -/
theorem semDealloc_under_borrowMut_is_ub_example :
    Sem.run (do
        let p ← semAlloca .I32 none
        let _ ← semBorrowMut p
        semDealloc p)
      MachineState.empty =
      .error (.ub "Dealloc: permission does not allow deallocation") :=
  by
    trustIrCompilerProof {
      rfl
    } {
      change StateT.run (semAlloca .I32 none >>= fun ptr =>
        semBorrowMut ptr >>= fun _ => semDealloc ptr) MachineState.empty = _
      rw [sr_bind, lifetimeStack32_run]
      change StateT.run (semBorrowMut lifetimeStack32.1 >>= fun _ =>
        semDealloc lifetimeStack32.1) lifetimeStack32.2 = _
      rw [sr_bind, lifetimeBorrow32_unique_run]
      change StateT.run (semDealloc lifetimeStack32.1) lifetimeBorrow32_unique.2 = _
      exact lifetimeBorrow32_unique_dealloc
    }

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
  by
    trustIrCompilerProof {
      rfl
    } {
      trustIrReduce
    }

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
  by
    trustIrCompilerProof {
      rfl
    } {
      change StateT.run (semAlloca .I32 none >>= fun ptr =>
        semBorrow ptr >>= fun first => semBorrow ptr >>= fun _ =>
        semEndBorrow first >>= fun _ => semDealloc ptr) MachineState.empty = _
      rw [sr_bind, lifetimeStack32_run]
      change StateT.run (semBorrow lifetimeStack32.1 >>= fun first =>
        semBorrow lifetimeStack32.1 >>= fun _ => semEndBorrow first >>= fun _ =>
        semDealloc lifetimeStack32.1) lifetimeStack32.2 = _
      rw [sr_bind, lifetimeBorrow32_first_run]
      change StateT.run (semBorrow lifetimeStack32.1 >>= fun _ =>
        semEndBorrow lifetimeBorrow32_first.1 >>= fun _ => semDealloc lifetimeStack32.1)
        lifetimeBorrow32_first.2 = _
      rw [sr_bind, lifetimeBorrow32_second_run]
      change StateT.run (semEndBorrow lifetimeBorrow32_first.1 >>= fun _ =>
        semDealloc lifetimeStack32.1) lifetimeBorrow32_second.2 = _
      rw [sr_bind, lifetimeBorrow32_endFirst_run]
      change StateT.run (semDealloc lifetimeStack32.1) lifetimeBorrow32_oneEnded = _
      exact lifetimeBorrow32_oneEnded_dealloc
    }

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
  by
    trustIrCompilerProof {
      rfl
    } {
      change (match StateT.run (semAlloca .I32 none >>= fun ptr =>
        semBorrow ptr >>= fun first => semBorrow ptr >>= fun second =>
        semEndBorrow first >>= fun _ => semEndBorrow second >>= fun _ =>
        semDealloc ptr) MachineState.empty with
        | .ok _ => true | .error _ => false) = true
      rw [sr_bind, lifetimeStack32_run]
      change (match StateT.run (semBorrow lifetimeStack32.1 >>= fun first =>
        semBorrow lifetimeStack32.1 >>= fun second => semEndBorrow first >>= fun _ =>
        semEndBorrow second >>= fun _ => semDealloc lifetimeStack32.1)
        lifetimeStack32.2 with | .ok _ => true | .error _ => false) = true
      rw [sr_bind, lifetimeBorrow32_first_run]
      change (match StateT.run (semBorrow lifetimeStack32.1 >>= fun second =>
        semEndBorrow lifetimeBorrow32_first.1 >>= fun _ => semEndBorrow second >>= fun _ =>
        semDealloc lifetimeStack32.1) lifetimeBorrow32_first.2 with
        | .ok _ => true | .error _ => false) = true
      rw [sr_bind, lifetimeBorrow32_second_run]
      change (match StateT.run (semEndBorrow lifetimeBorrow32_first.1 >>= fun _ =>
        semEndBorrow lifetimeBorrow32_second.1 >>= fun _ => semDealloc lifetimeStack32.1)
        lifetimeBorrow32_second.2 with | .ok _ => true | .error _ => false) = true
      rw [sr_bind, lifetimeBorrow32_endFirst_run]
      change (match StateT.run (semEndBorrow lifetimeBorrow32_second.1 >>= fun _ =>
        semDealloc lifetimeStack32.1) lifetimeBorrow32_oneEnded with
        | .ok _ => true | .error _ => false) = true
      rw [sr_bind, lifetimeBorrow32_endSecond_run]
      change (match StateT.run (semDealloc lifetimeStack32.1) lifetimeBorrow32_bothEnded with
        | .ok _ => true | .error _ => false) = true
      rw [lifetimeBorrow32_freed_run]
    }

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
  by
    trustIrCompilerProof {
      rfl
    } {
      trustIrReduce
    }

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


end TrustIr
