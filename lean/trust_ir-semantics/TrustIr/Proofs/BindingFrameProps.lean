-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Frame-algebra theorems for typed binding frames.
--
-- Reference: designs/2026-04-19-binding-frames-lean-semantics.md, section 4
-- Issue:     TrustIr#32
--
-- The four core algebraic laws of the BindSlot/LoadSlot API:
--   * loadSlot after bindSlot at the same slot returns the written value
--   * loadSlot after bindSlot at a different slot returns the original
--   * OpenFrame ; CloseFrame preserves memory/perms/refCounts
--   * BindSlot at distinct slots commutes
--
-- These laws justify TrustCg-side transformations: constant folding reads
-- back through a BindSlot, dead-frame elimination, and independent-slot
-- reordering during frame construction.

import TrustIr.Semantics.Frame
import TrustIr.Semantics.Call

namespace TrustIr

/-!
# Binding-frame algebra

Each theorem corresponds to one bullet in issue TrustIr#32's acceptance
criteria. Proofs are by structural induction on the slot list, using
only core Lean 4.8.0 (no Mathlib). The three private list lemmas
below are standard stdlib lemmas that ship in Mathlib but not in
Lean core -- reproved here to keep the trust_ir-semantics package
Mathlib-free.
-/

-- =================================================================
-- Private list lemmas (stdlib-free, Mathlib-free)
-- =================================================================

/-- List.get? after List.set at the same index returns the written
    value, provided the index is in bounds. -/
private theorem List_get?_set_eq_self {α : Type} :
    (l : List α) -> (k : Nat) -> (v : α) -> k < l.length ->
    trustIrListGet? (l.set k v) k = some v
  | [],      _,      _, h => absurd h (by simp [List.length])
  | _ :: _,  0,      _, _ => rfl
  | _ :: xs, n + 1,  v, h => by
      first
      | simp only [List.set, List.get?]
      | simp only [List.set, trustIrListGetConsSucc]
      have hxs : n < xs.length := by simp [List.length] at h; omega
      exact List_get?_set_eq_self xs n v hxs

/-- List.get? at index j after List.set at a different index k equals
    the original List.get? at j. -/
private theorem List_get?_set_ne_self {α : Type} :
    (l : List α) -> (k j : Nat) -> (v : α) -> k ≠ j ->
    trustIrListGet? (l.set k v) j = trustIrListGet? l j
  | [], _, _, _, _ => by simp [List.set]
  | _ :: _,  0,      0,     _, hne => absurd rfl hne
  | _ :: _,  0,      _ + 1, _, _   => rfl
  | _ :: _,  _ + 1,  0,     _, _   => rfl
  | _ :: xs, n + 1,  m + 1, v, hne => by
      first
      | simp only [List.set, List.get?]
      | simp only [List.set, trustIrListGetConsSucc]
      exact List_get?_set_ne_self xs n m v (fun h => hne (congrArg Nat.succ h))

/-- Two List.set operations at distinct indices commute. -/
private theorem List_set_comm_of_ne {α : Type} :
    (l : List α) -> (k j : Nat) -> (u v : α) -> k ≠ j ->
    (l.set k u).set j v = (l.set j v).set k u
  | [], _, _, _, _, _ => by simp [List.set]
  | _ :: _,  0,      0,     _, _, hne => absurd rfl hne
  | _ :: _,  0,      _ + 1, _, _, _   => rfl
  | _ :: _,  _ + 1,  0,     _, _, _   => rfl
  | _ :: xs, n + 1,  m + 1, u, v, hne => by
      simp only [List.set]
      congr 1
      exact List_set_comm_of_ne xs n m u v (fun h => hne (congrArg Nat.succ h))

-- =================================================================
-- 4.1 loadSlot_bindSlot_same: read-after-write
-- =================================================================

/-- Reading a slot immediately after writing it returns the written value.

    This is the core algebraic law: loadSlot is the left-inverse of
    bindSlot at the same index, for any in-bounds slot. It justifies
    constant-folding a load through a bind during TrustIr optimisation.

    Reference: designs/2026-04-19-binding-frames-lean-semantics.md, 4.1 -/
theorem loadSlot_bindSlot_same (lineage : Nat) (slots : List Value) (slot : Nat)
    (v : Value) (hv : slot < slots.length) :
    loadSlot (.frame lineage (slots.set slot v)) slot = some v := by
  simp only [loadSlot]
  exact List_get?_set_eq_self slots slot v hv

-- =================================================================
-- 4.2 loadSlot_bindSlot_other: non-interference
-- =================================================================

/-- Writing a slot does not affect reads at any other slot.

    This is the non-interference law for frame slots: BindSlot at
    slot k commutes (in observation) with LoadSlot at any distinct
    slot j. Justifies hoisting a LoadSlot above an independent
    BindSlot during scheduling.

    Reference: designs/2026-04-19-binding-frames-lean-semantics.md, 4.2 -/
theorem loadSlot_bindSlot_other (lineage : Nat) (slots : List Value) (k j : Nat)
    (v : Value) (hne : k ≠ j) :
    loadSlot (.frame lineage (slots.set k v)) j = loadSlot (.frame lineage slots) j := by
  simp only [loadSlot]
  exact List_get?_set_ne_self slots k j v hne

-- =================================================================
-- 4.3 openFrame_closeFrame_state: non-interference with memory
-- =================================================================

/-- Opening a fresh binding frame and immediately closing it leaves
    memory, permissions, and refcounts untouched. The SSA counter and frame-lineage counter each grow by one; the new
    lineage is closed. Allocation requires room in the UInt64 identity space.

    This is the key "binding frames do not interact with the heap"
    property called out in TrustIr#32 and section 4.3 of the design doc.
    Stated as an existential on the resulting state, because opening
    allocates a fresh ValueId so s'.locals and s'.nextValueId differ
    from s.

    Reference: designs/2026-04-19-binding-frames-lean-semantics.md, 4.3 -/
theorem openFrame_closeFrame_state
    (def_ : BindingFrameDef) (s : MachineState) (room : s.nextFrameLineage < 2^64-1) :
    ∃ s',
      Sem.run (do let id ← semOpenFrame def_; semCloseFrame id) s
        = .ok ((), s') ∧
      s'.memory = s.memory ∧
      s'.permissions = s.permissions ∧
      s'.refCounts = s.refCounts := by
  let final := { s with
    locals := s.locals.set ⟨s.nextValueId⟩ (initFrame s.nextFrameLineage def_.slots),
    nextValueId := s.nextValueId+1,
    openFrameLineages := (s.nextFrameLineage :: s.openFrameLineages).filter (fun id => id != s.nextFrameLineage),
    nextFrameLineage := s.nextFrameLineage+1 }
  refine ⟨final, ?_, rfl, rfl, rfl⟩
  simp [semOpenFrame, semCloseFrame, Sem.setFrameState, Sem.frameHandle, room, initFrame,
    Sem.run, Sem.getState, Sem.setState, Sem.bindFresh, Sem.lookupValue, Sem.rejectPartial,
    StateT.run, StateT.bind, StateT.get, StateT.set, StateT.pure, StateT.lift,
    MachineState.bindValue, MachineState.lookupValue, ValueMap.get, ValueMap.set, final,
    bind, pure, Except.bind, Except.pure]

-- =================================================================
-- 4.4 bindSlot_bindSlot_commute_different_slots: independent-slot
--     reordering
-- =================================================================

/-- Two BindSlot operations at distinct slots commute.

    Justifies reordering independent BindSlots during frame
    construction. Stated on the raw List.set representation because
    that is what matters for the algebraic law -- the bindSlot
    wrapper just threads bounds checks, which are independent of
    ordering.

    Reference: designs/2026-04-19-binding-frames-lean-semantics.md, 4.4 -/
theorem bindSlot_bindSlot_commute_different_slots
    (slots : List Value) (k j : Nat) (u v : Value) (hne : k ≠ j) :
    (slots.set k u).set j v = (slots.set j v).set k u :=
  List_set_comm_of_ne slots k j u v hne

/-! Runtime lifetime laws and closed kernel traces. These exercise actual
monadic operations, including snapshot aliases and error precedence; they
are separate from the pure slot algebra above. No native evaluation axiom. -/
namespace FrameLifetime
theorem closed_frame_load (s : MachineState) (id : ValueId) (lineage slot : Nat)
    (slots : List Value) (ty : Ty)
    (lookup : s.lookupValue id = some (.frame lineage slots))
    (closed : s.openFrameLineages.contains lineage = false) :
    Sem.run (semLoadSlot id slot ty) s = .error (.ub "LoadSlot: frame is not open") := by
  first
  | simp [semLoadSlot, Sem.frameHandle, Sem.run, Sem.lookupValue, Sem.rejectPartial,
      Sem.getState, Sem.throwUB, lookup, closed, StateT.run, StateT.bind,
      StateT.get, StateT.pure, StateT.lift, bind, pure, Except.bind, Except.pure]
    rfl
  | have notOpen : lineage ∉ s.openFrameLineages := by simpa using closed
    simp [semLoadSlot, Sem.frameHandle, Sem.run, Sem.lookupValue, Sem.rejectPartial,
      Sem.getState, Sem.throwUB, lookup, closed, notOpen, StateT.run, StateT.bind,
      StateT.get, StateT.pure, StateT.lift, bind, pure, Except.bind, Except.pure] <;> rfl

theorem closed_frame_bind (s : MachineState) (id rhs : ValueId) (lineage slot : Nat)
    (slots : List Value)
    (lookup : s.lookupValue id = some (.frame lineage slots))
    (closed : s.openFrameLineages.contains lineage = false) :
    Sem.run (semBindSlot id slot rhs) s = .error (.ub "BindSlot: frame is not open") := by
  first
  | simp [semBindSlot, Sem.frameHandle, Sem.run, Sem.lookupValue, Sem.rejectPartial,
      Sem.getState, Sem.throwUB, lookup, closed, StateT.run, StateT.bind,
      StateT.get, StateT.pure, StateT.lift, bind, pure, Except.bind, Except.pure]
    rfl
  | have notOpen : lineage ∉ s.openFrameLineages := by simpa using closed
    simp [semBindSlot, Sem.frameHandle, Sem.run, Sem.lookupValue, Sem.rejectPartial,
      Sem.getState, Sem.throwUB, lookup, closed, notOpen, StateT.run, StateT.bind,
      StateT.get, StateT.pure, StateT.lift, bind, pure, Except.bind, Except.pure] <;> rfl

theorem closed_frame_close (s : MachineState) (id : ValueId) (lineage : Nat)
    (slots : List Value)
    (lookup : s.lookupValue id = some (.frame lineage slots))
    (closed : s.openFrameLineages.contains lineage = false) :
    Sem.run (semCloseFrame id) s = .error (.ub "CloseFrame: frame is not open (double close)") := by
  first
  | simp [semCloseFrame, Sem.frameHandle, Sem.run, Sem.lookupValue, Sem.rejectPartial,
      Sem.getState, Sem.throwUB, lookup, closed, StateT.run, StateT.bind,
      StateT.get, StateT.pure, StateT.lift, bind, pure, Except.bind, Except.pure]
    rfl
  | have notOpen : lineage ∉ s.openFrameLineages := by simpa using closed
    simp [semCloseFrame, Sem.frameHandle, Sem.run, Sem.lookupValue, Sem.rejectPartial,
      Sem.getState, Sem.throwUB, lookup, closed, notOpen, StateT.run, StateT.bind,
      StateT.get, StateT.pure, StateT.lift, bind, pure, Except.bind, Except.pure] <;> rfl

private def frameDef : BindingFrameDef := ⟨⟨0⟩, "lifetime", [⟨"slot", .I32⟩]⟩
private def probe {α : Type} (program : Sem α) : Except SemError α :=
  (Sem.run program MachineState.empty).map Prod.fst

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem close_old_invalidates_new :
    probe (do
      let old ← semOpenFrame frameDef
      let value ← Sem.bindFresh (.int 32 7)
      let newer ← semBindSlot old 0 value
      semCloseFrame old
      semLoadSlot newer 0 .I32) = .error (.ub "LoadSlot: frame is not open") := by rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem close_new_invalidates_old :
    probe (do
      let old ← semOpenFrame frameDef
      let value ← Sem.bindFresh (.int 32 7)
      let newer ← semBindSlot old 0 value
      semCloseFrame newer
      semLoadSlot old 0 .I32) = .error (.ub "LoadSlot: frame is not open") := by rfl

theorem restoreFrame_preserves_lineage (s : MachineState) (frame : StackFrame) (ret : List Value) :
    (restoreFrame s frame ret).openFrameLineages = s.openFrameLineages ∧
    (restoreFrame s frame ret).nextFrameLineage = s.nextFrameLineage := by
  unfold restoreFrame
  split <;> exact ⟨rfl, rfl⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem snapshots_remain_functional :
    probe (do
      let old ← semOpenFrame frameDef
      let value ← Sem.bindFresh (.int 32 7)
      let newer ← semBindSlot old 0 value
      let before ← semLoadSlot old 0 .I32
      let after ← semLoadSlot newer 0 .I32
      let a ← Sem.lookupValue before
      let b ← Sem.lookupValue after
      pure (a, b)) = .ok (.undef .I32, .int 32 7) := by rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem reopen_does_not_revive_old :
    probe (do
      let old ← semOpenFrame frameDef
      semCloseFrame old
      let _ ← semOpenFrame frameDef
      semLoadSlot old 0 .I32) = .error (.ub "LoadSlot: frame is not open") := by rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem copy_alias_double_close :
    probe (do
      let old ← semOpenFrame frameDef
      let value ← Sem.lookupValue old
      let copy ← Sem.bindFresh value
      semCloseFrame copy
      semCloseFrame old) = .error (.ub "CloseFrame: frame is not open (double close)") := by rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem closing_one_keeps_other_open :
    probe (do
      let first ← semOpenFrame frameDef
      let second ← semOpenFrame frameDef
      semCloseFrame first
      let value ← semLoadSlot second 0 .I32
      Sem.lookupValue value) = .ok (.undef .I32) := by rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem closed_bind_precedes_missing_rhs_and_bounds :
    probe (do
      let old ← semOpenFrame frameDef
      semCloseFrame old
      semBindSlot old 99 ⟨999⟩) = .error (.ub "BindSlot: frame is not open") := by rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem lineage_counter_overflow :
    (Sem.run (semOpenFrame frameDef)
      { MachineState.empty with nextFrameLineage := 2^64-1 }).map Prod.fst =
        .error (.ub "OpenFrame: frame id overflow") := by rfl


end FrameLifetime

end TrustIr
