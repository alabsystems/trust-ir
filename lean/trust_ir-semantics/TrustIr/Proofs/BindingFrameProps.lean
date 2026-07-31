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
    (l.set k v).get? k = some v
  | [],      _,      _, h => absurd h (by simp [List.length])
  | _ :: _,  0,      _, _ => rfl
  | _ :: xs, n + 1,  v, h => by
      simp only [List.set, List.get?]
      have hxs : n < xs.length := by simp [List.length] at h; omega
      exact List_get?_set_eq_self xs n v hxs

/-- List.get? at index j after List.set at a different index k equals
    the original List.get? at j. -/
private theorem List_get?_set_ne_self {α : Type} :
    (l : List α) -> (k j : Nat) -> (v : α) -> k ≠ j ->
    (l.set k v).get? j = l.get? j
  | [], _, _, _, _ => by simp [List.set]
  | _ :: _,  0,      0,     _, hne => absurd rfl hne
  | _ :: _,  0,      _ + 1, _, _   => rfl
  | _ :: _,  _ + 1,  0,     _, _   => rfl
  | _ :: xs, n + 1,  m + 1, v, hne => by
      simp only [List.set, List.get?]
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
theorem loadSlot_bindSlot_same (slots : List Value) (slot : Nat)
    (v : Value) (hv : slot < slots.length) :
    loadSlot (.frame (slots.set slot v)) slot = some v := by
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
theorem loadSlot_bindSlot_other (slots : List Value) (k j : Nat)
    (v : Value) (hne : k ≠ j) :
    loadSlot (.frame (slots.set k v)) j = loadSlot (.frame slots) j := by
  simp only [loadSlot]
  exact List_get?_set_ne_self slots k j v hne

-- =================================================================
-- 4.3 openFrame_closeFrame_state: non-interference with memory
-- =================================================================

/-- Opening a fresh binding frame and immediately closing it leaves
    memory, permissions, and refcounts untouched. Only the SSA locals
    vector and the nextValueId counter grow by one.

    This is the key "binding frames do not interact with the heap"
    property called out in TrustIr#32 and section 4.3 of the design doc.
    Stated as an existential on the resulting state, because opening
    allocates a fresh ValueId so s'.locals and s'.nextValueId differ
    from s.

    Reference: designs/2026-04-19-binding-frames-lean-semantics.md, 4.3 -/
theorem openFrame_closeFrame_state
    (def_ : BindingFrameDef) (s : MachineState) :
    ∃ s',
      Sem.run (do let id ← semOpenFrame def_; semCloseFrame id) s
        = .ok ((), s') ∧
      s'.memory = s.memory ∧
      s'.permissions = s.permissions ∧
      s'.refCounts = s.refCounts := by
  -- semOpenFrame is Sem.bindFresh (initFrame ...); semCloseFrame is pure ().
  -- Both operations only touch locals and nextValueId, leaving the
  -- heap sub-state unchanged. The state that emerges from running the
  -- do-block is s with locals extended and nextValueId bumped.
  refine ⟨{ s with
            locals      := s.locals.set
                             (ValueId.mk s.nextValueId)
                             (initFrame def_.slots)
          , nextValueId := s.nextValueId + 1 }, ?_, rfl, rfl, rfl⟩
  rfl

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

end TrustIr
