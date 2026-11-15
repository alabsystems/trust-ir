-- Copyright 2026 Andrew Yates
-- Licensed under the Apache License, Version 2.0

import TrustIr.Proofs.ByteMemory

/-! Canonical allocation/layout facts shared by the 4.8 reference package and
SemR's 4.30 memory embedding. These are the existing MemoryProps definitions
and theorem statements, factored without changing the allocator or memory
semantics. The two list-inversion helpers use proof syntax accepted by both
versions. No new axiom, evaluator or compiler authority is introduced.
-/

namespace TrustIr

/-- The fresh allocation record `Memory.alloc` pushes (the head of the
    allocation list). -/
def Memory.allocRecord (mem : Memory) (size align slack : Nat) (origin : AllocationOrigin) :
    Allocation :=
  { id := AllocId.mk mem.nextAllocId, base := alignUp mem.nextAddr align
  , size := size + slack, alive := true, origin := origin, requested := size }

/-- `Memory.alloc` places the allocation at the next free address rounded up
    to `align` (the interpreter's `align_addr(next_addr, align)`). -/
theorem alloc_addr_is_aligned_nextAddr (mem : Memory) (size align slack : Nat)
    (origin : AllocationOrigin) :
    (mem.alloc size align slack origin).fst = alignUp mem.nextAddr align := by
  unfold Memory.alloc; split <;> rfl

/-- `Memory.alloc` pushes exactly its fresh record onto the allocation list
    (the slack fill writes bytes only). -/
theorem alloc_allocations (mem : Memory) (size align slack : Nat) (origin : AllocationOrigin) :
    (mem.alloc size align slack origin).snd.allocations
      = mem.allocRecord size align slack origin :: mem.allocations := by
  unfold Memory.alloc
  split <;> simp [Memory.allocRecord]

/-- `Memory.alloc` advances `nextAddr` past the new allocation's footprint,
    by one byte for a zero-size one (the interpreter's `footprint.max(1)`). -/
theorem alloc_advances_nextAddr (mem : Memory) (size align slack : Nat)
    (origin : AllocationOrigin) :
    (mem.alloc size align slack origin).snd.nextAddr
      = alignUp mem.nextAddr align + max (size + slack) 1 := by
  unfold Memory.alloc
  split <;> simp

/-- Memory.alloc increments the allocation ID counter. -/
theorem alloc_increments_allocId (mem : Memory) (size align slack : Nat)
    (origin : AllocationOrigin) :
    (mem.alloc size align slack origin).snd.nextAllocId = mem.nextAllocId + 1 := by
  unfold Memory.alloc
  split <;> simp

/-- Memory.alloc adds exactly one allocation to the list. -/
theorem alloc_adds_one_allocation (mem : Memory) (size align slack : Nat)
    (origin : AllocationOrigin) :
    (mem.alloc size align slack origin).snd.allocations.length = mem.allocations.length + 1 := by
  rw [alloc_allocations]; rfl

/-- The fresh allocation from Memory.alloc is alive. -/
theorem alloc_is_alive (mem : Memory) (size align slack : Nat) (origin : AllocationOrigin) :
    match (mem.alloc size align slack origin).snd.allocations with
    | alloc :: _ => alloc.alive = true
    | [] => False := by
  rw [alloc_allocations]; rfl

/-- `alignUp n a` is at least `n`. -/
theorem le_alignUp (n a : Nat) : n ≤ alignUp n a := by
  unfold alignUp
  split
  · exact Nat.le_refl n
  · rename_i h
    have ha : 0 < a := Nat.pos_of_ne_zero (by simpa using h)
    have h1 := Nat.div_add_mod (n + a - 1) a
    have h2 := Nat.mod_lt (n + a - 1) ha
    rw [Nat.mul_comm]
    generalize (n + a - 1) / a = q at *
    generalize (n + a - 1) % a = r at *
    generalize a * q = m at *
    omega

/-- `alignUp n a` is a multiple of `a`. -/
theorem alignUp_mod (n a : Nat) (ha : a ≠ 0) : alignUp n a % a = 0 := by
  unfold alignUp
  simp [ha, Nat.mul_mod_left]

/-- In the initial empty memory, nextAddr is 1024 (null page reserve).
    Combined with `alloc_addr_is_aligned_nextAddr` and `le_alignUp`, this
    proves an allocation never has base 0. -/
theorem empty_memory_nextAddr :
    Memory.empty.nextAddr = 1024 := by
  simp [Memory.empty]

/-- Allocation on empty memory produces a non-null address. -/
theorem alloc_on_empty_is_nonzero (size align slack : Nat) (origin : AllocationOrigin) :
    (Memory.empty.alloc size align slack origin).fst > 0 := by
  rw [alloc_addr_is_aligned_nextAddr]
  exact Nat.lt_of_lt_of_le (by decide) (le_alignUp Memory.empty.nextAddr align)

-- =================================================================
-- Allocation origins are provenance, not discipline (P1 CleanHeap)
-- =================================================================

/-- The IR→memory-model origin mapping sends Clean's Perceus RC origin to
    `cleanHeap` — the mapping lock for `AllocOrigin.CleanHeap` (the Rust
    binary codec's origin byte 3). -/
theorem cleanHeap_toAllocationOrigin :
    AllocOrigin.CleanHeap.toAllocationOrigin = AllocationOrigin.cleanHeap := rfl

/-- Origins are provenance, not discipline: the origin tag never affects
    which accesses an allocation admits. In particular a `cleanHeap` cell
    and its `swiftHeap` twin accept exactly the same in-bounds accesses —
    the symbolic backbone of the executable cleanHeap/swiftHeap refcount
    parity fixtures (`ExecutableFixtures.lean`). No operational rule
    matches on `AllocationOrigin`; ARC ops gate on `Permission.arcRef` and
    `semDealloc` on `Permission.canDealloc`. -/
theorem alloc_isInBounds_ignores_origin (mem : Memory) (size align slack : Nat)
    (o₁ o₂ : AllocationOrigin) (addr : Addr) (n : Nat) :
    (mem.alloc size align slack o₁).snd.isInBounds addr n
      = (mem.alloc size align slack o₂).snd.isInBounds addr n := by
  simp only [Memory.isInBounds, alloc_allocations, Memory.allocRecord, List.any_cons]

/-- Origin-irrelevance of liveness: same statement for `isAllocated`. -/
theorem alloc_isAllocated_ignores_origin (mem : Memory) (size align slack : Nat)
    (o₁ o₂ : AllocationOrigin) (addr : Addr) :
    (mem.alloc size align slack o₁).snd.isAllocated addr
      = (mem.alloc size align slack o₂).snd.isAllocated addr := by
  simp only [Memory.isAllocated, alloc_allocations, Memory.allocRecord, List.any_cons]


theorem find?_some_pred {α : Type _} {p : α → Bool} {l : List α} {a : α}
    (h : l.find? p = some a) : p a = true := by
  induction l with
  | nil => simp [List.find?] at h
  | cons x xs ih =>
    rw [List.find?_cons] at h
    cases hx : p x
    · rw [hx] at h; exact ih h
    · rw [hx] at h
      simp only [Option.some.injEq] at h
      exact h ▸ hx

theorem mem_of_find?_some {α : Type _} {p : α → Bool} {l : List α} {a : α}
    (h : l.find? p = some a) : a ∈ l := by
  induction l with
  | nil => simp [List.find?] at h
  | cons x xs ih =>
    rw [List.find?_cons] at h
    cases hx : p x
    · rw [hx] at h; exact List.mem_cons_of_mem x (ih h)
    · rw [hx] at h
      simp only [Option.some.injEq] at h
      exact h ▸ (by simp)

/-- `omega` over `Addr`: Lean 4.8's `omega` does not see through the `Addr`
    abbreviation, so unfold it first. -/
local macro "addr_omega" : tactic => `(tactic| ((try simp only [Addr] at *) <;> omega))

/-- The reference placement's layout invariant: allocation ids are below
    `nextAllocId` and name one record; every allocation's footprint — at
    least one byte, as the bump makes a zero-size one — lies below
    `nextAddr`, and two different allocations' footprints are disjoint; an
    allocation's requested bytes lie inside its footprint. ("Ends before
    `x`" is `base + size ≤ x ∧ base < x`: the footprint `[base, base + max
    size 1)`.) -/
def Memory.layoutWF (mem : Memory) : Prop :=
  (∀ a ∈ mem.allocations, a.id.id < mem.nextAllocId) ∧
  (∀ a ∈ mem.allocations, ∀ b ∈ mem.allocations, a.id = b.id → a = b) ∧
  (∀ a ∈ mem.allocations, a.base + a.size ≤ mem.nextAddr ∧ a.base < mem.nextAddr) ∧
  (∀ a ∈ mem.allocations, ∀ b ∈ mem.allocations, a ≠ b →
    (a.base + a.size ≤ b.base ∧ a.base < b.base) ∨
    (b.base + b.size ≤ a.base ∧ b.base < a.base)) ∧
  (∀ a ∈ mem.allocations, a.requested ≤ a.size)

theorem empty_layoutWF : Memory.empty.layoutWF := by
  simp [Memory.layoutWF, Memory.empty]

/-- `Memory.alloc` keeps the layout invariant: the fresh allocation gets a
    fresh id and starts at or above every footprint already placed. -/
theorem alloc_preserves_layoutWF (mem : Memory) (size align slack : Nat)
    (origin : AllocationOrigin) (h : mem.layoutWF) :
    (mem.alloc size align slack origin).snd.layoutWF := by
  obtain ⟨hId, hUniq, hBelow, hDisj, hReq⟩ := h
  have hAllocs := alloc_allocations mem size align slack origin
  have hNext := alloc_advances_nextAddr mem size align slack origin
  have hNextId := alloc_increments_allocId mem size align slack origin
  have hBase := le_alignUp mem.nextAddr align
  have hm1 : size + slack ≤ max (size + slack) 1 := Nat.le_max_left _ _
  have hm2 : 1 ≤ max (size + slack) 1 := Nat.le_max_right _ _
  have hRecBase : (mem.allocRecord size align slack origin).base = alignUp mem.nextAddr align := rfl
  have hRecSize : (mem.allocRecord size align slack origin).size = size + slack := rfl
  have hRecId : (mem.allocRecord size align slack origin).id = ⟨mem.nextAllocId⟩ := rfl
  generalize max (size + slack) 1 = m at hNext hm1 hm2
  generalize alignUp mem.nextAddr align = base at hBase hNext hRecBase
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hAllocs] at ha; rw [hNextId]
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [hRecId]; exact Nat.lt_succ_self _
    · have := hId a ha; addr_omega
  · intro a ha b hb hab
    rw [hAllocs] at ha hb
    rcases List.mem_cons.mp ha with rfl | ha <;> rcases List.mem_cons.mp hb with rfl | hb
    · rfl
    · have := hId b hb; rw [← hab, hRecId] at this; exact absurd this (Nat.lt_irrefl _)
    · have := hId a ha; rw [hab, hRecId] at this; exact absurd this (Nat.lt_irrefl _)
    · exact hUniq a ha b hb hab
  · intro a ha
    rw [hAllocs] at ha; rw [hNext]
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [hRecBase, hRecSize]; exact ⟨by addr_omega, by addr_omega⟩
    · obtain ⟨h1, h2⟩ := hBelow a ha; exact ⟨by addr_omega, by addr_omega⟩
  · intro a ha b hb hab
    rw [hAllocs] at ha hb
    rcases List.mem_cons.mp ha with rfl | ha <;> rcases List.mem_cons.mp hb with rfl | hb
    · exact absurd rfl hab
    · right; obtain ⟨h1, h2⟩ := hBelow b hb; rw [hRecBase]; exact ⟨by addr_omega, by addr_omega⟩
    · left; obtain ⟨h1, h2⟩ := hBelow a ha; rw [hRecBase]; exact ⟨by addr_omega, by addr_omega⟩
    · exact hDisj a ha b hb hab
  · intro a ha
    rw [hAllocs] at ha
    rcases List.mem_cons.mp ha with rfl | ha
    · show size ≤ size + slack; addr_omega
    · exact hReq a ha

/-- `Memory.alloc` places its allocation at a multiple of `align` (the
    interpreter's `align_addr`). -/
theorem alloc_base_aligned (mem : Memory) (size align slack : Nat) (origin : AllocationOrigin)
    (ha : align ≠ 0) : (mem.alloc size align slack origin).fst % align = 0 := by
  rw [alloc_addr_is_aligned_nextAddr]
  exact alignUp_mod _ _ ha

end TrustIr
