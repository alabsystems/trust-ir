-- Copyright 2026 Andrew Yates | Apache-2.0
-- Foundational finite-reference and frame laws for the UInt32 leaf runtime.
-- No HostCalls, native implementation axiom, codegen license or G4 claim.
-- This proves the reference-occurrence algebra, NOT refinement of Rust/ABI bytes.
namespace CleanUInt32Ownership

/-- Consume one owned reference per occurrence. Zero remaining means retirement;
    a request beyond the actual references is an error, never saturating success.
    For ordinary Clean cells initial refs = raw_header_rc + 1. -/
def consume : Nat → Nat → Option Nat
  | 0, refs => some refs
  | _ + 1, 0 => none
  | n + 1, refs + 1 => consume n refs

/-- All aliased input occurrences need their own transferred reference. -/
theorem consume_sufficient (occurrences external : Nat) :
    consume occurrences (occurrences + external) = some external := by
  induction occurrences with
  | zero => simp [consume]
  | succ n ih => simpa [consume, Nat.succ_add] using ih

/-- Even one excess alias is refused. This is the UAF/double-release control. -/
theorem consume_excess (refs extra : Nat) :
    consume (refs + extra + 1) refs = none := by
  induction refs with
  | zero => simp [consume]
  | succ n ih => simpa [consume, Nat.succ_add] using ih

/-- Last-reference retirement and an unrelated owner are distinct outcomes. -/
theorem consume_all_and_external (n external : Nat) :
    consume n (n + external) = some external ∧ consume n n = some 0 := by
  constructor
  · exact consume_sufficient n external
  · simpa using consume_sufficient n 0

abbrev Heap := Nat → Option Nat

/-- Ordinary (not sticky) leaf drop; count is raw RC = logical refs - 1.
    Missing cells are outside valid-release admission. No child traversal is
    needed for the exact Ctor(0 children, 4 scalar bytes) UInt32 layout. -/
def dropFinite (heap : Heap) (address : Nat) : Heap :=
  fun probe => if probe = address then
    match heap address with
    | none => none
    | some 0 => none
    | some (n + 1) => some n
  else heap probe

def drops (heap : Heap) (address : Nat) : Nat → Heap
  | 0 => heap
  | n + 1 => drops (dropFinite heap address) address n

/-- Every prefix of repeated alias drops preserves every unrelated cell. -/
theorem drop_frame (heap : Heap) (address probe n : Nat) (h : probe ≠ address) :
    drops heap address n probe = heap probe := by
  induction n generalizing heap with
  | zero => simp [drops]
  | succ n ih =>
    rw [drops, ih]
    simp [dropFinite, h]

/-- Exact raw-count relation after n valid ordinary drops, with at least one
    external reference left; unlike a whole-world equality this permits RC writes. -/
theorem drop_alias_count (heap : Heap) (address n external : Nat)
    (h : heap address = some (n + external)) :
    drops heap address n address = some external := by
  induction n generalizing heap with
  | zero => simpa [drops] using h
  | succ n ih =>
    apply ih
    simp [dropFinite, h, Nat.succ_add]

/-- n+1 occurrences consume exactly raw_rc=n plus its implicit first reference. -/
theorem drop_last_alias (heap : Heap) (address n : Nat)
    (h : heap address = some n) :
    drops heap address (n + 1) address = none := by
  induction n generalizing heap with
  | zero => simp [drops, dropFinite, h]
  | succ n ih =>
    apply ih
    simp [dropFinite, h]

end CleanUInt32Ownership

namespace CleanUInt32Ownership

/-- The source runtime's actual sticky-drop threshold. -/
def stickyDrop : Nat := 0xE0000000

def dropSticky (heap : Heap) (address : Nat) : Heap :=
  match heap address with
  | none => heap
  | some rc => if stickyDrop ≤ rc then heap else dropFinite heap address

def dropsSticky (heap : Heap) (address : Nat) : Nat → Heap
  | 0 => heap
  | n + 1 => dropsSticky (dropSticky heap address) address n

/-- Frozen RC cells remain live and byte-unmodified for any finite number of
    valid owned occurrences; consume still limits ghost ownership separately. -/
theorem frozen_releases (heap : Heap) (address rc n : Nat)
    (h : heap address = some rc) (frozen : stickyDrop ≤ rc) :
    dropsSticky heap address n = heap := by
  induction n with
  | zero => simp [dropsSticky]
  | succ n ih => simpa [dropsSticky, dropSticky, h, frozen] using ih

/-- Canonical pointer64 UInt32 encoder arithmetic; Rust bounds n by u32::MAX. -/
def encodeTagged (n : Nat) : Nat := n * 2 + 1

theorem tagged_roundtrip (n : Nat) : encodeTagged n / 2 = n := by
  simpa [encodeTagged, Nat.add_comm] using
    Nat.add_mul_div_right 1 n (by decide : 0 < 2)

end CleanUInt32Ownership
