-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Mechanical axiom-boundary gate.
--
-- The TrustIr trust boundary claims (HANDOFF.md, docs/roadmap/README.md) that
-- there is exactly ONE first-party axiom — `ay_sound_unsat` (ay is trusted to be
-- sound on `unsat`) — beyond the Lean-core trio `propext` / `Classical.choice` /
-- `Quot.sound`. These `#guard_msgs`-wrapped `#print axioms` commands turn that
-- claim into a build-enforced check: if any proof below later starts depending
-- on a NEW axiom (or a proof placeholder, which surfaces as `sorryAx`), `lake build` fails
-- here with a message mismatch. Imported by `TrustIr.lean`, so the gate runs on
-- every build.
--
-- If a message below changes, do NOT just update the expected string — first
-- confirm the new axiom dependency is intended. A `sorryAx` appearing here is a
-- regression, never an acceptable update.

import TrustIr.Proofs.AYBridge
import TrustIr.Proofs.TransformCorrectness
import TrustIr.Proofs.MemorySafety
import TrustIr.Proofs.VectorDialectProps
import TrustIr.Proofs.AggregateProps
import TrustIr.Proofs.PredLatticeProps

namespace TrustIr
namespace AxiomAudit

open TrustIr.VectorDialect

-- The AY soundness bridge: its SOLE first-party axiom is `ay_sound_unsat`.
/-- info: 'TrustIr.ay_sound_contrapositive' depends on axioms: [propext, TrustIr.ay_sound_unsat] -/
#guard_msgs in
#print axioms ay_sound_contrapositive

-- DCE correctness: no first-party axiom (Lean-core trio only).
/-- info: 'TrustIr.dce_pure_inst' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms dce_pure_inst

-- The four formerly-axiomatized theorems are genuine proofs: Lean-core trio only,
-- NO `ay_sound_unsat`, NO `sorryAx`.
/-- info: 'TrustIr.semStore_characterize' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms semStore_characterize

/-- info: 'TrustIr.load_after_store_program' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms load_after_store_program

-- B2 dealloc lifecycle (dead-marking + double-free UB): Lean-core trio only.
/-- info: 'TrustIr.semDealloc_marks_dead' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms semDealloc_marks_dead

/-- info: 'TrustIr.semDealloc_twice_is_ub' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms semDealloc_twice_is_ub

-- Heap-lifetime UB ratification (docs/ub-numerics-policy.md §6): the
-- double-free / use-after-free / ARC-underflow theorems are plain `rfl`
-- computations over the executable semantics — Lean-core axioms at most
-- (semLoad unfolds through well-founded-recursion helpers, pulling in
-- propext/Quot.sound), and in particular NOT native_decide's
-- Lean.ofReduceBool and NOT ay_sound_unsat.
/-- info: 'TrustIr.semDealloc_twice_is_ub_example' does not depend on any axioms -/
#guard_msgs in
#print axioms semDealloc_twice_is_ub_example

/-- info: 'TrustIr.semLoad_after_dealloc_is_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms semLoad_after_dealloc_is_ub

/-- info: 'TrustIr.semRelease_after_last_release_is_ub' does not depend on any axioms -/
#guard_msgs in
#print axioms semRelease_after_last_release_is_ub

-- P1 CleanHeap origin: the IR→memory-model mapping lock and the
-- origins-are-provenance parity backbone are definitional (`rfl`) — no axioms.
/-- info: 'TrustIr.cleanHeap_toAllocationOrigin' does not depend on any axioms -/
#guard_msgs in
#print axioms cleanHeap_toAllocationOrigin

/-- info: 'TrustIr.alloc_isInBounds_ignores_origin' does not depend on any axioms -/
#guard_msgs in
#print axioms alloc_isInBounds_ignores_origin

/-- info: 'TrustIr.VectorDialect.runsAgreeFrom_pack_lanes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runsAgreeFrom_pack_lanes

/-- info: 'TrustIr.VectorDialect.runsAgreeFrom_mask_to_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runsAgreeFrom_mask_to_bits

-- B5 bridge + transfer: the evaluator's Call handling IS runCallReq
-- (terminator branch verbatim; body branch composed with bindResultDests),
-- and the ProofContext postcondition transfer holds over the real evaluator.
-- Lean-core trio only — NO `ay_sound_unsat`, NO `sorryAx`.
/-- info: 'TrustIr.stepNWithContext_callReq_eq_runCallReq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepNWithContext_callReq_eq_runCallReq

/-- info: 'TrustIr.stepNWithContext_bodyCall_eq_runCallReq_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepNWithContext_bodyCall_eq_runCallReq_bind

/-- info: 'TrustIr.proof_context_assume_sound_evaluator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms proof_context_assume_sound_evaluator

-- B5/EH Invoke bridge + transfer: the evaluator's InvokeReq branch IS
-- runInvokeCall composed with the invoke node's result binding, the
-- normal-edge argument evaluation, and the normal-edge continuation; the
-- ProofContext postcondition transfer holds for the Invoke path over the
-- real evaluator. Lean-core trio only — NO `ay_sound_unsat`, NO `sorryAx`.
/-- info: 'TrustIr.stepNWithContext_invokeReq_eq_runInvokeCall_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepNWithContext_invokeReq_eq_runInvokeCall_bind

/-- info: 'TrustIr.proof_context_assume_sound_invoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms proof_context_assume_sound_invoke

/-- info: 'TrustIr.proof_context_assume_sound_invoke_evaluator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms proof_context_assume_sound_invoke_evaluator

-- Inlining correctness (frame-discipline form): Lean-core trio only.
/-- info: 'TrustIr.inlining_preserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inlining_preserving

-- Give-back loop-instruction round-trip laws (the listMap_roundTrip /
-- boolNotLoop_roundTrip counterparts at the operational layer): Lean-core
-- trio only.
/-- info: 'TrustIr.seqMapAddKList_roundTrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms seqMapAddKList_roundTrip

-- (This proof's elaboration no longer touches Classical.choice / Quot.sound
-- — the dependency set SHRANK to a subset of the Lean-core trio, which is
-- always acceptable.)
/-- info: 'TrustIr.seqMapNotList_involutive' depends on axioms: [propext] -/
#guard_msgs in
#print axioms seqMapNotList_involutive

-- B3 depth ledger "Fat-pointer values": the fat-pointer decompose/recombine
-- round trip, at the value level and over the Sem-monad semantics of the
-- PtrData / PtrMetadata / PtrFromParts trio. Lean-core axioms only.
/-- info: 'TrustIr.fatPtr_roundTrip_value' does not depend on any axioms -/
#guard_msgs in
#print axioms fatPtr_roundTrip_value

/-- info: 'TrustIr.semFatPtr_roundTrip' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms semFatPtr_roundTrip

-- fast-4 cross-lane refinements: genuine proofs, Lean-core trio only.
/-- info: 'TrustIr.VectorDialect.runsAgreeFrom_reduce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runsAgreeFrom_reduce

/-- info: 'TrustIr.VectorDialect.runsAgreeFrom_shuffle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms runsAgreeFrom_shuffle

/-- info: 'TrustIr.VectorDialect.vectorLowerFrom_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms vectorLowerFrom_sound

-- ───────────────────────────────────────────────────────────────────────────
-- G5: the PREDICATE LATTICE soundness proofs (TrustIr/Proofs/PredLatticeProps).
--
-- BUDGET CLAIM: these add NO first-party axiom. They are structural induction
-- plus `omega`/`simp`; there is no `axiom`, no proof placeholder, and no
-- `native_decide`
-- (hence no `Lean.ofReduceBool`), and in particular no `ay_sound_unsat` — the
-- lattice is solver-free by construction, which is the whole point of it being
-- decidable in microseconds.
--
-- The expected messages below are observed from the checked proofs. The ONLY
-- acceptable outcome remains a subset of the Lean-core trio [propext,
-- Classical.choice, Quot.sound]. A `sorryAx` is a regression;
-- `TrustIr.ay_sound_unsat` appearing here would mean the lattice had acquired
-- a solver dependency and must be investigated, never absorbed.
/-- info: 'TrustIr.implies_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms implies_sound

/-- info: 'TrustIr.join_upper_bound_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms join_upper_bound_left

/-- info: 'TrustIr.join_upper_bound_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms join_upper_bound_right

/-- info: 'TrustIr.denote_Top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms denote_Top

/-- info: 'TrustIr.top_certifies_only_trivia' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms top_certifies_only_trivia

/-- info: 'TrustIr.index_never_implies_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms index_never_implies_member

end AxiomAudit
end TrustIr
