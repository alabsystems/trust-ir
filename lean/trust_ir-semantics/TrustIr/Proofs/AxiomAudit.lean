import TrustIr.Proofs.BlockCheckCompletenessControls
import TrustIr.Proofs.StoreImageReadbackControls
import TrustIr.Proofs.ScalarLoadExecutionControls
import TrustIr.Proofs.AggregateLoadExecutionControls
import TrustIr.Proofs.LoadInstructionControls
import TrustIr.Proofs.StoreInstructionControls
import TrustIr.Proofs.AggregateStoreExecutionControls
import TrustIr.Proofs.UnwrittenOverwriteControls
import TrustIr.Proofs.UnwrittenImageBoundsControls
import TrustIr.Proofs.OrdinaryImageMetadataControls
import TrustIr.Proofs.VectorReadbackControls
import TrustIr.Proofs.FloatStorageControls
import TrustIr.Proofs.SourceReadbackPolicyControls
import TrustIr.Proofs.SourceStructAdmissionControls
import TrustIr.Proofs.SourceCheckedAdmissionControls
import TrustIr.Proofs.ScalarAdmissionControls
import TrustIr.Proofs.EncodedAdmissionControls
import TrustIr.Proofs.FunctionReadbackControls
import TrustIr.Proofs.SourceRecursiveReadback
import TrustIr.Proofs.SourceIntegerReadback
import TrustIr.Proofs.SourcePreparedReferences
import TrustIr.Proofs.SourceLayoutReferenceBounds
import TrustIr.Proofs.SourceLayoutRootFrontier
import TrustIr.Proofs.SourceLayoutClosedRegions
import TrustIr.Proofs.SourceLayoutArrayOrigin
import TrustIr.Proofs.SourceLayoutDeterminism
import TrustIr.Proofs.SourceArrayLaneControls
import TrustIr.Proofs.SourcePlanKinds
import TrustIr.Proofs.SourceArrayIdentity
import TrustIr.Proofs.SourceArrayCoverage
import TrustIr.Proofs.SourceSiblingGeometry
import TrustIr.Proofs.SourceFieldSteps
import TrustIr.Proofs.SourceLeafCoverage
import TrustIr.Proofs.SourceByteCoverage
import TrustIr.Proofs.SourceFieldCoherence
import TrustIr.Proofs.SourceFieldBindings
import TrustIr.Proofs.SourceEnumImage
import TrustIr.Proofs.SourceEnumDecode
import TrustIr.Proofs.SourceEnumCodec
import TrustIr.Proofs.SourceEnumPlan
import TrustIr.Proofs.SourceEnumGraph
import TrustIr.Proofs.SourceEnumOmission
import TrustIr.Proofs.SourceEnumAdmission
import TrustIr.Proofs.SourceEnumPayload
import TrustIr.Proofs.SourceInhabitSound
import TrustIr.Proofs.SourceNodeMeaning
import TrustIr.Proofs.SourceValueMembership
import TrustIr.Proofs.SourceLayoutCombinators
import TrustIr.Proofs.SourceLayoutSession
import TrustIr.Proofs.SourceLayoutDerivation
import TrustIr.Proofs.SourceLayoutBounds
import TrustIr.Proofs.TargetWidthDefinition
import TrustIr.Proofs.DecodedFrameEntry
import TrustIr.Proofs.FrameCoroExits
import TrustIr.Proofs.FrameStaticExits
import TrustIr.Proofs.FrameInstructionAdmission
import TrustIr.Proofs.ConstantFrameValues
import TrustIr.Proofs.FrameConstantPublication
import TrustIr.Proofs.FrameGlobalExits
import TrustIr.Proofs.ConstantContextEquations
import TrustIr.Proofs.FrameConstantExits
import TrustIr.Proofs.FrameSeqMapExits
import TrustIr.Proofs.FrameSequenceRecursion
import TrustIr.Proofs.FrameMemoryRecursion
import TrustIr.Proofs.FrameWorldUpdates
import TrustIr.Proofs.FrameBulkMemoryExits
import TrustIr.Proofs.FrameOwnershipExits
import TrustIr.Proofs.FrameAggregateDecoding
import TrustIr.Proofs.FrameAggregateLoads
import TrustIr.Proofs.FrameMemoryEncoding
import TrustIr.Proofs.FrameAggregateStores
import TrustIr.Proofs.FrameAtomicScalarExits
import TrustIr.Proofs.FrameAtomicExits
import TrustIr.Proofs.FrameAllocationExits
import TrustIr.Proofs.FrameGEPExits
import TrustIr.Proofs.FrameBlockDecoding
import TrustIr.Proofs.FrameMemoryLoads
import TrustIr.Proofs.FrameMemoryDecodeExits
import TrustIr.Proofs.FrameTerminalRecursion
import TrustIr.Proofs.FrameTerminalExits
import TrustIr.Proofs.FrameUnwindRecursion
import TrustIr.Proofs.FrameAssertInvokeExits
import TrustIr.Proofs.FrameExceptionalExits
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

import TrustIr.Proofs.FrameLifetimeProps
import TrustIr.Proofs.FrameValueValidity
import TrustIr.Proofs.FrameSlotValidity
import TrustIr.Proofs.FrameAliasValidity
import TrustIr.Proofs.FrameUnaryValidity
import TrustIr.Proofs.FrameBinaryValidity
import TrustIr.Proofs.FrameComparisonValidity
import TrustIr.Proofs.FrameCastValidity
import TrustIr.Proofs.FrameAggregateValidity
import TrustIr.Proofs.FrameConstructionValidity
import TrustIr.Proofs.FrameFieldValidity
import TrustIr.Proofs.FramePointerValidity
import TrustIr.Proofs.FrameCollectionValidity
import TrustIr.Proofs.FrameResultValidity
import TrustIr.Proofs.FrameBodyValidity
import TrustIr.Proofs.FrameTransferValidity
import TrustIr.Proofs.FrameHistoryEffects
import TrustIr.Proofs.FrameExecutionHistory
import TrustIr.Proofs.FrameDirectCalls
import TrustIr.Proofs.FrameCheckedCalls
import TrustIr.Proofs.FrameIndirectCalls
import TrustIr.Proofs.FrameTailBoundary
import TrustIr.Proofs.FrameTailRecursion
import TrustIr.Proofs.FrameAllTailCalls
import TrustIr.Proofs.FrameInvokeBoundary
import TrustIr.Proofs.FrameInvokeExits
import TrustIr.Proofs.FrameActionExits
import TrustIr.Proofs.FrameCallExits
import TrustIr.Proofs.FrameContextSafety
import TrustIr.Proofs.FramePublicationExits
import TrustIr.Proofs.FrameDirectBodyExits
import TrustIr.Proofs.FrameControlExits
import TrustIr.Proofs.FrameInvokeTransfers
import TrustIr.Proofs.FrameIndirectInvokeExits
import TrustIr.Proofs.FrameClosureExits
import TrustIr.Proofs.FrameIndirectBodyExits
import TrustIr.Proofs.FrameScalarExits
import TrustIr.Proofs.FrameScalarActions
import TrustIr.Proofs.FrameCastExits
import TrustIr.Proofs.FrameBodyExits
import TrustIr.Proofs.FrameAggregateChecks
import TrustIr.Proofs.FrameAggregateActions
import TrustIr.Proofs.FrameGrammarExits
import TrustIr.Proofs.FrameRecursiveExits
import TrustIr.Proofs.AYWordPermutation
import TrustIr.Proofs.AYPermutationTarget
import TrustIr.Proofs.AYPermutationInstruction
import TrustIr.Proofs.AYPopulationCount
import TrustIr.Proofs.AYPopulationInstruction
import TrustIr.Proofs.AYPopulationGates
import TrustIr.Proofs.AYZeroCountTarget
import TrustIr.Proofs.AYZeroCountInstruction
import TrustIr.Proofs.AYZeroCountGates
import TrustIr.Proofs.AYUnaryBody
import TrustIr.Proofs.AYUnaryReplay
import TrustIr.Proofs.AYUnaryReturnBlock
import TrustIr.Proofs.AYUnaryCFGReplay
import TrustIr.Proofs.AYUnaryEntryReplay
import TrustIr.Proofs.AYDecodedEntryReplay
import TrustIr.Proofs.AYBridge
import TrustIr.Proofs.SourceLayoutAxiomAudit
import TrustIr.Proofs.AggregateImageAxiomAudit
import TrustIr.Proofs.TransformCorrectness
import TrustIr.Proofs.TransformRefinementCtx
import TrustIr.Proofs.ProgramRefinement
import TrustIr.Proofs.FloatChoiceRefinement
import TrustIr.Proofs.MemorySafety
import TrustIr.Proofs.PointerObservationProps
import TrustIr.Proofs.HostPointerProps
import TrustIr.Proofs.FunctionMemoryProps
import TrustIr.Proofs.BorrowMemoryProps
import TrustIr.Proofs.VectorDialectProps
import TrustIr.Proofs.VectorLaneProps
import TrustIr.Proofs.LocalTypeProps
import TrustIr.Proofs.AggregateProps
import TrustIr.Proofs.AggregateContextProps
import TrustIr.Proofs.PredLatticeProps
import TrustIr.Proofs.MetaTheorems
import TrustIr.Proofs.ArithProps
import TrustIr.Proofs.AtomicProps
import TrustIr.Proofs.CoroutineProps
import TrustIr.Proofs.SSACharProps
import TrustIr.Proofs.HeldMemoryFrames
import TrustIr.Proofs.SSAFreshFrames
import TrustIr.Proofs.SSAFreshStep
import TrustIr.Proofs.SSAFreshInstructions
import TrustIr.Proofs.SSAFreshMemory
import TrustIr.Proofs.SSAFreshOwnership
import TrustIr.Proofs.SSAFreshAtomic
import TrustIr.Proofs.SSAFreshMemoryExtra
import TrustIr.Proofs.SSAFreshDispatch
import TrustIr.Proofs.SSAFreshContext
import TrustIr.Proofs.SSAFreshAggregate
import TrustIr.Proofs.SSAFreshUnwindBody
import TrustIr.Proofs.SSAFreshLoops
import TrustIr.Proofs.GenericCoroCell
import TrustIr.Proofs.GenericCoroInvoke
import TrustIr.Proofs.GenericCoroTermContext
import TrustIr.Proofs.GenericCoroProps
import TrustIr.Proofs.GenericCoroControls
import TrustIr.Proofs.LocalTypeInferenceProps
import TrustIr.Semantics.NatIndex
import TrustIr.Proofs.NatIndexProps
import TrustIr.Proofs.DropProps
import TrustIr.Proofs.UnwindProps
import TrustIr.Proofs.TemplateProps
import TrustIr.Proofs.ClosureProps
import TrustIr.Proofs.GenericCoroPrefixCorrect
import TrustIr.Proofs.GenericCoroPrefixProofControls
import TrustIr.Proofs.GenericCoroPrefixControls
import TrustIr.Proofs.GenericCoroAllBlocksCorrect
import TrustIr.Proofs.GenericCoroAllBlocksControls
import TrustIr.Proofs.GenericCoroAllBlocksProofControls

namespace TrustIr
namespace AxiomAudit

-- Symbolic function-memory words use the existing byte arithmetic and an
-- immutable source-order table. These are kernel proofs, not native images.
/-- info: 'TrustIr.functionAddressIndex_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.functionAddressIndex_spec

/-- info: 'TrustIr.encodeFunctionWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.encodeFunctionWord

/-- info: 'TrustIr.decodeFunctionWord' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.decodeFunctionWord

/-- info: 'TrustIr.functionTargetAt_unregistered' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.functionTargetAt_unregistered

/-- info: 'TrustIr.constValueAtWithDefs_withFunctionOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.constValueAtWithDefs_withFunctionOrder

/-- info: 'TrustIr.functionOrder_mapFunctionCFGs' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.functionOrder_mapFunctionCFGs

/-- info: 'TrustIr.functionCall_signature_mismatch' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.functionCall_signature_mismatch

/-- info: 'TrustIr.const_function_retains_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.const_function_retains_identity

open TrustIr.VectorDialect

-- Bool ICmp is checked by exhaustive kernel reduction, not a native oracle.
/-- info: 'TrustIr.semBoolICmp_truth_table' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.semBoolICmp_truth_table

-- The AY soundness bridge: its SOLE first-party axiom is `ay_sound_unsat`.
/-- info: 'TrustIr.ay_sound_contrapositive' depends on axioms: [propext, TrustIr.ay_sound_unsat] -/
#guard_msgs in
#print axioms TrustIr.ay_sound_contrapositive

-- Semantic decoding and its controls must not depend on the solver oracle.
/-- info: 'TrustIr.ay_equiv_implies_inst_equiv' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.ay_equiv_implies_inst_equiv

/-- info: 'TrustIr.unreachable_encoding_faithful' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.unreachable_encoding_faithful

/-- info: 'TrustIr.unreachable_error_decoder_refused' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.unreachable_error_decoder_refused

-- DCE correctness: no first-party axiom (Lean-core trio only).
/-- info: 'TrustIr.dce_pure_inst' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.dce_pure_inst

-- The four formerly-axiomatized theorems are genuine proofs: Lean-core trio only,
-- NO `ay_sound_unsat`, NO `sorryAx`.
-- Typed-vector encoding now checks integer lane widths with the existing
-- `Ty.bitWidth`, whose axiom census includes `Classical.choice`. This reaches
-- `semStore` and dependent theorem types, including scalar examples below.
-- Their exact guards retain only the same permitted Lean-core trio.
/-- info: 'TrustIr.semStore_characterize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semStore_characterize

/-- info: 'TrustIr.load_after_store_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.load_after_store_program

-- WS3.7 (F-047, memory half): the sealed handle slot round trip is an
-- instance of the byte-level load-after-store lemma at the handle width —
-- Lean-core trio only, no first-party axiom.
/-- info: 'TrustIr.load_store_roundtrip_handle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.load_store_roundtrip_handle

-- Borrow address resolution: existing invariant proofs and the actual
-- allocation/borrow/memory compositions use Lean-core axioms only.
/-- info: 'TrustIr.borrow_preserves_stack' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.borrow_preserves_stack

/-- info: 'TrustIr.borrow_mut_preserves_stack' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.borrow_mut_preserves_stack

/-- info: 'TrustIr.end_borrow_preserves_stack' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.end_borrow_preserves_stack

/-- info: 'TrustIr.BorrowMemoryProps.alloca_store_borrow_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.BorrowMemoryProps.alloca_store_borrow_load

/-- info: 'TrustIr.BorrowMemoryProps.alloca_borrow_mut_store_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.BorrowMemoryProps.alloca_borrow_mut_store_load

/-- info: 'TrustIr.BorrowMemoryProps.shared_reborrow_and_end_preserve_address' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.BorrowMemoryProps.shared_reborrow_and_end_preserve_address

/-- info: 'TrustIr.BorrowMemoryProps.interior_borrow_keeps_offset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.BorrowMemoryProps.interior_borrow_keeps_offset

-- A Rust reference carries no permission instruction (docs/SPEC_RATIFICATIONS.md):
-- the two permission-machine faults and the Copy step's frame property, stated
-- for every state and peeled with the sr_* helpers. Lean-core axioms at most;
-- no native_decide (Lean.ofReduceBool) and no ay_sound_unsat.
/-- info: 'TrustIr.BorrowMemoryProps.semBorrow_ub_of_uniqueBorrow' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.BorrowMemoryProps.semBorrow_ub_of_uniqueBorrow

/-- info: 'TrustIr.BorrowMemoryProps.semBorrowMut_ub_of_not_owned' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.BorrowMemoryProps.semBorrowMut_ub_of_not_owned

/-- info: 'TrustIr.BorrowMemoryProps.stepInst_copy_preserves_memory_and_permissions' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.BorrowMemoryProps.stepInst_copy_preserves_memory_and_permissions

-- B2 dealloc lifecycle (dead-marking + double-free UB): Lean-core trio only.
/-- info: 'TrustIr.semDealloc_marks_dead' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.semDealloc_marks_dead

/-- info: 'TrustIr.semDealloc_twice_is_ub' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.semDealloc_twice_is_ub

-- Heap-lifetime UB ratification (docs/ub-numerics-policy.md §6): the
-- double-free / use-after-free / ARC-underflow theorems are plain `rfl`
-- computations over the executable semantics — Lean-core axioms at most
-- (semLoad unfolds through well-founded-recursion helpers, pulling in
-- propext/Quot.sound), and in particular NOT native_decide's
-- Lean.ofReduceBool and NOT ay_sound_unsat.
/-- info: 'TrustIr.semDealloc_twice_is_ub_example' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.semDealloc_twice_is_ub_example

/-- info: 'TrustIr.semLoad_after_dealloc_is_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semLoad_after_dealloc_is_ub

/-- info: 'TrustIr.semRelease_after_last_release_is_ub' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.semRelease_after_last_release_is_ub

-- A reference-counted cell is released by `Release`, never by `Dealloc`
-- (docs/SPEC_RATIFICATIONS.md): the general arcRef theorem peels semDealloc
-- with the sr_* helpers (Lean-core trio); the concrete CleanHeap / SwiftHeap
-- instances are axiom-free `rfl` computations; the positive Release twin runs
-- semLoad (its well-founded helpers pull in propext / Quot.sound). None uses
-- native_decide's Lean.ofReduceBool or ay_sound_unsat.
/-- info: 'TrustIr.semDealloc_arcRef_is_ub' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.semDealloc_arcRef_is_ub

/-- info: 'TrustIr.semDealloc_cleanHeap_is_ub_example' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.semDealloc_cleanHeap_is_ub_example

/-- info: 'TrustIr.semDealloc_swiftHeap_is_ub_example' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.semDealloc_swiftHeap_is_ub_example

/-- info: 'TrustIr.semRelease_cleanHeap_after_store_load_ok_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semRelease_cleanHeap_after_store_load_ok_example

-- An ARC operation counts only a reference-counted cell
-- (docs/SPEC_RATIFICATIONS.md): `requireArcRef_non_arcRef_is_ub` is a case
-- split with no axiom; the three general theorems peel the op with the sr_*
-- helpers, whose `simp` rewriting uses propext; the four concrete instances
-- (stack, RustHeap, CMalloc, global reservation) and the address-model pin
-- `retain_one_past_rustHeap_counts_neighbour` are axiom-free `rfl`
-- computations. None uses native_decide's Lean.ofReduceBool or ay_sound_unsat.
/-- info: 'TrustIr.requireArcRef_non_arcRef_is_ub' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.requireArcRef_non_arcRef_is_ub

/-- info: 'TrustIr.semRetain_non_arcRef_is_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.semRetain_non_arcRef_is_ub

/-- info: 'TrustIr.semRelease_non_arcRef_is_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.semRelease_non_arcRef_is_ub

/-- info: 'TrustIr.semIsUnique_non_arcRef_is_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.semIsUnique_non_arcRef_is_ub

/-- info: 'TrustIr.semRetain_alloca_is_ub_example' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.semRetain_alloca_is_ub_example

/-- info: 'TrustIr.semRelease_rustHeap_is_ub_example' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.semRelease_rustHeap_is_ub_example

/-- info: 'TrustIr.semIsUnique_cMalloc_is_ub_example' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.semIsUnique_cMalloc_is_ub_example

/-- info: 'TrustIr.semRetain_globalAddr_is_ub_example' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.semRetain_globalAddr_is_ub_example

/-- info: 'TrustIr.retain_one_past_rustHeap_is_ub_and_spares_neighbour' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.retain_one_past_rustHeap_is_ub_and_spares_neighbour

-- An ARC operand names its cell's object base (SPEC "An ARC operation
-- counts only a reference-counted cell", clause 3, decided 2026-09-30).

/-- info: 'TrustIr.requireObjectBase_off_base_is_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.requireObjectBase_off_base_is_ub

/-- info: 'TrustIr.semRetain_interior_is_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semRetain_interior_is_ub

/-- info: 'TrustIr.semRelease_interior_is_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semRelease_interior_is_ub

/-- info: 'TrustIr.semIsUnique_interior_is_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semIsUnique_interior_is_ub

/-- info: 'TrustIr.retain_interior_of_cleanHeap_is_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.retain_interior_of_cleanHeap_is_ub

/-- info: 'TrustIr.release_one_past_cleanHeap_is_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.release_one_past_cleanHeap_is_ub

/-- info: 'TrustIr.isUnique_past_slack_of_cleanHeap_is_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.isUnique_past_slack_of_cleanHeap_is_ub

/-- info: 'TrustIr.arc_at_object_base_ok_example' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.arc_at_object_base_ok_example

-- Freeing an allocation under a live borrow is undefined behaviour
-- (docs/SPEC_RATIFICATIONS.md): the general borrow-state theorem peels
-- semDealloc with the sr_* helpers (Lean-core trio); the five concrete
-- instances and the two decided provenance families
-- (`borrow_one_past_moves_no_permission_and_neighbour_frees`,
-- `double_endBorrow_one_past_keeps_neighbour_borrow`) are axiom-free `rfl`
-- computations. None uses native_decide's Lean.ofReduceBool or ay_sound_unsat.
/-- info: 'TrustIr.semDealloc_borrowed_is_ub' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.semDealloc_borrowed_is_ub

/-- info: 'TrustIr.semDealloc_under_borrow_is_ub_example' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.semDealloc_under_borrow_is_ub_example

/-- info: 'TrustIr.semDealloc_under_borrowMut_is_ub_example' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.semDealloc_under_borrowMut_is_ub_example

/-- info: 'TrustIr.semDealloc_under_interior_borrow_is_ub_example' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semDealloc_under_interior_borrow_is_ub_example

/-- info: 'TrustIr.semDealloc_one_of_two_borrows_live_is_ub_example' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.semDealloc_one_of_two_borrows_live_is_ub_example

/-- info: 'TrustIr.semDealloc_after_every_endBorrow_ok_example' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.semDealloc_after_every_endBorrow_ok_example

/-- info: 'TrustIr.borrow_one_past_moves_no_permission_and_neighbour_frees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.borrow_one_past_moves_no_permission_and_neighbour_frees

/-- info: 'TrustIr.double_endBorrow_one_past_keeps_neighbour_borrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.double_endBorrow_one_past_keeps_neighbour_borrow

-- P1 CleanHeap origin: the IR→memory-model mapping lock and the
-- origins-are-provenance parity backbone are definitional (`rfl`) — no axioms.
/-- info: 'TrustIr.cleanHeap_toAllocationOrigin' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.cleanHeap_toAllocationOrigin

/-- info: 'TrustIr.alloc_isInBounds_ignores_origin' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.alloc_isInBounds_ignores_origin

/-- info: 'TrustIr.VectorDialect.runsAgreeFrom_pack_lanes' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.runsAgreeFrom_pack_lanes

/-- info: 'TrustIr.VectorDialect.runsAgreeFrom_mask_to_bits' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.runsAgreeFrom_mask_to_bits

-- B5 bridge + transfer: the evaluator's Call handling IS runCallReq
-- (terminator branch verbatim; body branch composed with bindResultDests),
-- and the ProofContext postcondition transfer holds over the real evaluator.
-- Lean-core trio only — NO `ay_sound_unsat`, NO `sorryAx`.
/-- info: 'TrustIr.stepNWithContext_callReq_eq_runCallReq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepNWithContext_callReq_eq_runCallReq

/-- info: 'TrustIr.stepNWithContext_bodyCall_eq_runCallReq_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepNWithContext_bodyCall_eq_runCallReq_bind

/-- info: 'TrustIr.proof_context_assume_sound_evaluator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.proof_context_assume_sound_evaluator

-- B5/EH Invoke bridge + transfer: the evaluator's InvokeReq branch IS
-- runInvokeCall composed with the invoke node's result binding, the
-- normal-edge argument evaluation, and the normal-edge continuation; the
-- ProofContext postcondition transfer holds for the Invoke path over the
-- real evaluator. Lean-core trio only — NO `ay_sound_unsat`, NO `sorryAx`.
/-- info: 'TrustIr.stepNWithContext_invokeReq_eq_runInvokeCall_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepNWithContext_invokeReq_eq_runInvokeCall_bind

/-- info: 'TrustIr.proof_context_assume_sound_invoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.proof_context_assume_sound_invoke

/-- info: 'TrustIr.proof_context_assume_sound_invoke_evaluator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.proof_context_assume_sound_invoke_evaluator

-- Inlining correctness (frame-discipline form): Lean-core trio only.
/-- info: 'TrustIr.inlining_preserving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.inlining_preserving

-- Give-back loop-instruction round-trip laws (the listMap_roundTrip /
-- boolNotLoop_roundTrip counterparts at the operational layer): Lean-core
-- trio only.
/-- info: 'TrustIr.seqMapAddKList_roundTrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.seqMapAddKList_roundTrip

-- (This proof's elaboration no longer touches Classical.choice / Quot.sound
-- — the dependency set SHRANK to a subset of the Lean-core trio, which is
-- always acceptable.)
/-- info: 'TrustIr.seqMapNotList_involutive' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.seqMapNotList_involutive

-- B3 depth ledger "Fat-pointer values": the fat-pointer decompose/recombine
-- round trip, at the value level and over the Sem-monad semantics of the
-- PtrData / PtrMetadata / PtrFromParts trio. Lean-core axioms only.
/-- info: 'TrustIr.fatPtr_roundTrip_value' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.fatPtr_roundTrip_value

/-- info: 'TrustIr.semFatPtr_roundTrip' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.semFatPtr_roundTrip

-- fast-4 cross-lane refinements: genuine proofs, Lean-core trio only.
/-- info: 'TrustIr.VectorDialect.runsAgreeFrom_reduce' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.runsAgreeFrom_reduce

/-- info: 'TrustIr.VectorDialect.runsAgreeFrom_shuffle' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.runsAgreeFrom_shuffle

/-- info: 'TrustIr.VectorDialect.vectorLowerFrom_sound' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.vectorLowerFrom_sound

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
#print axioms TrustIr.implies_sound

/-- info: 'TrustIr.join_upper_bound_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.join_upper_bound_left

/-- info: 'TrustIr.join_upper_bound_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.join_upper_bound_right

/-- info: 'TrustIr.denote_Top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.denote_Top

/-- info: 'TrustIr.top_certifies_only_trivia' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.top_certifies_only_trivia

/-- info: 'TrustIr.index_never_implies_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.index_never_implies_member

-- WS8.15 behaviour refinement (`TransformCorrectness.lean`): the refinement
-- theorems, the constant-fold instance, the negative twin and the mutation
-- controls (the `.ok`-only notions hold where refinement is refuted) all rest
-- on the Lean-core trio only. `sorryAx` or `ay_sound_unsat` here is a
-- regression.
/-- info: 'TrustIr.id_refines' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.id_refines

/-- info: 'TrustIr.compose_refines' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.compose_refines

/-- info: 'TrustIr.block_transform_lifts_to_cfg_refines' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.block_transform_lifts_to_cfg_refines

/-- info: 'TrustIr.constant_fold_refines' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.constant_fold_refines

/-- info: 'TrustIr.assertElim_semantics_preserving' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.assertElim_semantics_preserving

/-- info: 'TrustIr.assertElim_not_refines' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.assertElim_not_refines

/-- info: 'TrustIr.loop_not_refines' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.loop_not_refines

/-- info: 'TrustIr.panicToLoop_semantics_preserving_weak' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.panicToLoop_semantics_preserving_weak

/-- info: 'TrustIr.panicToLoop_not_refines' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.panicToLoop_not_refines

/-- info: 'TrustIr.ub_introduction_not_refines' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.ub_introduction_not_refines

/-- info: 'TrustIr.semantics_preserving_not_imp_refines' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.semantics_preserving_not_imp_refines

/-- info: 'TrustIr.inlining_error_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.inlining_error_transfer

-- WS8.15 adversarial review: divergence-to-return is accepted by the `.ok`-only
-- notion and refused by refinement, trap classes are distinguished, and the
-- UB-top ruling admits a UB-exploiting rewrite.
/-- info: 'TrustIr.divToRet_semantics_preserving' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.divToRet_semantics_preserving

/-- info: 'TrustIr.divToRet_not_refines' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.divToRet_not_refines

/-- info: 'TrustIr.trapClass_not_refines' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.trapClass_not_refines

/-- info: 'TrustIr.unreachableToReturn_refines' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.unreachableToReturn_refines

-- WS8.15 (remainder): behaviour refinement with calls executed
-- (`TransformRefinementCtx.lean`), at the Lean-core trio.
/-- info: 'TrustIr.behavesIn_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.behavesIn_nonempty

/-- info: 'TrustIr.id_refines_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.id_refines_in

/-- info: 'TrustIr.compose_refines_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.compose_refines_in

/-- info: 'TrustIr.stepNWithContext_unreachableToReturn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepNWithContext_unreachableToReturn

/-- info: 'TrustIr.unreachableToReturn_refines_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.unreachableToReturn_refines_in

/-- info: 'TrustIr.stepNWithContext_mapUnreachableToReturn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepNWithContext_mapUnreachableToReturn

/-- info: 'TrustIr.evalFunctionInContext_mapUnreachableToReturn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.evalFunctionInContext_mapUnreachableToReturn

/-- info: 'TrustIr.unreachableToReturn_program_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.unreachableToReturn_program_refines

/-- info: 'TrustIr.inlining_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.inlining_outcome

/-- info: 'TrustIr.inlining_behaves_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.inlining_behaves_iff

/-- info: 'TrustIr.assertElim_not_refines_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.assertElim_not_refines_in

/-- info: 'TrustIr.callRetarget_refines' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.callRetarget_refines

/-- info: 'TrustIr.callRetarget_not_refines_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.callRetarget_not_refines_in

/-- info: 'TrustIr.behaviour_refines_not_imp_refines_in' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.behaviour_refines_not_imp_refines_in

/-- info: 'TrustIr.behavesFn_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.behavesFn_nonempty

/-- info: 'TrustIr.compose_program_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.compose_program_refines

/-- info: 'TrustIr.withMaxCallDepth_program_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.withMaxCallDepth_program_refines

/-- info: 'TrustIr.callProgram_zero_budget_runs_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.callProgram_zero_budget_runs_out

-- WS8.15 review: divergence and recursion controls with calls executed.
/-- info: 'TrustIr.loop_not_refines_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.loop_not_refines_in

/-- info: 'TrustIr.recursion_not_refines_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.recursion_not_refines_in

/-- info: 'TrustIr.panicToLoop_not_refines_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.panicToLoop_not_refines_in

/-- info: 'TrustIr.withMaxCallDepth_not_fixedDepth_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.withMaxCallDepth_not_fixedDepth_refines


-- WS2.18: the fail-closed refusal of a link-time `symbolAddr` constant, and
-- the seed lemmas that thread its absence through the vector lowering.
/-- info: 'TrustIr.const_symbolAddr_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.const_symbolAddr_refused

/-- info: 'TrustIr.VectorDialect.seed_noSym_of_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.seed_noSym_of_lane

/-- info: 'TrustIr.VectorDialect.listHasSymbolAddr_replicate_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.listHasSymbolAddr_replicate_int

-- WS2.24 two-result binding: the unpacked `Overflow` / `CmpXchg` component
-- theorems carry no first-party axiom.
/-- info: 'TrustIr.Sem.bindFreshPair_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.Sem.bindFreshPair_ok

/-- info: 'TrustIr.semOverflow_binds_components' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semOverflow_binds_components

-- Factoring the exchange through typed codecs changes dependency traversal
-- order; the exact census still contains only the same three Lean-core axioms.
/-- info: 'TrustIr.semCmpXchg_binds_components' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.semCmpXchg_binds_components

-- Scalar Undef is poison (roadmap WS2.10): executing it succeeds, inspecting it is UB.
/-- info: 'TrustIr.undef_inspect_is_ub' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.undef_inspect_is_ub

/-- info: 'TrustIr.undef_binop_operand_is_ub' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.undef_binop_operand_is_ub

/-- info: 'TrustIr.undef_condbr_is_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.undef_condbr_is_ub

-- Coroutine controls now use the faithful held-value intrinsic and actual
-- finite source graphs. The false private-register macro/evaluator claims
-- are replaced by value composition and a concrete counterexample. The full
-- source-aware generic graph theorem remains an explicitly open follow-up.
/-- info: 'TrustIr.semGEP_endsFresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semGEP_endsFresh

/-- info: 'TrustIr.semCoroSuspend_bind_value_composition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semCoroSuspend_bind_value_composition

/-- info: 'TrustIr.semCoroSuspend_step_value_composition' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.semCoroSuspend_step_value_composition

/-- info: 'TrustIr.coro_private_spine_counterexample' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.coro_private_spine_counterexample

/-- info: 'TrustIr.CoroGen.coro_two_state_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.CoroGen.coro_two_state_roundtrip

/-- info: 'TrustIr.CoroGen.coro_two_state_mutant_traps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.CoroGen.coro_two_state_mutant_traps

/-- info: 'TrustIr.CoroGen.coro_two_state_roundtrip_mutant_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.CoroGen.coro_two_state_roundtrip_mutant_refuted

-- WS2.25 review controls: the SILENT `next - 1` mutant (second resume
-- succeeds but re-yields), the load-bearing initial-state hypothesis, and
-- the generator whose suspend state is the literal five-instruction
-- expansion — identical round trip for the correct operand wiring, refuted
-- for the mis-wired store that reads the slot immediate.
/-- info: 'TrustIr.CoroGen.coro_two_state_mutant_loops_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.CoroGen.coro_two_state_mutant_loops_refuted

/-- info: 'TrustIr.CoroGen.coro_two_state_from_state_one_never_yields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.CoroGen.coro_two_state_from_state_one_never_yields

/-- info: 'TrustIr.CoroGen.coro_two_state_roundtrip_expanded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.CoroGen.coro_two_state_roundtrip_expanded

/-- info: 'TrustIr.CoroGen.coro_two_state_roundtrip_miswired_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.CoroGen.coro_two_state_roundtrip_miswired_refuted

-- SPEC "A pointer operand names the allocation it was derived from": the
-- general provenance theorems (every state) and the decided cells (`rfl`
-- computations in the reference placement). Lean-core trio at most; none
-- uses native_decide's Lean.ofReduceBool or ay_sound_unsat.
/-- info: 'TrustIr.semAccess_names_provenance' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semAccess_names_provenance

/-- info: 'TrustIr.accessAddr_ok_of' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.accessAddr_ok_of

/-- info: 'TrustIr.expectPointer_ok_inv' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.expectPointer_ok_inv

/-- info: 'TrustIr.checkedAccess_ok_inv' depends on axioms: [Quot.sound, propext, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.checkedAccess_ok_inv

/-- info: 'TrustIr.checkedAccess_ok_of' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.checkedAccess_ok_of

/-- info: 'TrustIr.semBorrow_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semBorrow_frame

/-- info: 'TrustIr.semBorrowMut_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semBorrowMut_frame

/-- info: 'TrustIr.semEndBorrow_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.semEndBorrow_frame

/-- info: 'TrustIr.semBorrow_outside_requested_is_identity' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.semBorrow_outside_requested_is_identity

/-- info: 'TrustIr.semEndBorrow_outside_requested_is_noop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.semEndBorrow_outside_requested_is_noop

/-- info: 'TrustIr.semRetain_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semRetain_frame

/-- info: 'TrustIr.semRelease_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semRelease_frame

/-- info: 'TrustIr.semIsUnique_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semIsUnique_frame

/-- info: 'TrustIr.semDealloc_frees_its_provenance' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.semDealloc_frees_its_provenance

/-- info: 'TrustIr.addrOfInt_lt_two_pow_64' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.addrOfInt_lt_two_pow_64

/-- info: 'TrustIr.alloc_preserves_layoutWF' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.alloc_preserves_layoutWF

/-- info: 'TrustIr.alloc_base_aligned' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.alloc_base_aligned

/-- info: 'TrustIr.provenanceAt_inside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.provenanceAt_inside

/-- info: 'TrustIr.load_after_store_ptr_recovers_inside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.load_after_store_ptr_recovers_inside

/-- info: 'TrustIr.decode_encode_address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.decode_encode_address

/-- info: 'TrustIr.inttoptr_resolves_in_the_one_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.inttoptr_resolves_in_the_one_layout

/-- info: 'TrustIr.dealloc_zero_size_frees_itself' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.dealloc_zero_size_frees_itself

/-- info: 'TrustIr.dealloc_one_past_end_is_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.dealloc_one_past_end_is_ub

/-- info: 'TrustIr.aligned_store_after_byte_local_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.aligned_store_after_byte_local_ok

/-- info: 'TrustIr.load_one_past_end_is_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.load_one_past_end_is_ub

/-- info: 'TrustIr.load_misaligned_without_declared_align_is_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.load_misaligned_without_declared_align_is_ub

/-- info: 'TrustIr.gep_keeps_no_provenance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.gep_keeps_no_provenance

/-- info: 'TrustIr.inttoptr_negative_is_dangling_not_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.inttoptr_negative_is_dangling_not_null

/-- info: 'TrustIr.BorrowMemoryProps.one_past_address_moves_no_permission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.BorrowMemoryProps.one_past_address_moves_no_permission

/-- info: 'TrustIr.BorrowMemoryProps.dead_allocation_moves_no_permission' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.BorrowMemoryProps.dead_allocation_moves_no_permission

-- WS2.25 mutation control as an EXPECTED ELABORATION FAILURE (the roadmap's
-- Tests field): the round-trip statement for the scratch variant whose
-- `CoroSuspend` stores `next + 1` (`resume … 2 …`, the generator's second
-- state index written as 2 instead of 1), attacked with
-- `coro_two_state_roundtrip`'s own proof script, must NOT elaborate. The
-- first resume still goes through (the yield is not what the round trip
-- checks); the second resume's dispatch `rfl` — "state index 2 selects the
-- `1 → bb_final` case" — is false, and `#guard_msgs` pins exactly that
-- failure. An `example` never enters the environment, so the failed
-- declaration leaves no `sorryAx` behind it. The refutation THEOREM
-- `coro_two_state_roundtrip_mutant_refuted` above is the stronger,
-- environment-level form of the same control.
section CoroMutant
open TrustIr.CoroGen

/--
error: application type mismatch
  entry_run_case ctx 1 depth (Model.intrinsic 2) a fid (suspendExit s0 a fid 0 2 stateTwoBytes) stateTwoBytes 2 1
    bbFinal hFrame' hRead1 rfl rfl
argument
  rfl
has type
  matchSwitchCase (Value.int 64 2) entryCases = matchSwitchCase (Value.int 64 2) entryCases : Prop
but is expected to have type
  matchSwitchCase (Value.int 64 2) entryCases = some { value := Constant.int 1, target := bbFinal, args := [] } : Prop
-/
#guard_msgs in
example (ctx : EvalContext) (depth : Nat) (a : Addr) (fid : AllocId)
    (s0 : MachineState) (hFrame : FrameOk s0.memory a fid ctx.byteModel)
    (hZero : s0.memory.readBytes a 8 = some (List.replicate 8 0)) :
    resume ctx depth 2 a fid s0 = .ok ([yieldValue], suspendExit s0 a fid 0 2 stateTwoBytes) ∧
    resume ctx depth 2 a fid (suspendExit s0 a fid 0 2 stateTwoBytes)
      = .ok ([finalValue], finalExit (suspendExit s0 a fid 0 2 stateTwoBytes) a fid 2) := by
  have hFrame' : FrameOk (s0.memory.writeBytes a stateTwoBytes) a fid ctx.byteModel := hFrame
  have hRead1 : (s0.memory.writeBytes a stateTwoBytes).readBytes a 8 = some stateTwoBytes :=
    writeBytes_readBytes_general s0.memory a stateTwoBytes
  constructor
  · have h1 := entry_run_case ctx 1 depth (Model.intrinsic 2) a fid s0 (List.replicate 8 0) 0 0
      bbSuspend hFrame hZero rfl rfl
    have h2 := suspend_run ctx 0 depth 2 a fid s0 0 stateTwoBytes hFrame rfl rfl
    simp only [Nat.zero_add] at h2
    unfold resume resumeWith
    rw [show (2 : Nat) = 1 + 1 from rfl, h1, h2]
  · have h1 := entry_run_case ctx 1 depth (Model.intrinsic 2) a fid
      (suspendExit s0 a fid 0 2 stateTwoBytes) stateTwoBytes 2 1 bbFinal hFrame' hRead1 rfl rfl
    have h2 := final_run ctx 0 depth (Model.intrinsic 2) a fid (suspendExit s0 a fid 0 2 stateTwoBytes) 2
    simp only [Nat.zero_add] at h2
    unfold resume resumeWith
    rw [show (2 : Nat) = 1 + 1 from rfl, h1, h2]

end CoroMutant

-- Authoritative compact byte images: complete extents and pointwise reads.
/-- info: 'TrustIr.ByteStore.size_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteStore.size_snapshot

/-- info: 'TrustIr.ByteStore.get_snapshot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteStore.get_snapshot

/-- info: 'TrustIr.Memory.bytes_copyImage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.Memory.bytes_copyImage

/-- info: 'TrustIr.Memory.bytes_fillImage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.Memory.bytes_fillImage

/-- info: 'TrustIr.ByteImage.get_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.get_slice

/-- info: 'TrustIr.ByteImage.get_append' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.get_append

-- WS3.20 (F-057): the MemCopy byte-level contract.
/-- info: 'TrustIr.memcopy_preserves_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.memcopy_preserves_bytes

/-- info: 'TrustIr.memcopy_untouched_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.memcopy_untouched_below

-- v50: the uniform array. `ExtractElement i ∘ ArraySplat = v` for every `n`
-- (the replicated list is never enumerated), and its constant twin.
/-- info: 'TrustIr.extract_array_splat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.extract_array_splat

/-- info: 'TrustIr.getElement_ofConstant_splat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.getElement_ofConstant_splat

-- Amendment D (§20): a drop is a call of its type's glue. The resolution
-- lemmas, and the evaluator lift: running a CFG whose drops were rewritten
-- to calls of their glue IS running the original.
/-- info: 'TrustIr.resolveDrop_drop' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.resolveDrop_drop

/-- info: 'TrustIr.resolveDrop_dropInvoke' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.resolveDrop_dropInvoke

/-- info: 'TrustIr.resolveDrop_unresolved' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.resolveDrop_unresolved

/-- info: 'TrustIr.resolveDrop_idem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.resolveDrop_idem

/-- info: 'TrustIr.stepNWithContext_resolveDrops' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepNWithContext_resolveDrops

/-- info: 'TrustIr.drop_unresolved_is_unsupported' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.drop_unresolved_is_unsupported

/-- info: 'TrustIr.dropInvoke_unresolved_is_unsupported' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.dropInvoke_unresolved_is_unsupported

-- Amendment D, Part 2 (§21): unwinding as an exit. The abort run is a prefix
-- of the unwind run (the relational fuel induction), lifted to the entry as the
-- three abort-projection theorems; a plain call propagates an unwinding; Resume
-- re-raises; pad entry is blind to drop resolution (so the §20 evaluator lift
-- holds under both strategies).
/-- info: 'TrustIr.semEnterPad_resolveCfg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.semEnterPad_resolveCfg

/-- info: 'TrustIr.stepTermUnwind_resolveCfg' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.stepTermUnwind_resolveCfg

/-- info: 'TrustIr.stepNWithContext_abort_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepNWithContext_abort_prefix

/-- info: 'TrustIr.evalFunctionInContext_abort_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.evalFunctionInContext_abort_prefix

/-- info: 'TrustIr.abort_projection_normal_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.abort_projection_normal_exit

/-- info: 'TrustIr.abort_projection_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.abort_projection_ub

/-- info: 'TrustIr.abort_projection_out_of_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.abort_projection_out_of_fuel

/-- info: 'TrustIr.plain_call_propagates_unwinding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.plain_call_propagates_unwinding

/-- info: 'TrustIr.resume_reraises_in_hand_exception' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.resume_reraises_in_hand_exception

-- Amendment S (`docs/SPEC_RATIFICATIONS.md` §22): level-S substitution is
-- the identity on ground types and total on a scoped template; the drop
-- rewrite removes exactly the erased drops and commutes with drop resolution
-- when no erased type has a glue row. No first-party axiom.
/-- info: 'TrustIr.substTy_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.substTy_embed

/-- info: 'TrustIr.substTys_embeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.substTys_embeds

/-- info: 'TrustIr.substTy_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.substTy_total

/-- info: 'TrustIr.substTys_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.substTys_total

/-- info: 'TrustIr.substConst_embed' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.substConst_embed

/-- info: 'TrustIr.substConst_total' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.substConst_total

/-- info: 'TrustIr.eraseDrops_removes_erased' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.eraseDrops_removes_erased

/-- info: 'TrustIr.eraseDrops_terminator' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.eraseDrops_terminator

/-- info: 'TrustIr.eraseDrops_keeps_others' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.eraseDrops_keeps_others

/-- info: 'TrustIr.eraseTerminator_idem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.eraseTerminator_idem

/-- info: 'TrustIr.eraseDrops_body_idem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.eraseDrops_body_idem

/-- info: 'TrustIr.resolveBlock_eraseDrops_body' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.resolveBlock_eraseDrops_body

/-- info: 'TrustIr.resolveDrop_eraseTerminator' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.resolveDrop_eraseTerminator

/-- info: 'TrustIr.resolveBlock_eraseDropsBlock' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.resolveBlock_eraseDropsBlock

/-- info: 'TrustIr.resolveCfg_eraseDrops' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.resolveCfg_eraseDrops

-- Nominal closure contracts and the actual evaluator use only Lean-core axioms.
/-- info: 'TrustIr.closureTyEq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.closureTyEq_iff

/-- info: 'TrustIr.closureTyListEq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.closureTyListEq_iff

/-- info: 'TrustIr.checkClosureValue_ptr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.checkClosureValue_ptr

/-- info: 'TrustIr.makeClosureValue_of_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.makeClosureValue_of_checked

/-- info: 'TrustIr.stepInstWithContext_makeClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepInstWithContext_makeClosure

/-- info: 'TrustIr.closureCall_of_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.closureCall_of_checked

/-- info: 'TrustIr.closureInsert_of_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.closureInsert_of_checked

/-- info: 'TrustIr.closureExtract_of_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.closureExtract_of_checked

/-- info: 'TrustIr.evaluator_closure_preserves_pointer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.evaluator_closure_preserves_pointer

/-- info: 'TrustIr.evaluator_closure_preserves_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.evaluator_closure_preserves_memory

/-- info: 'TrustIr.evaluator_closure_update_preserves_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.evaluator_closure_update_preserves_original

/-- info: 'TrustIr.evaluator_closure_update_preserves_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.evaluator_closure_update_preserves_memory

/-- info: 'TrustIr.Sem.run_nextFloatZeroChoice' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.Sem.run_nextFloatZeroChoice

/-- info: 'TrustIr.semFloatMinMaxAt_permitted' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.semFloatMinMaxAt_permitted

/-- info: 'TrustIr.semFloatMinMaxAt_both_choices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semFloatMinMaxAt_both_choices

/-- info: 'TrustIr.program_refines_withFloatChoices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.program_refines_withFloatChoices

/-- info: 'TrustIr.unreachableToReturn_program_refinesWithFloatChoices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.unreachableToReturn_program_refinesWithFloatChoices

/-- info: 'TrustIr.minmax_encoding_refused' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.minmax_encoding_refused

-- General vector execution and the shared typed Bool boundary.

/-- info: 'TrustIr.executableVectorLaneValueMatches_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.executableVectorLaneValueMatches_check

/-- info: 'TrustIr.executableVectorLanePayloadMatches_member' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.executableVectorLanePayloadMatches_member

/-- info: 'TrustIr.executableVectorLanePayloadMatches_nonempty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.executableVectorLanePayloadMatches_nonempty

/-- info: 'TrustIr.executableVectorLanePayloadMatches_semantic' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.executableVectorLanePayloadMatches_semantic

/-- info: 'TrustIr.executableVectorPayloadMatches_shape' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.executableVectorPayloadMatches_shape

/-- info: 'TrustIr.executableVectorPayloadMatches_lanePayload' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.executableVectorPayloadMatches_lanePayload

/-- info: 'TrustIr.getVectorElement_of_executablePayload' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.getVectorElement_of_executablePayload

/-- info: 'TrustIr.setVectorElement_of_executablePayload' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.setVectorElement_of_executablePayload

/-- info: 'TrustIr.semVectorUnOp_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semVectorUnOp_length

/-- info: 'TrustIr.semVectorBinOp_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semVectorBinOp_length

/-- info: 'TrustIr.semUnOpValue_bool_not_replicate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semUnOpValue_bool_not_replicate

/-- info: 'TrustIr.semUnOpValue_zero_vector' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semUnOpValue_zero_vector

/-- info: 'TrustIr.checkVectorLaneType_undef_inspect' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.checkVectorLaneType_undef_inspect

/-- info: 'TrustIr.checkVectorLaneType_undef_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.checkVectorLaneType_undef_transport

/-- info: 'TrustIr.getVectorElement_bool_head' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.getVectorElement_bool_head

/-- info: 'TrustIr.setVectorElement_transports_unselected_poison' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.setVectorElement_transports_unselected_poison

/-- info: 'TrustIr.semBoolBinOp_conjunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.semBoolBinOp_conjunction

/-- info: 'TrustIr.semBoolBinOp_disjunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.semBoolBinOp_disjunction

/-- info: 'TrustIr.semBoolBinOp_exclusive_or' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.semBoolBinOp_exclusive_or

/-- info: 'TrustIr.semVectorBinOpLane_bool_agrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semVectorBinOpLane_bool_agrees

/-- info: 'TrustIr.semBinOpValues_bool_agrees' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.semBinOpValues_bool_agrees

/-- info: 'TrustIr.semBoolBinOpValues_int_refused' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.semBoolBinOpValues_int_refused

/-- info: 'TrustIr.semBoolBinOpValues_rhs_undef_priority' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.semBoolBinOpValues_rhs_undef_priority

/-- info: 'TrustIr.run_contextual_bool_binop_int_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.run_contextual_bool_binop_int_refused

-- State-local extraction domain and concrete kernel controls.

/-- info: 'TrustIr.VectorDialect.runsAgree_extract_lane' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.runsAgree_extract_lane

/-- info: 'TrustIr.VectorDialect.runsAgree_insert_lane' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.runsAgree_insert_lane

/-- info: 'TrustIr.VectorDialect.extract_lane_refinement_valid_state' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.extract_lane_refinement_valid_state

/-- info: 'TrustIr.VectorDialect.extract_lane_result_type_mismatch_refused' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.extract_lane_result_type_mismatch_refused

/-- info: 'TrustIr.VectorDialect.extract_lane_valid_state_instance' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.extract_lane_valid_state_instance

/-- info: 'TrustIr.VectorDialect.extract_lane_poison_state_instance' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.extract_lane_poison_state_instance

/-- info: 'TrustIr.VectorDialect.extract_lane_wrong_census_refused' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.extract_lane_wrong_census_refused

/-- info: 'TrustIr.VectorDialect.extract_lane_wrong_lane_type_agrees' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.extract_lane_wrong_lane_type_agrees

/-- info: 'TrustIr.VectorDialect.extract_lane_out_of_bounds_agrees' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.extract_lane_out_of_bounds_agrees

/-- info: 'TrustIr.VectorDialect.insert_lane_refinement_valid_state' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.insert_lane_refinement_valid_state

/-- info: 'TrustIr.VectorDialect.insert_lane_unselected_poison_transport' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.insert_lane_unselected_poison_transport

/-- info: 'TrustIr.VectorDialect.insert_lane_new_poison_refused' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.insert_lane_new_poison_refused

/-- info: 'TrustIr.VectorDialect.insert_lane_wrong_lane_type_refused' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.VectorDialect.insert_lane_wrong_lane_type_refused

-- Source-derived SSA metadata and typed integer consumers. These exact
-- guards retain only the existing Lean-core trust boundary.

/-- info: 'TrustIr.typedIntegerValue_i8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.typedIntegerValue_i8

/-- info: 'TrustIr.typedIntegerValue_u8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.typedIntegerValue_u8

/-- info: 'TrustIr.typedIntegerValue_negative_offset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.typedIntegerValue_negative_offset

/-- info: 'TrustIr.typed_signed_index_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.typed_signed_index_refused

/-- info: 'TrustIr.typed_unsigned_index_255' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.typed_unsigned_index_255

/-- info: 'TrustIr.typed_isize32_high_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.typed_isize32_high_bit

/-- info: 'TrustIr.typed_usize32_high_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.typed_usize32_high_bit

/-- info: 'TrustIr.typed_integer_width_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.typed_integer_width_refused

/-- info: 'TrustIr.typed_integer_poison_priority' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.typed_integer_poison_priority

/-- info: 'TrustIr.integerOperand_missing_metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.integerOperand_missing_metadata

/-- info: 'TrustIr.integerOperand_poison_before_metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.integerOperand_poison_before_metadata

/-- info: 'TrustIr.integerOperand_missing_declaration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.integerOperand_missing_declaration

/-- info: 'TrustIr.inferLocalTypes_source_producers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.inferLocalTypes_source_producers

/-- info: 'TrustIr.inferLocalTypes_fat_borrow_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.inferLocalTypes_fat_borrow_chain

/-- info: 'TrustIr.inferLocalTypes_thin_borrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.inferLocalTypes_thin_borrow

/-- info: 'TrustIr.inferLocalTypes_duplicate_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.inferLocalTypes_duplicate_refused

/-- info: 'TrustIr.inferLocalTypes_result_census_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.inferLocalTypes_result_census_refused

/-- info: 'TrustIr.inferLocalTypes_borrow_cycle_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.inferLocalTypes_borrow_cycle_refused

/-- info: 'TrustIr.localTypes_mapFunctionCFGs' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.localTypes_mapFunctionCFGs

/-- info: 'TrustIr.forFunction_mapFunctionCFGs' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.forFunction_mapFunctionCFGs

/-- info: 'TrustIr.integerOperand_mapFunctionCFGs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.integerOperand_mapFunctionCFGs

/-- info: 'TrustIr.elementIndex_mapFunctionCFGs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.elementIndex_mapFunctionCFGs


-- Top-level Char binding and source association, private-result retirement,
-- exact sparse index laws, and finite source-graph declarations. These are
-- kernel proofs; no native/checker or project axiom is added here.
/-- info: 'TrustIr.ssaChar_int_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ssaChar_int_success_iff

/-- info: 'TrustIr.ssaChar_width_independent' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ssaChar_width_independent

/-- info: 'TrustIr.ssaChar_non_integer_transport' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ssaChar_non_integer_transport

/-- info: 'TrustIr.ssaChar_other_type' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ssaChar_other_type

/-- info: 'TrustIr.ssaChar_poison_transport' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ssaChar_poison_transport

/-- info: 'TrustIr.ssaChar_partial_transport' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ssaChar_partial_transport

/-- info: 'TrustIr.ssaChar_uninit_transport' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ssaChar_uninit_transport

/-- info: 'TrustIr.ssaChar_aggregate_transport' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ssaChar_aggregate_transport

/-- info: 'TrustIr.ssaChar_valid_edges' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ssaChar_valid_edges

/-- info: 'TrustIr.ssaChar_invalid_edges' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ssaChar_invalid_edges

/-- info: 'TrustIr.ssaChar_u32_control' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ssaChar_u32_control

/-- info: 'TrustIr.ssaChar_mixed_top_level_only' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ssaChar_mixed_top_level_only

/-- info: 'TrustIr.ssaChar_block_parameter_valid' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ssaChar_block_parameter_valid

/-- info: 'TrustIr.ssaChar_block_parameter_invalid' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ssaChar_block_parameter_invalid

/-- info: 'TrustIr.ssaChar_block_arity_priority' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ssaChar_block_arity_priority

/-- info: 'TrustIr.ssaChar_manual_source_declaration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ssaChar_manual_source_declaration

/-- info: 'TrustIr.ssaChar_source_missing_destination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ssaChar_source_missing_destination

/-- info: 'TrustIr.ssaChar_source_result_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ssaChar_source_result_count

/-- info: 'TrustIr.ssaChar_manual_borrow_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ssaChar_manual_borrow_boundary

/-- info: 'TrustIr.ssaChar_manual_header_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ssaChar_manual_header_boundary

/-- info: 'TrustIr.ssaChar_classification_result_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ssaChar_classification_result_count

/-- info: 'TrustIr.ssaChar_discarded_result_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ssaChar_discarded_result_checked

/-- info: 'TrustIr.ssaChar_missing_association_before_value_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ssaChar_missing_association_before_value_check

/-- info: 'TrustIr.ssaChar_manual_call_result_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ssaChar_manual_call_result_order

/-- info: 'TrustIr.checkInstructionResults_single_nonChar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.checkInstructionResults_single_nonChar

/-- info: 'TrustIr.bindInstructionResults_single_nonChar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.bindInstructionResults_single_nonChar

/-- info: 'TrustIr.single_result_private_retired' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.single_result_private_retired

/-- info: 'TrustIr.single_result_same_id' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.single_result_same_id

/-- info: 'TrustIr.single_result_implicit_keeps_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.single_result_implicit_keeps_fresh

/-- info: 'TrustIr.single_result_future_declaration_retired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.single_result_future_declaration_retired

/-- info: 'TrustIr.single_result_later_source_destination' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.single_result_later_source_destination

/-- info: 'TrustIr.NatIndexTree.insert_unfold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexTree.insert_unfold

/-- info: 'TrustIr.NatIndexTree.lookupSteps_le_depth' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexTree.lookupSteps_le_depth

/-- info: 'TrustIr.NatIndexTree.keyDepth_le_of_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexTree.keyDepth_le_of_lt_two_pow

/-- info: 'TrustIr.NatIndexTree.depth_insert_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexTree.depth_insert_le

/-- info: 'TrustIr.NatIndexTree.find_unfold' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.NatIndexTree.find_unfold

/-- info: 'TrustIr.NatIndexTree.find_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexTree.find_insert

/-- info: 'TrustIr.NatIndex.find?_empty' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatIndex.find?_empty

/-- info: 'TrustIr.NatIndex.find?_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndex.find?_insert

/-- info: 'TrustIr.NatIndex.find?_insert_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndex.find?_insert_same

/-- info: 'TrustIr.NatIndex.find?_insert_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndex.find?_insert_ne

/-- info: 'TrustIr.NatIndex.find?_insert_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndex.find?_insert_commute

/-- info: 'TrustIr.resultTypeHeaders_mapFunctionCFGs' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.resultTypeHeaders_mapFunctionCFGs

/-- info: 'TrustIr.instructionResultTypes_mapFunctionCFGs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.instructionResultTypes_mapFunctionCFGs

/-- info: 'TrustIr.checkInstructionResults_mapFunctionCFGs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.checkInstructionResults_mapFunctionCFGs

/-- info: 'TrustIr.bindCallResults_mapFunctionCFGs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.bindCallResults_mapFunctionCFGs

/-- info: 'TrustIr.bindInstructionResults_mapFunctionCFGs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.bindInstructionResults_mapFunctionCFGs

/-- info: 'TrustIr.CoroGen.Model.localTypes_present' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.CoroGen.Model.localTypes_present

/-- info: 'TrustIr.CoroGen.expansion_ids_absent_from_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.CoroGen.expansion_ids_absent_from_original

/-- info: 'TrustIr.CoroGen.expanded_source_declarations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.CoroGen.expanded_source_declarations

/-- info: 'TrustIr.CoroGen.expanded_preserves_original_declarations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.CoroGen.expanded_preserves_original_declarations

/-- info: 'TrustIr.FrameOk.legacy_iff' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.FrameOk.legacy_iff

-- Qualified inference/construction/frame scaffolds for the source-aware
-- coroutine replacement. The actual total expansion theorem remains OPEN;
-- these guards do not claim that a callee-relation premise proves it.
/-- info: 'TrustIr.HeldMemoryFrames.semGEPValuesUsing_eqv' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.HeldMemoryFrames.semGEPValuesUsing_eqv

/-- info: 'TrustIr.HeldMemoryFrames.semStoreValueUsing_eqv' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.HeldMemoryFrames.semStoreValueUsing_eqv

/-- info: 'TrustIr.GenericCoro.index_lt_valueBound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.index_lt_valueBound

/-- info: 'TrustIr.GenericCoro.freshId_not_source' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.freshId_not_source

/-- info: 'TrustIr.GenericCoro.freshId_offset_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.freshId_offset_injective

/-- info: 'TrustIr.GenericCoro.inferredFreshId_not_source' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.inferredFreshId_not_source

/-- info: 'TrustIr.GenericCoro.inferredFreshId_not_declared' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.inferredFreshId_not_declared

/-- info: 'TrustIr.GenericCoro.inferredFreshId_offset_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.inferredFreshId_offset_injective

/-- info: 'TrustIr.GenericCoro.mem_map_of_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.mem_map_of_mem

/-- info: 'TrustIr.GenericCoro.mem_bind_of_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.mem_bind_of_mem

/-- info: 'TrustIr.GenericCoro.graphParam_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.graphParam_mem

/-- info: 'TrustIr.GenericCoro.graphNode_dest_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.graphNode_dest_mem

/-- info: 'TrustIr.GenericCoro.graphNode_operand_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.graphNode_operand_mem

/-- info: 'TrustIr.GenericCoro.functionOfGraphWithEvidence_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.functionOfGraphWithEvidence_projection

/-- info: 'TrustIr.GenericCoro.expandedEntry_params' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.expandedEntry_params

/-- info: 'TrustIr.GenericCoro.graphParams_expandFirstEntry' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.graphParams_expandFirstEntry

/-- info: 'TrustIr.GenericCoro.cfgOf_expandFirstEntry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.cfgOf_expandFirstEntry

/-- info: 'TrustIr.GenericCoro.expandedEntry_result_classifications' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.expandedEntry_result_classifications

/-- info: 'TrustIr.GenericCoro.sourceEntry_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.sourceEntry_eq

/-- info: 'TrustIr.GenericCoro.restoreFrame_callerWorld' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.restoreFrame_callerWorld

/-- info: 'TrustIr.GenericCoro.restoreFrame_eq_of_callerWorld' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.restoreFrame_eq_of_callerWorld

/-- info: 'TrustIr.GenericCoro.finishCall_eq_of_effectRelation' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.finishCall_eq_of_effectRelation

/-- info: 'TrustIr.GenericCoro.callFrame_eq_of_effectRelation' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.callFrame_eq_of_effectRelation

/-- info: 'TrustIr.GenericCoro.runCallReq_found' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.runCallReq_found

/-- info: 'TrustIr.GenericCoro.runCallReq_eq_of_effectRelation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.runCallReq_eq_of_effectRelation

/-- info: 'TrustIr.LocalTypeInference.AgreesExcept.insert_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.AgreesExcept.insert_same

/-- info: 'TrustIr.LocalTypeInference.AgreesExcept.insert_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.AgreesExcept.insert_fresh

/-- info: 'TrustIr.LocalTypeInference.AgreesExcept.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.AgreesExcept.trans

/-- info: 'TrustIr.LocalTypeInference.fillPath_agreesExcept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.fillPath_agreesExcept

/-- info: 'TrustIr.LocalTypeInference.fillPath_preserves_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.fillPath_preserves_fresh

/-- info: 'TrustIr.LocalTypeInference.finishPath_agreesExcept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.finishPath_agreesExcept

/-- info: 'TrustIr.LocalTypeInference.finishPath_preserves_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.finishPath_preserves_fresh

/-- info: 'TrustIr.LocalTypeInference.resolve_fresh_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.resolve_fresh_extension

/-- info: 'TrustIr.LocalTypeInference.resolve_direct_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.resolve_direct_fresh

/-- info: 'TrustIr.LocalTypeInference.resolveAll_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.resolveAll_cons

/-- info: 'TrustIr.LocalTypeInference.resolveAll_fresh_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.resolveAll_fresh_extension

/-- info: 'TrustIr.LocalTypeInference.addSource_fresh_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.addSource_fresh_extension

/-- info: 'TrustIr.LocalTypeInference.addSources_fresh_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.addSources_fresh_extension

/-- info: 'TrustIr.LocalTypeInference.zip_fst_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.zip_fst_mem

/-- info: 'TrustIr.LocalTypeInference.addNode_fresh_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.addNode_fresh_extension

/-- info: 'TrustIr.LocalTypeInference.collectNodes_fresh_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.collectNodes_fresh_extension

/-- info: 'TrustIr.LocalTypeInference.original_empty' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.original_empty

/-- info: 'TrustIr.LocalTypeInference.addSource_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.addSource_original

/-- info: 'TrustIr.LocalTypeInference.addSources_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.addSources_original

/-- info: 'TrustIr.LocalTypeInference.zip_snd_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.zip_snd_mem

/-- info: 'TrustIr.LocalTypeInference.addNode_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.addNode_original

/-- info: 'TrustIr.LocalTypeInference.collectNodes_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.collectNodes_original

/-- info: 'TrustIr.LocalTypeInference.withoutFresh_eq_self' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.withoutFresh_eq_self

/-- info: 'TrustIr.LocalTypeInference.freshNode_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.freshNode_seed

/-- info: 'TrustIr.LocalTypeInference.withoutFresh_length_le' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.withoutFresh_length_le

/-- info: 'TrustIr.LocalTypeInference.DeclarationExtension.length_le' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.DeclarationExtension.length_le

/-- info: 'TrustIr.LocalTypeInference.addNode_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.addNode_empty

/-- info: 'TrustIr.LocalTypeInference.collectNodes_insert_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.collectNodes_insert_empty

/-- info: 'TrustIr.LocalTypeInference.addNode_success_census' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.addNode_success_census

/-- info: 'TrustIr.LocalTypeInference.collectParams_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.collectParams_original

/-- info: 'TrustIr.LocalTypeInference.inference_eq_collection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.inference_eq_collection

/-- info: 'TrustIr.LocalTypeInference.collectedInference_fresh_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.collectedInference_fresh_extension

/-- info: 'TrustIr.LocalTypeInference.infer_insert_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.infer_insert_fresh

-- SSA publication freshness and checked parameter binding.
/-- info: 'TrustIr.SSAFreshFrames.cleared_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SSAFreshFrames.cleared_fresh

/-- info: 'TrustIr.SSAFreshFrames.set_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshFrames.set_fresh

/-- info: 'TrustIr.SSAFreshFrames.publish_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshFrames.publish_fresh

/-- info: 'TrustIr.SSAFreshFrames.bindFresh_publish_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshFrames.bindFresh_publish_run

/-- info: 'TrustIr.SSAFreshFrames.bindBlockParams_preserves_fresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshFrames.bindBlockParams_preserves_fresh

/-- info: 'TrustIr.SSAFreshFrames.bindBlockParamsChecked_preserves_fresh' depends on axioms: [Classical.choice,
 propext,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshFrames.bindBlockParamsChecked_preserves_fresh

-- Checked pointer observations add no project-specific axiom.
/-- info: 'TrustIr.bindPointerInteger_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.bindPointerInteger_run

/-- info: 'TrustIr.bindPointerInteger_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.bindPointerInteger_success

/-- info: 'TrustIr.encodeMemoryAt_pointer_address_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.encodeMemoryAt_pointer_address_bound

/-- info: 'TrustIr.encodeMemoryAt_fat_pointer_address_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.encodeMemoryAt_fat_pointer_address_bounds

-- Total source-aware coroutine entry expansion and exact u32 capacity.

/-- info: 'TrustIr.LocalTypeInference.resolve_preserves_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.resolve_preserves_fresh

/-- info: 'TrustIr.LocalTypeInference.resolveAll_preserves_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.resolveAll_preserves_fresh

/-- info: 'TrustIr.LocalTypeInference.collectedInference_missing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.collectedInference_missing

/-- info: 'TrustIr.LocalTypeInference.infer_missing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.infer_missing

/-- info: 'TrustIr.LocalTypeInference.append_member_cases' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.append_member_cases

/-- info: 'TrustIr.LocalTypeInference.InputAvoids.insert_declared' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.InputAvoids.insert_declared

/-- info: 'TrustIr.LocalTypeInference.infer_insert_of_avoid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.infer_insert_of_avoid

/-- info: 'TrustIr.LocalTypeInference.collectNodes_success_census' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.collectNodes_success_census

/-- info: 'TrustIr.LocalTypeInference.infer_success_census' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.infer_success_census

/-- info: 'TrustIr.LocalTypeInference.infer_insert_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.infer_insert_empty

/-- info: 'TrustIr.LocalTypeInference.infer_insert_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.infer_insert_three

/-- info: 'TrustIr.LocalTypeInference.InputAvoids.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.InputAvoids.mono

/-- info: 'TrustIr.LocalTypeInference.InputAvoids.removeNode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.LocalTypeInference.InputAvoids.removeNode

/-- info: 'TrustIr.GenericCoroFreshIds.map_member' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshIds.map_member

/-- info: 'TrustIr.GenericCoroFreshIds.unused_le_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshIds.unused_le_length

/-- info: 'TrustIr.GenericCoroFreshIds.fold_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshIds.fold_find

/-- info: 'TrustIr.GenericCoroFreshIds.occupied_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshIds.occupied_find

/-- info: 'TrustIr.GenericCoroFreshIds.occupied_correct' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshIds.occupied_correct

/-- info: 'TrustIr.GenericCoroFreshIds.scanGap_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshIds.scanGap_some

/-- info: 'TrustIr.GenericCoroFreshIds.scanGap_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshIds.scanGap_none

/-- info: 'TrustIr.GenericCoroFreshIds.nextGap_some' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshIds.nextGap_some

/-- info: 'TrustIr.GenericCoroFreshIds.nextGap_none' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshIds.nextGap_none

/-- info: 'TrustIr.GenericCoroFreshIds.contains_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshIds.contains_insert

/-- info: 'TrustIr.GenericCoroFreshIds.correct_insert' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshIds.correct_insert

/-- info: 'TrustIr.GenericCoroFreshIds.max_u32_does_not_force_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshIds.max_u32_does_not_force_overflow

/-- info: 'TrustIr.GenericCoroFreshIds.original_undefined_uses_stay_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshIds.original_undefined_uses_stay_reserved

/-- info: 'TrustIr.GenericCoroFreshIds.two_remaining_ids_are_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshIds.two_remaining_ids_are_capacity

/-- info: 'TrustIr.GenericCoroFreshIds.duplicates_do_not_create_false_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshIds.duplicates_do_not_create_false_capacity

/-- info: 'TrustIr.GenericCoroFreshIds.left_member_of_append_not_right' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshIds.left_member_of_append_not_right

/-- info: 'TrustIr.GenericCoroFreshIds.capacity_excludes_triple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshIds.capacity_excludes_triple

/-- info: 'TrustIr.GenericCoro.declared_map_avoids' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.declared_map_avoids

/-- info: 'TrustIr.GenericCoro.classified_sources_avoid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.classified_sources_avoid

/-- info: 'TrustIr.GenericCoro.graph_params_original' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.graph_params_original

/-- info: 'TrustIr.GenericCoro.graph_destinations_original' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.graph_destinations_original

/-- info: 'TrustIr.GenericCoro.graph_sources_original' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.graph_sources_original

/-- info: 'TrustIr.GenericCoro.graph_input_avoids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.graph_input_avoids

/-- info: 'TrustIr.GenericCoro.graph_inference_unused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.graph_inference_unused

/-- info: 'TrustIr.GenericCoro.reservation_unused' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.reservation_unused

/-- info: 'TrustIr.GenericCoro.GraphNames.unused' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.GraphNames.unused

/-- info: 'TrustIr.GenericCoro.functionsOfExpansion_source_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.functionsOfExpansion_source_error

/-- info: 'TrustIr.GenericCoro.functionsOfExpansion_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.functionsOfExpansion_capacity

/-- info: 'TrustIr.GenericCoro.cfgOf_decompose' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.cfgOf_decompose

/-- info: 'TrustIr.GenericCoro.expandFirstEntry_at' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.expandFirstEntry_at

/-- info: 'TrustIr.GenericCoro.graphNodes_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.graphNodes_append

/-- info: 'TrustIr.GenericCoro.graphNodes_cons' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.graphNodes_cons

/-- info: 'TrustIr.GenericCoro.graphNodes_sourceEntry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.graphNodes_sourceEntry

/-- info: 'TrustIr.GenericCoro.graphNodes_expandedEntry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.graphNodes_expandedEntry

/-- info: 'TrustIr.GenericCoro.expandedGraph_inference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.expandedGraph_inference

/-- info: 'TrustIr.GenericCoro.functionOfGraph_of_inference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.functionOfGraph_of_inference

/-- info: 'TrustIr.GenericCoro.functionsOfExpansion_metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.functionsOfExpansion_metadata

/-- info: 'TrustIr.GenericCoro.replaceSSA_of_callerWorld' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.replaceSSA_of_callerWorld

/-- info: 'TrustIr.GenericCoro.equivariant_preservesSSA' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.equivariant_preservesSSA

/-- info: 'TrustIr.GenericCoro.equivariant_transport' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.equivariant_transport

/-- info: 'TrustIr.GenericCoro.carrierIntegerOperand_i64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.carrierIntegerOperand_i64

/-- info: 'TrustIr.GenericCoro.gepOffset_singleton_keys' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.gepOffset_singleton_keys

/-- info: 'TrustIr.GenericCoro.heldGEP_i64_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.heldGEP_i64_index

/-- info: 'TrustIr.GenericCoro.encodeMemoryWithFunctions_i64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.encodeMemoryWithFunctions_i64

/-- info: 'TrustIr.GenericCoro.bindInstructionResults_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.bindInstructionResults_store

/-- info: 'TrustIr.GenericCoro.instructionResultTypes_declared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.instructionResultTypes_declared

/-- info: 'TrustIr.GenericCoro.targetEntry_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.targetEntry_eq

/-- info: 'TrustIr.GenericCoro.publishFresh_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.publishFresh_run

/-- info: 'TrustIr.GenericCoro.publishState_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.publishState_fresh

/-- info: 'TrustIr.GenericCoro.publishState_world' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.publishState_world

/-- info: 'TrustIr.GenericCoro.publishState_lookup_same' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.publishState_lookup_same

/-- info: 'TrustIr.GenericCoro.publishState_lookup_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.publishState_lookup_other

/-- info: 'TrustIr.GenericCoro.replaceSSA_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.replaceSSA_fresh

/-- info: 'TrustIr.GenericCoro.replaceSSA_world' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.replaceSSA_world

/-- info: 'TrustIr.GenericCoro.replaceSSA_lookup' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.replaceSSA_lookup

/-- info: 'TrustIr.GenericCoro.lookupValue_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.lookupValue_run

/-- info: 'TrustIr.GenericCoro.expandedValues_held' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.expandedValues_held

/-- info: 'TrustIr.GenericCoro.expandedValues_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.expandedValues_effect

/-- info: 'TrustIr.GenericCoro.suspend_entry_operands' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.suspend_entry_operands

/-- info: 'TrustIr.GenericCoro.GraphNames.different_original' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.GraphNames.different_original

/-- info: 'TrustIr.GenericCoro.expandedGraph_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.expandedGraph_effect

/-- info: 'TrustIr.GenericCoro.callEntry_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.callEntry_succ

/-- info: 'TrustIr.GenericCoro.callEntry_zero_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.callEntry_zero_depth

/-- info: 'TrustIr.GenericCoro.withFunction_found' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.withFunction_found

/-- info: 'TrustIr.GenericCoro.callEntry_eq_of_runCallReq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.callEntry_eq_of_runCallReq

/-- info: 'TrustIr.GenericCoro.expandedGraph_callEquivalent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.expandedGraph_callEquivalent

/-- info: 'TrustIr.GenericCoro.functionsOfExpansion_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.functionsOfExpansion_correct

/-- info: 'TrustIr.GenericCoro.Controls.dense_graph_uses_actual_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Controls.dense_graph_uses_actual_gaps

/-- info: 'TrustIr.GenericCoro.Controls.sparse_graph_uses_low_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Controls.sparse_graph_uses_low_gaps

/-- info: 'TrustIr.GenericCoro.Controls.maximum_u32_graph_stays_serializable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Controls.maximum_u32_graph_stays_serializable

/-- info: 'TrustIr.GenericCoro.Controls.maximum_u32_actual_call_equivalence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Controls.maximum_u32_actual_call_equivalence

/-- info: 'TrustIr.GenericCoro.Controls.unvisited_rows_reserve_identifiers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Controls.unvisited_rows_reserve_identifiers

/-- info: 'TrustIr.GenericCoro.Controls.undeclared_yield_and_unused_rows_are_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Controls.undeclared_yield_and_unused_rows_are_reserved

/-- info: 'TrustIr.GenericCoro.Controls.missing_yield_retains_complete_call_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Controls.missing_yield_retains_complete_call_contract

/-- info: 'TrustIr.GenericCoro.Controls.source_metadata_cycle_is_propagated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Controls.source_metadata_cycle_is_propagated

/-- info: 'TrustIr.GenericCoro.Controls.cyclic_metadata_refuses_before_expansion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Controls.cyclic_metadata_refuses_before_expansion

/-- info: 'TrustIr.GenericCoro.Controls.zero_block_fuel_precedes_missing_cfg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Controls.zero_block_fuel_precedes_missing_cfg

/-- info: 'TrustIr.GenericCoro.Controls.zero_depth_preserves_parameter_arity_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Controls.zero_depth_preserves_parameter_arity_error

/-- info: 'TrustIr.GenericCoro.Controls.zero_depth_preserves_undefined_argument' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Controls.zero_depth_preserves_undefined_argument

/-- info: 'TrustIr.GenericCoro.Controls.zero_depth_precedes_callee_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Controls.zero_depth_precedes_callee_lookup

/-- info: 'TrustIr.GenericCoro.expandedGraph_runCallEquivalent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.expandedGraph_runCallEquivalent

end AxiomAudit
end TrustIr

-- Contextual aggregate operand transport and non-partial Undef.
/-- info: 'TrustIr.checkAggregateLane_tuple_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.checkAggregateLane_tuple_transport

/-- info: 'TrustIr.checkAggregateLane_record_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.checkAggregateLane_record_transport

/-- info: 'TrustIr.checkAggregateLane_nested_poison_is_not_inspected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.checkAggregateLane_nested_poison_is_not_inspected

/-- info: 'TrustIr.checkAggregateLane_immediate_poison_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.checkAggregateLane_immediate_poison_refused

/-- info: 'TrustIr.checkAggregateLane_wrong_bool_carrier_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.checkAggregateLane_wrong_bool_carrier_refused

/-- info: 'TrustIr.checkAggregateLane_wrong_integer_width_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.checkAggregateLane_wrong_integer_width_refused

/-- info: 'TrustIr.stepInstWithContext_nonpartial_undef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepInstWithContext_nonpartial_undef

/-- info: 'TrustIr.makeAggregateValueWithContext_transports_unwritten_tuple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.makeAggregateValueWithContext_transports_unwritten_tuple

-- Host-supplied raw pointer carrier and operation-specific integer exposure.
/-- info: 'TrustIr.rawPointerInteger_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.rawPointerInteger_run

/-- info: 'TrustIr.derivedPointerInteger_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.derivedPointerInteger_unchanged

/-- info: 'TrustIr.rawPointerInteger_width_error_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.rawPointerInteger_width_error_first

/-- info: 'TrustIr.rawPointerInteger_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.rawPointerInteger_success

/-- info: 'TrustIr.ptrToInt_raw_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ptrToInt_raw_lookup

/-- info: 'TrustIr.rawPointerInteger_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.rawPointerInteger_in_range

/-- info: 'TrustIr.raw_far32_to_u128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.raw_far32_to_u128

/-- info: 'TrustIr.raw_far32_to_u32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.raw_far32_to_u32

/-- info: 'TrustIr.raw_far32_to_usize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.raw_far32_to_usize

/-- info: 'TrustIr.raw_u64_max_to_u128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.raw_u64_max_to_u128

/-- info: 'TrustIr.raw_u64_overflow_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.raw_u64_overflow_refused

/-- info: 'TrustIr.derived_far32_still_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.derived_far32_still_refused

-- Exact compressed-index logical view, storage and cost laws.

/-- info: 'TrustIr.NatIndexTree.depth_insert_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexTree.depth_insert_eq

/-- info: 'TrustIr.NatIndexTree.keyDepthFast_eq' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.NatIndexTree.keyDepthFast_eq

/-- info: 'TrustIr.NatIndexTree.nodeCount_empty_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexTree.nodeCount_empty_insert

/-- info: 'TrustIr.NatIndexTree.nodeCount_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexTree.nodeCount_insert

/-- info: 'TrustIr.NatIndexTree.newPathSteps_le_keyDepth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexTree.newPathSteps_le_keyDepth

/-- info: 'TrustIr.NatIndexStorage.KeyDepthCertificate' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatIndexStorage.KeyDepthCertificate

/-- info: 'TrustIr.NatIndexStorage.DepthCertificate' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.NatIndexStorage.DepthCertificate

/-- info: 'TrustIr.NatIndexStorage.keyDepth_certificate' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.NatIndexStorage.keyDepth_certificate

/-- info: 'TrustIr.NatIndexStorage.KeyDepthCertificate.eq_depth' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.NatIndexStorage.KeyDepthCertificate.eq_depth

/-- info: 'TrustIr.NatIndexStorage.DepthCertificate.eq_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexStorage.DepthCertificate.eq_view

/-- info: 'TrustIr.NatIndexStorage.depth_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexStorage.depth_certificate

/-- info: 'TrustIr.NatIndexStorage.toTree_ofTree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.NatIndexStorage.toTree_ofTree

/-- info: 'TrustIr.NatIndexStorage.toTree_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexStorage.toTree_value

/-- info: 'TrustIr.NatIndexStorage.toTree_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexStorage.toTree_even

/-- info: 'TrustIr.NatIndexStorage.toTree_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexStorage.toTree_odd

/-- info: 'TrustIr.NatIndexStorage.toTree_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexStorage.toTree_find

/-- info: 'TrustIr.NatIndexStorage.toTree_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexStorage.toTree_insert

/-- info: 'TrustIr.NatIndexStorage.find_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexStorage.find_insert

/-- info: 'TrustIr.NatIndexStorage.lookupSteps_le_depth' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexStorage.lookupSteps_le_depth

/-- info: 'TrustIr.NatIndexStorage.nodeCount_le_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexStorage.nodeCount_le_view

/-- info: 'TrustIr.NatIndexStorage.depth_le_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexStorage.depth_le_view

/-- info: 'TrustIr.NatIndexStorage.ofTree_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndexStorage.ofTree_find

/-- info: 'TrustIr.NatIndex.tree_ofTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndex.tree_ofTree

/-- info: 'TrustIr.NatIndex.depth_eq_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndex.depth_eq_tree

/-- info: 'TrustIr.NatIndex.tree_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndex.tree_find

/-- info: 'TrustIr.NatIndex.tree_outsideBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndex.tree_outsideBound

/-- info: 'TrustIr.NatIndex.find?_ofTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndex.find?_ofTree

/-- info: 'TrustIr.NatIndex.depth_ofTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndex.depth_ofTree

/-- info: 'TrustIr.NatIndex.keyBound_ofTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndex.keyBound_ofTree

/-- info: 'TrustIr.NatIndex.inserted_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndex.inserted_tree

/-- info: 'TrustIr.NatIndex.inserted_keyBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndex.inserted_keyBound

/-- info: 'TrustIr.NatIndex.inserted_depth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.NatIndex.inserted_depth

-- Successful instruction freshness and actual invoke restoration.

/-- info: 'TrustIr.SSAFreshInstructions.ite_fresh' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.ite_fresh

/-- info: 'TrustIr.SSAFreshInstructions.except_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.except_fresh

/-- info: 'TrustIr.SSAFreshInstructions.rejectPartial_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.rejectPartial_fresh

/-- info: 'TrustIr.SSAFreshInstructions.rejectPoisonValues_fresh' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.rejectPoisonValues_fresh

/-- info: 'TrustIr.SSAFreshInstructions.bindFreshPair_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.bindFreshPair_fresh

/-- info: 'TrustIr.SSAFreshInstructions.nextFloatZeroChoice_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.nextFloatZeroChoice_fresh

/-- info: 'TrustIr.SSAFreshInstructions.addrOfInt_fresh' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.addrOfInt_fresh

/-- info: 'TrustIr.SSAFreshInstructions.bindPointerInteger_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.bindPointerInteger_fresh

/-- info: 'TrustIr.SSAFreshInstructions.bindPointerIntegerWithProvenance_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.bindPointerIntegerWithProvenance_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semCast_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semCast_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semBinOpDeterministic_fresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semBinOpDeterministic_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semBoolBinOpInst_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semBoolBinOpInst_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semUnOp_fresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semUnOp_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semOverflow_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semOverflow_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semICmpInst_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semICmpInst_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semFCmpInst_fresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semFCmpInst_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semOpenFrame_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semOpenFrame_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semBindSlot_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semBindSlot_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semLoadSlot_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semLoadSlot_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semCloseFrame_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semCloseFrame_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semBr_fresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semBr_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semCondBr_fresh' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semCondBr_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semReturn_fresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semReturn_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semFloatMinMaxAt_fresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semFloatMinMaxAt_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semFloatMinMaxScalarValue_fresh' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semFloatMinMaxScalarValue_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semFloatMinMaxLanes_fresh' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semFloatMinMaxLanes_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semFloatMinMaxValues_fresh' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semFloatMinMaxValues_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semFloatMinMax_fresh' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semFloatMinMax_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semBinOp_fresh' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semBinOp_fresh

/-- info: 'TrustIr.SSAFreshInstructions.lookupLanes_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.lookupLanes_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semExtractField_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semExtractField_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semInsertField_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semInsertField_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semMakeAggregate_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semMakeAggregate_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semArraySplat_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semArraySplat_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semSeqMapAddK_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semSeqMapAddK_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semSeqMapNot_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semSeqMapNot_fresh

/-- info: 'TrustIr.SSAFreshInstructions.context_elementIndex_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.context_elementIndex_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semExtractElementUsing_fresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semExtractElementUsing_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semInsertElementUsing_fresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semInsertElementUsing_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semExtractElement_fresh' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semExtractElement_fresh

/-- info: 'TrustIr.SSAFreshInstructions.semInsertElement_fresh' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshInstructions.semInsertElement_fresh

/-- info: 'TrustIr.SSAFreshMemory.fromMemoryExcept_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemory.fromMemoryExcept_fresh

/-- info: 'TrustIr.SSAFreshMemory.getState_bind_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemory.getState_bind_fresh

/-- info: 'TrustIr.SSAFreshMemory.setState_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemory.setState_fresh

/-- info: 'TrustIr.SSAFreshMemory.semStoreUsing_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemory.semStoreUsing_fresh

/-- info: 'TrustIr.SSAFreshMemory.semGEPUsing_fresh' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemory.semGEPUsing_fresh

/-- info: 'TrustIr.SSAFreshMemory.semAllocateUsing_fresh' depends on axioms: [Quot.sound, propext, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemory.semAllocateUsing_fresh

/-- info: 'TrustIr.SSAFreshMemory.expectPointer_fresh' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemory.expectPointer_fresh

/-- info: 'TrustIr.SSAFreshMemory.targetAddress_fresh' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemory.targetAddress_fresh

/-- info: 'TrustIr.SSAFreshMemory.checkTargetRange_fresh' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemory.checkTargetRange_fresh

/-- info: 'TrustIr.SSAFreshMemory.declaredOrNaturalAlign_fresh' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemory.declaredOrNaturalAlign_fresh

/-- info: 'TrustIr.SSAFreshMemory.accessAlign_fresh' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemory.accessAlign_fresh

/-- info: 'TrustIr.SSAFreshMemory.checkedAccess_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemory.checkedAccess_fresh

/-- info: 'TrustIr.SSAFreshMemory.semLoadUsing_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemory.semLoadUsing_fresh

/-- info: 'TrustIr.SSAFreshMemory.semAllocaUsing_fresh' depends on axioms: [Quot.sound, propext, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemory.semAllocaUsing_fresh

/-- info: 'TrustIr.SSAFreshMemory.semHeapAllocUsing_fresh' depends on axioms: [Quot.sound, propext, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemory.semHeapAllocUsing_fresh

/-- info: 'TrustIr.SSAFreshOwnership.getPermission_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshOwnership.getPermission_fresh

/-- info: 'TrustIr.SSAFreshOwnership.setPermission_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SSAFreshOwnership.setPermission_fresh

/-- info: 'TrustIr.SSAFreshOwnership.borrowOperand_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshOwnership.borrowOperand_fresh

/-- info: 'TrustIr.SSAFreshOwnership.getAllocIdFromPtrARC_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshOwnership.getAllocIdFromPtrARC_fresh

/-- info: 'TrustIr.SSAFreshOwnership.requireArcRef_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshOwnership.requireArcRef_fresh

/-- info: 'TrustIr.SSAFreshOwnership.requireObjectBase_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshOwnership.requireObjectBase_fresh

/-- info: 'TrustIr.SSAFreshOwnership.deallocARC_fresh' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshOwnership.deallocARC_fresh

/-- info: 'TrustIr.SSAFreshOwnership.semBorrow_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshOwnership.semBorrow_fresh

/-- info: 'TrustIr.SSAFreshOwnership.semBorrowMut_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshOwnership.semBorrowMut_fresh

/-- info: 'TrustIr.SSAFreshOwnership.semEndBorrow_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshOwnership.semEndBorrow_fresh

/-- info: 'TrustIr.SSAFreshOwnership.semIsUnique_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshOwnership.semIsUnique_fresh

/-- info: 'TrustIr.SSAFreshOwnership.semRetain_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshOwnership.semRetain_fresh

/-- info: 'TrustIr.SSAFreshOwnership.semRelease_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshOwnership.semRelease_fresh

/-- info: 'TrustIr.SSAFreshAtomic.semAtomicLoadUsing_fresh' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshAtomic.semAtomicLoadUsing_fresh

/-- info: 'TrustIr.SSAFreshAtomic.semAtomicStoreUsing_fresh' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshAtomic.semAtomicStoreUsing_fresh

/-- info: 'TrustIr.SSAFreshAtomic.semAtomicRMWUsing_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshAtomic.semAtomicRMWUsing_fresh

/-- info: 'TrustIr.SSAFreshAtomic.semCmpXchgExchangeUsing_fresh' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshAtomic.semCmpXchgExchangeUsing_fresh

/-- info: 'TrustIr.SSAFreshAtomic.semCmpXchg_fresh' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshAtomic.semCmpXchg_fresh

/-- info: 'TrustIr.SSAFreshAtomic.semFence_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SSAFreshAtomic.semFence_fresh

/-- info: 'TrustIr.SSAFreshMemoryExtra.accessAddr_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemoryExtra.accessAddr_fresh

/-- info: 'TrustIr.SSAFreshMemoryExtra.bulkByteCount_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemoryExtra.bulkByteCount_fresh

/-- info: 'TrustIr.SSAFreshMemoryExtra.bulkPointer_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemoryExtra.bulkPointer_fresh

/-- info: 'TrustIr.SSAFreshMemoryExtra.semMemCopy_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemoryExtra.semMemCopy_fresh

/-- info: 'TrustIr.SSAFreshMemoryExtra.semMemSet_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemoryExtra.semMemSet_fresh

/-- info: 'TrustIr.SSAFreshMemoryExtra.semDealloc_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemoryExtra.semDealloc_fresh

/-- info: 'TrustIr.SSAFreshMemoryExtra.semGlobalAddr_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemoryExtra.semGlobalAddr_fresh

/-- info: 'TrustIr.SSAFreshMemoryExtra.semGlobalAddrUsing_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemoryExtra.semGlobalAddrUsing_fresh

/-- info: 'TrustIr.SSAFreshMemoryExtra.semPtrData_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemoryExtra.semPtrData_fresh

/-- info: 'TrustIr.SSAFreshMemoryExtra.semPtrMetadata_fresh' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemoryExtra.semPtrMetadata_fresh

/-- info: 'TrustIr.SSAFreshMemoryExtra.semPtrFromParts_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshMemoryExtra.semPtrFromParts_fresh

/-- info: 'TrustIr.SSAFreshDispatch.semAssertFail_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SSAFreshDispatch.semAssertFail_fresh

/-- info: 'TrustIr.SSAFreshDispatch.semCoroSuspend_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshDispatch.semCoroSuspend_fresh

/-- info: 'TrustIr.SSAFreshDispatch.throwUB_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SSAFreshDispatch.throwUB_fresh

/-- info: 'TrustIr.SSAFreshDispatch.throwTypeError_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SSAFreshDispatch.throwTypeError_fresh

/-- info: 'TrustIr.SSAFreshDispatch.throwUnsupported_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SSAFreshDispatch.throwUnsupported_fresh

/-- info: 'TrustIr.SSAFreshDispatch.semSwitch_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshDispatch.semSwitch_fresh

/-- info: 'TrustIr.SSAFreshDispatch.stepInst_fresh' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshDispatch.stepInst_fresh

/-- info: 'TrustIr.SSAFreshContext.stepInstWithContext_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshContext.stepInstWithContext_fresh

/-- info: 'TrustIr.GenericCoro.finishInvokeReturnWith_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.finishInvokeReturnWith_eq

/-- info: 'TrustIr.GenericCoro.invokeCatch_run' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.invokeCatch_run

/-- info: 'TrustIr.GenericCoro.finishInvokeWith_eq_of_effectRelation' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.finishInvokeWith_eq_of_effectRelation


-- Prepared aggregate memory preserves the actual SSA high-water invariant.

/-- info: 'TrustIr.SSAFreshAggregate.loadValue_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshAggregate.loadValue_fresh

/-- info: 'TrustIr.SSAFreshAggregate.storeValue_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshAggregate.storeValue_fresh

/-- info: 'TrustIr.SSAFreshAggregate.load_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshAggregate.load_fresh

/-- info: 'TrustIr.SSAFreshAggregate.store_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshAggregate.store_fresh

/-- info: 'TrustIr.SSAFreshAggregate.atomicLoad_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshAggregate.atomicLoad_fresh

/-- info: 'TrustIr.SSAFreshAggregate.atomicStore_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshAggregate.atomicStore_fresh

/-- info: 'TrustIr.SSAFreshAggregate.atomicRMW_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshAggregate.atomicRMW_fresh

/-- info: 'TrustIr.SSAFreshAggregate.cmpXchgExchange_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshAggregate.cmpXchgExchange_fresh

/-- info: 'TrustIr.SSAFreshAggregate.semGlobalAddrInContext_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshAggregate.semGlobalAddrInContext_fresh
-- Body unwinding freshness and complete terminator resolver congruence.

/-- info: 'TrustIr.SSAFreshUnwindBody.tryCatch_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SSAFreshUnwindBody.tryCatch_fresh

/-- info: 'TrustIr.SSAFreshUnwindBody.semAllocException_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshUnwindBody.semAllocException_fresh

/-- info: 'TrustIr.SSAFreshUnwindBody.semRaise_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshUnwindBody.semRaise_fresh

/-- info: 'TrustIr.SSAFreshUnwindBody.raiseIfUnwind_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshUnwindBody.raiseIfUnwind_fresh

/-- info: 'TrustIr.SSAFreshUnwindBody.semLandingPadWith_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshUnwindBody.semLandingPadWith_fresh

/-- info: 'TrustIr.GenericCoro.closureTermWithContext_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.closureTermWithContext_congr

/-- info: 'TrustIr.GenericCoro.stepTermWithContext_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.stepTermWithContext_congr


-- Actual list iteration and held-cell allocation preserve SSA frames.

/-- info: 'TrustIr.SSAFreshLoops.forIn_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SSAFreshLoops.forIn_fresh

/-- info: 'TrustIr.GenericCoro.allocateCell_equivariant' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.allocateCell_equivariant

/-- info: 'TrustIr.GenericCoro.allocateCell_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.allocateCell_fresh


-- Generic selected-entry prefix simulation: exact observed dependencies.

/-- info: 'TrustIr.GenericCoro.Prefix.producedStepRaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.producedStepRaw

/-- info: 'TrustIr.GenericCoro.Prefix.producedStepRaw_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.producedStepRaw_eq

/-- info: 'TrustIr.GenericCoro.Prefix.bodyDispatch' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.bodyDispatch

/-- info: 'TrustIr.GenericCoro.Prefix.evalBodyStep_dispatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalBodyStep_dispatch

/-- info: 'TrustIr.GenericCoro.Prefix.semLandingPadWith_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.semLandingPadWith_congr

/-- info: 'TrustIr.GenericCoro.Prefix.evalBodyStep_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalBodyStep_congr

/-- info: 'TrustIr.GenericCoro.Prefix.bodyCall_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.bodyCall_fresh

/-- info: 'TrustIr.GenericCoro.Prefix.bodyIndirect_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.bodyIndirect_fresh

/-- info: 'TrustIr.GenericCoro.Prefix.producedStep_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.producedStep_fresh

/-- info: 'TrustIr.GenericCoro.Prefix.evalBodyStep_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalBodyStep_fresh

/-- info: 'TrustIr.GenericCoro.Prefix.evalBody_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalBody_fresh

/-- info: 'TrustIr.GenericCoro.Prefix.runCallEquivalent_of_selectedEffects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.runCallEquivalent_of_selectedEffects

/-- info: 'TrustIr.GenericCoro.Prefix.callEquivalent_of_runCallEquivalent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.callEquivalent_of_runCallEquivalent

/-- info: 'TrustIr.GenericCoro.Prefix.callEquivalent_of_selectedEffects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.callEquivalent_of_selectedEffects

/-- info: 'TrustIr.GenericCoro.Prefix.bind_same' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.bind_same

/-- info: 'TrustIr.GenericCoro.Prefix.throw_bind_sem' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.throw_bind_sem

/-- info: 'TrustIr.GenericCoro.Prefix.run_throw_sem' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.run_throw_sem

/-- info: 'TrustIr.GenericCoro.Prefix.run_get_sem' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.run_get_sem

/-- info: 'TrustIr.GenericCoro.Prefix.run_set_sem' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.run_set_sem

/-- info: 'TrustIr.GenericCoro.Prefix.bind_match_except' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.bind_match_except

/-- info: 'TrustIr.GenericCoro.Prefix.bind_match_option' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.bind_match_option

/-- info: 'TrustIr.GenericCoro.Prefix.bind_match_unit' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.bind_match_unit

/-- info: 'TrustIr.GenericCoro.Prefix.bind_ite_sem' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.bind_ite_sem

/-- info: 'TrustIr.GenericCoro.Prefix.typedClosure_ite' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.typedClosure_ite

/-- info: 'TrustIr.GenericCoro.Prefix.forIn_equivariant' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.forIn_equivariant

/-- info: 'TrustIr.GenericCoro.Prefix.finishCalleeWith' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.finishCalleeWith

/-- info: 'TrustIr.GenericCoro.Prefix.finishCalleeWith_eq_of_effectRelation' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.finishCalleeWith_eq_of_effectRelation

/-- info: 'TrustIr.GenericCoro.Prefix.callFrameWith' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.callFrameWith

/-- info: 'TrustIr.GenericCoro.Prefix.callFrameWith_eq_of_effectRelation' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.callFrameWith_eq_of_effectRelation

/-- info: 'TrustIr.GenericCoro.Prefix.checkReturns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.checkReturns

/-- info: 'TrustIr.GenericCoro.Prefix.checkReturns_equivariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.checkReturns_equivariant

/-- info: 'TrustIr.GenericCoro.Prefix.checkReturns_scoped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.checkReturns_scoped

/-- info: 'TrustIr.GenericCoro.Prefix.checkReturns_scoped_function' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.checkReturns_scoped_function

/-- info: 'TrustIr.GenericCoro.Prefix.callFrameWith_checkReturns_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.callFrameWith_checkReturns_bind

/-- info: 'TrustIr.GenericCoro.Prefix.callFrameWith_arity_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.callFrameWith_arity_bind

/-- info: 'TrustIr.GenericCoro.Prefix.CalleeEffects' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.CalleeEffects

/-- info: 'TrustIr.GenericCoro.Prefix.bodyCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.bodyCall

/-- info: 'TrustIr.GenericCoro.Prefix.evalBodyStep_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalBodyStep_call

/-- info: 'TrustIr.GenericCoro.Prefix.scopedContext_forFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.scopedContext_forFunction

/-- info: 'TrustIr.GenericCoro.Prefix.bodyCall_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.bodyCall_congr

/-- info: 'TrustIr.GenericCoro.Prefix.HeaderRelated' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.HeaderRelated

/-- info: 'TrustIr.GenericCoro.Prefix.HeaderAgreement' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.HeaderAgreement

/-- info: 'TrustIr.GenericCoro.Prefix.scopedContext' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.scopedContext

/-- info: 'TrustIr.GenericCoro.Prefix.headerAgreement_refl' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.headerAgreement_refl

/-- info: 'TrustIr.GenericCoro.Prefix.headerAgreement_withFunction' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.headerAgreement_withFunction

/-- info: 'TrustIr.GenericCoro.Prefix.HeaderRelated.resultHeaders' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.HeaderRelated.resultHeaders

/-- info: 'TrustIr.GenericCoro.Prefix.resultTypeHeaders_congr' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.resultTypeHeaders_congr

/-- info: 'TrustIr.GenericCoro.Prefix.constValueAtWithDefs_withLocalTypes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.constValueAtWithDefs_withLocalTypes

/-- info: 'TrustIr.GenericCoro.Prefix.checkClosureValueAt_withLocalTypes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.checkClosureValueAt_withLocalTypes

/-- info: 'TrustIr.GenericCoro.Prefix.checkClosureValue_withLocalTypes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.checkClosureValue_withLocalTypes

/-- info: 'TrustIr.GenericCoro.Prefix.constValueAtWithDefs_scoped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.constValueAtWithDefs_scoped

/-- info: 'TrustIr.GenericCoro.Prefix.checkClosureValue_scoped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.checkClosureValue_scoped

/-- info: 'TrustIr.GenericCoro.Prefix.makeAggregateValueWithContext_scoped' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.makeAggregateValueWithContext_scoped

/-- info: 'TrustIr.GenericCoro.Prefix.functionCall_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.functionCall_congr

/-- info: 'TrustIr.GenericCoro.Prefix.checkedClosureCaptures_scoped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.checkedClosureCaptures_scoped

/-- info: 'TrustIr.GenericCoro.Prefix.closureExtract_scoped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.closureExtract_scoped

/-- info: 'TrustIr.GenericCoro.Prefix.closureInsert_scoped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.closureInsert_scoped

/-- info: 'TrustIr.GenericCoro.Prefix.makeClosureValue_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.makeClosureValue_congr

/-- info: 'TrustIr.GenericCoro.Prefix.closureCall_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.closureCall_congr

/-- info: 'TrustIr.GenericCoro.PrefixControls.graph' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PrefixControls.graph

/-- info: 'TrustIr.GenericCoro.PrefixControls.selectedTarget' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PrefixControls.selectedTarget

/-- info: 'TrustIr.GenericCoro.PrefixControls.actual_factory_expands_nonempty_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PrefixControls.actual_factory_expands_nonempty_entry

/-- info: 'TrustIr.GenericCoro.PrefixControls.prefix_destination_is_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PrefixControls.prefix_destination_is_retained

/-- info: 'TrustIr.GenericCoro.PrefixControls.unused_trailing_rows_are_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PrefixControls.unused_trailing_rows_are_reserved

/-- info: 'TrustIr.GenericCoro.PrefixControls.actual_prefix_rows_are_normalized_before_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PrefixControls.actual_prefix_rows_are_normalized_before_append

/-- info: 'TrustIr.GenericCoro.PrefixControls.full_prefix_and_macro_are_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PrefixControls.full_prefix_and_macro_are_retained

/-- info: 'TrustIr.GenericCoro.expandedGraph_prefix_runCallEquivalent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.expandedGraph_prefix_runCallEquivalent

/-- info: 'TrustIr.GenericCoro.expandedGraph_prefix_callEquivalent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.expandedGraph_prefix_callEquivalent

/-- info: 'TrustIr.GenericCoro.functionsOfExpansion_prefix_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.functionsOfExpansion_prefix_correct

/-- info: 'TrustIr.GenericCoro.Prefix.evalLayer_sourceEntry_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalLayer_sourceEntry_eq

/-- info: 'TrustIr.GenericCoro.Prefix.evalLayer_targetEntry_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalLayer_targetEntry_eq

/-- info: 'TrustIr.GenericCoro.Prefix.resolvedEntry_typesAgree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.resolvedEntry_typesAgree

/-- info: 'TrustIr.GenericCoro.Prefix.effect_after_fresh_prefix' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.effect_after_fresh_prefix

/-- info: 'TrustIr.GenericCoro.Prefix.suspend_prefix_operands' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.suspend_prefix_operands

/-- info: 'TrustIr.GenericCoro.Prefix.expandedPrefix_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.expandedPrefix_effect

/-- info: 'TrustIr.GenericCoro.Prefix.callFrameWith_run' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.callFrameWith_run

/-- info: 'TrustIr.GenericCoro.Prefix.callFrameWith_equivariant' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.callFrameWith_equivariant

/-- info: 'TrustIr.GenericCoro.Prefix.callFrameWith_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.callFrameWith_fresh

/-- info: 'TrustIr.GenericCoro.Prefix.callFrame_with_checkReturns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.callFrame_with_checkReturns

/-- info: 'TrustIr.GenericCoro.Prefix.callFrame_equivariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.callFrame_equivariant

/-- info: 'TrustIr.GenericCoro.Prefix.callFrame_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.callFrame_fresh

/-- info: 'TrustIr.GenericCoro.Prefix.resolveDrop_operands' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.resolveDrop_operands

/-- info: 'TrustIr.GenericCoro.Prefix.resolveDrop_scoped' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.resolveDrop_scoped

/-- info: 'TrustIr.GenericCoro.Prefix.resolveBlock_scoped' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.resolveBlock_scoped

/-- info: 'TrustIr.GenericCoro.Prefix.bodyInsts_resolve' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.bodyInsts_resolve

/-- info: 'TrustIr.GenericCoro.Prefix.graphNode_ids' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.graphNode_ids

/-- info: 'TrustIr.GenericCoro.Prefix.resolvedRow_typesAgree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.resolvedRow_typesAgree

/-- info: 'TrustIr.GenericCoro.Prefix.entry_body_mem_graphNodes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.entry_body_mem_graphNodes

/-- info: 'TrustIr.GenericCoro.Prefix.expandedGraph_prefix_layer_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.expandedGraph_prefix_layer_effect

/-- info: 'TrustIr.GenericCoro.Prefix.rawIndirectArguments' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.rawIndirectArguments

/-- info: 'TrustIr.GenericCoro.Prefix.rawIndirectArgumentsWith' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.rawIndirectArgumentsWith

/-- info: 'TrustIr.GenericCoro.Prefix.rawIndirectArguments_bind' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.rawIndirectArguments_bind

/-- info: 'TrustIr.GenericCoro.Prefix.rawIndirectArguments_congr' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.rawIndirectArguments_congr

/-- info: 'TrustIr.GenericCoro.Prefix.indirectArguments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.indirectArguments

/-- info: 'TrustIr.GenericCoro.Prefix.indirectArgumentsWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.indirectArgumentsWith

/-- info: 'TrustIr.GenericCoro.Prefix.indirectArguments_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.indirectArguments_bind

/-- info: 'TrustIr.GenericCoro.Prefix.indirectArguments_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.indirectArguments_congr

/-- info: 'TrustIr.GenericCoro.Prefix.indirectAddress' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.indirectAddress

/-- info: 'TrustIr.GenericCoro.Prefix.bodyIndirect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.bodyIndirect

/-- info: 'TrustIr.GenericCoro.Prefix.evalBodyStep_indirect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalBodyStep_indirect

/-- info: 'TrustIr.GenericCoro.Prefix.bodyIndirect_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.bodyIndirect_congr

/-- info: 'TrustIr.GenericCoro.Prefix.effectRelation_refl' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.effectRelation_refl

/-- info: 'TrustIr.GenericCoro.Prefix.evaluatorAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evaluatorAt

/-- info: 'TrustIr.GenericCoro.Prefix.SameGraphs' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.SameGraphs

/-- info: 'TrustIr.GenericCoro.Prefix.SelectedEffects' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.SelectedEffects

/-- info: 'TrustIr.GenericCoro.Prefix.calleeEffects_of_update' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.calleeEffects_of_update

/-- info: 'TrustIr.GenericCoro.Prefix.evaluator_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evaluator_simulation

/-- info: 'TrustIr.GenericCoro.bodyInsts_normalized_append' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.bodyInsts_normalized_append

/-- info: 'TrustIr.GenericCoro.graphNodes_prefix_sourceEntry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.graphNodes_prefix_sourceEntry

/-- info: 'TrustIr.GenericCoro.graphNodes_prefix_expandedEntry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.graphNodes_prefix_expandedEntry

/-- info: 'TrustIr.GenericCoro.expandedGraph_prefix_inference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.expandedGraph_prefix_inference

/-- info: 'TrustIr.GenericCoro.Prefix.invokeFrameWith' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.invokeFrameWith

/-- info: 'TrustIr.GenericCoro.Prefix.invokeFrameWith_eq_of_effectRelation' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.invokeFrameWith_eq_of_effectRelation

/-- info: 'TrustIr.GenericCoro.Prefix.invokeFrameWith_checkReturns_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.invokeFrameWith_checkReturns_bind

/-- info: 'TrustIr.GenericCoro.Prefix.invokeFrameWith_checkReturns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.invokeFrameWith_checkReturns

/-- info: 'TrustIr.GenericCoro.Prefix.Recurse' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.Recurse

/-- info: 'TrustIr.GenericCoro.Prefix.evalBodyStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalBodyStep

/-- info: 'TrustIr.GenericCoro.Prefix.evalBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalBody

/-- info: 'TrustIr.GenericCoro.Prefix.evalLayer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalLayer

/-- info: 'TrustIr.GenericCoro.Prefix.stepNWithContext_succ_layer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.stepNWithContext_succ_layer

/-- info: 'TrustIr.GenericCoro.Prefix.evalBody_congrOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalBody_congrOn

/-- info: 'TrustIr.GenericCoro.Prefix.evalLayer_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalLayer_congr

/-- info: 'TrustIr.GenericCoro.Prefix.OnlyYield' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.OnlyYield

/-- info: 'TrustIr.GenericCoro.Prefix.onlyYield_pure' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.onlyYield_pure

/-- info: 'TrustIr.GenericCoro.Prefix.onlyYield_throw' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.onlyYield_throw

/-- info: 'TrustIr.GenericCoro.Prefix.onlyYield_typeError' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.onlyYield_typeError

/-- info: 'TrustIr.GenericCoro.Prefix.onlyYield_bind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.onlyYield_bind

/-- info: 'TrustIr.GenericCoro.Prefix.evalBodyStep_onlyYield' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalBodyStep_onlyYield

/-- info: 'TrustIr.GenericCoro.Prefix.onlyYield_bind_eq' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.onlyYield_bind_eq

/-- info: 'TrustIr.GenericCoro.Prefix.evalBody_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalBody_nil

/-- info: 'TrustIr.GenericCoro.Prefix.evalBody_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalBody_cons

/-- info: 'TrustIr.GenericCoro.Prefix.evalBody_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalBody_append

/-- info: 'TrustIr.GenericCoro.Prefix.evalBody_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalBody_congr

/-- info: 'TrustIr.GenericCoro.Prefix.forIn_sem_congr' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.forIn_sem_congr

/-- info: 'TrustIr.GenericCoro.Prefix.TypesAgreeOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.TypesAgreeOn

/-- info: 'TrustIr.GenericCoro.Prefix.TypesAgreeOn.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.TypesAgreeOn.mono

/-- info: 'TrustIr.GenericCoro.Prefix.TypesAgreeOn.at' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.TypesAgreeOn.at

/-- info: 'TrustIr.GenericCoro.Prefix.localResultTypes_borrow_operand' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.localResultTypes_borrow_operand

/-- info: 'TrustIr.GenericCoro.Prefix.mapM_congr_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.mapM_congr_mem

/-- info: 'TrustIr.GenericCoro.Prefix.integerOperand_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.integerOperand_congr

/-- info: 'TrustIr.GenericCoro.Prefix.carrierIntegerOperand_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.carrierIntegerOperand_congr

/-- info: 'TrustIr.GenericCoro.Prefix.elementIndex_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.elementIndex_congr

/-- info: 'TrustIr.GenericCoro.Prefix.declaredFieldTy_scoped' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.declaredFieldTy_scoped

/-- info: 'TrustIr.GenericCoro.Prefix.checkDeclaredField_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.checkDeclaredField_congr

/-- info: 'TrustIr.GenericCoro.Prefix.resultSourceType_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.resultSourceType_congr

/-- info: 'TrustIr.GenericCoro.Prefix.ssaInstructionResultTypes_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.ssaInstructionResultTypes_congr

/-- info: 'TrustIr.GenericCoro.Prefix.instructionResultTypes_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.instructionResultTypes_congr

/-- info: 'TrustIr.GenericCoro.Prefix.checkInstructionResults_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.checkInstructionResults_congr

/-- info: 'TrustIr.GenericCoro.Prefix.bindCallResults_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.bindCallResults_congr

/-- info: 'TrustIr.GenericCoro.Prefix.bindInstructionResults_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.bindInstructionResults_congr

/-- info: 'TrustIr.GenericCoro.PrefixProofControls.nonempty_copy_factory_retains_call_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PrefixProofControls.nonempty_copy_factory_retains_call_contract

/-- info: 'TrustIr.GenericCoro.PrefixProofControls.metadataCycleGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PrefixProofControls.metadataCycleGraph

/-- info: 'TrustIr.GenericCoro.PrefixProofControls.nonempty_prefix_metadata_cycle_is_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PrefixProofControls.nonempty_prefix_metadata_cycle_is_refused

/-- info: 'TrustIr.GenericCoro.PrefixProofControls.nonempty_prefix_metadata_refusal_retains_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PrefixProofControls.nonempty_prefix_metadata_refusal_retains_contract

/-- info: 'TrustIr.GenericCoro.PrefixProofControls.undefinedYieldGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PrefixProofControls.undefinedYieldGraph

/-- info: 'TrustIr.GenericCoro.PrefixProofControls.undefined_yield_and_unused_rows_remain_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PrefixProofControls.undefined_yield_and_unused_rows_remain_reserved

/-- info: 'TrustIr.GenericCoro.PrefixProofControls.undefined_yield_prefix_retains_complete_call_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PrefixProofControls.undefined_yield_prefix_retains_complete_call_contract

/-- info: 'TrustIr.GenericCoro.PrefixProofControls.recursiveSignature' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PrefixProofControls.recursiveSignature

/-- info: 'TrustIr.GenericCoro.PrefixProofControls.recursiveHeaders' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PrefixProofControls.recursiveHeaders

/-- info: 'TrustIr.GenericCoro.PrefixProofControls.recursiveGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PrefixProofControls.recursiveGraph

/-- info: 'TrustIr.GenericCoro.PrefixProofControls.recursive_prefix_factory_retains_call_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PrefixProofControls.recursive_prefix_factory_retains_call_contract

/-- info: 'TrustIr.GenericCoro.PrefixProofControls.actual_copy_pair_preserves_zero_resource_contracts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PrefixProofControls.actual_copy_pair_preserves_zero_resource_contracts

/-- info: 'TrustIr.GenericCoro.Prefix.semAllocateUsing_reader_congr' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.semAllocateUsing_reader_congr

/-- info: 'TrustIr.GenericCoro.Prefix.forIn_except_congr' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.forIn_except_congr

/-- info: 'TrustIr.GenericCoro.Prefix.gepOffsetUsing_reader_congr' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.gepOffsetUsing_reader_congr

/-- info: 'TrustIr.GenericCoro.Prefix.lookupInput_key' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.lookupInput_key

/-- info: 'TrustIr.GenericCoro.Prefix.lookupInputs_keys' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.lookupInputs_keys

/-- info: 'TrustIr.GenericCoro.Prefix.semGEPUsing_reader_congr' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.semGEPUsing_reader_congr

/-- info: 'TrustIr.GenericCoro.Prefix.seqMapStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.seqMapStep

/-- info: 'TrustIr.GenericCoro.Prefix.seqMapReturns' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.seqMapReturns

/-- info: 'TrustIr.GenericCoro.Prefix.seqMapReturns_equivariant' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.seqMapReturns_equivariant

/-- info: 'TrustIr.GenericCoro.Prefix.seqMapElement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.seqMapElement

/-- info: 'TrustIr.GenericCoro.Prefix.seqMapElement_scoped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.seqMapElement_scoped

/-- info: 'TrustIr.GenericCoro.Prefix.seqMapInvoke' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.seqMapInvoke

/-- info: 'TrustIr.GenericCoro.Prefix.seqMapApply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.seqMapApply

/-- info: 'TrustIr.GenericCoro.Prefix.seqMapRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.seqMapRun

/-- info: 'TrustIr.GenericCoro.Prefix.seqMapApplyCallWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.seqMapApplyCallWith

/-- info: 'TrustIr.GenericCoro.Prefix.seqMapApply_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.seqMapApply_framed

/-- info: 'TrustIr.GenericCoro.Prefix.seqMapStep_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.seqMapStep_calls

/-- info: 'TrustIr.GenericCoro.Prefix.seqMapStep_framed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.seqMapStep_framed

/-- info: 'TrustIr.GenericCoro.Prefix.seqMapRun_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.seqMapRun_congr

/-- info: 'TrustIr.GenericCoro.Prefix.seqMapStep_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.seqMapStep_congr

/-- info: 'TrustIr.GenericCoro.Prefix.producedStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.producedStep

/-- info: 'TrustIr.GenericCoro.Prefix.producedStep_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.producedStep_congr

/-- info: 'TrustIr.GenericCoro.Prefix.seqMapElement_equivariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.seqMapElement_equivariant

/-- info: 'TrustIr.GenericCoro.Prefix.seqMapElement_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.seqMapElement_fresh

/-- info: 'TrustIr.GenericCoro.Prefix.seqMapRun_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.seqMapRun_fresh

/-- info: 'TrustIr.GenericCoro.Prefix.seqMapStep_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.seqMapStep_fresh

/-- info: 'TrustIr.GenericCoro.Prefix.stepInstWithContext_const_scoped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.stepInstWithContext_const_scoped

/-- info: 'TrustIr.GenericCoro.Prefix.stepInstWithContext_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.stepInstWithContext_congr

/-- info: 'TrustIr.GenericCoro.Prefix.evalTransfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalTransfer

/-- info: 'TrustIr.GenericCoro.Prefix.evalLayer_eq_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalLayer_eq_transfer

/-- info: 'TrustIr.GenericCoro.Prefix.evalTransfer_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalTransfer_congr

/-- info: 'TrustIr.GenericCoro.Prefix.captureCheckStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.captureCheckStep

/-- info: 'TrustIr.GenericCoro.Prefix.checkClosureValueAt_succ_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.checkClosureValueAt_succ_step

/-- info: 'TrustIr.GenericCoro.Prefix.captureCheckStep_withLocalTypes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.captureCheckStep_withLocalTypes


-- Complete finite-graph coroutine lowering: exact observed dependencies.

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_duplicate_labels_keep_first_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_duplicate_labels_keep_first_match

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_duplicate_labels_keep_first_match.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_duplicate_labels_keep_first_match.match_1

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_expands_nonentry_graph' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_expands_nonentry_graph

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_infers_all_generated_types' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_infers_all_generated_types

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_installs_both_expanded_blocks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_installs_both_expanded_blocks

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_installs_both_expanded_blocks.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_installs_both_expanded_blocks.match_1

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_keeps_dropped_raw_ids_undeclared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_keeps_dropped_raw_ids_undeclared

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.actual_graph_instantiates_factory_inference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.actual_graph_instantiates_factory_inference

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.actual_partial_capacity_is_reported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.actual_partial_capacity_is_reported

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.actual_plan_uses_two_distinct_triples' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.actual_plan_uses_two_distinct_triples

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.actual_source_error_precedes_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.actual_source_error_precedes_capacity

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.cyclicGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.cyclicGraph

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.empty_graph_needs_no_identifier_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.empty_graph_needs_no_identifier_capacity

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.entry' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.entry

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.first' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.first

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.graph' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.graph

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.header' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.header

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.outputTag' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.outputTag

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.outputTag.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.outputTag.match_1

/-- info: 'TrustIr.GenericCoro.AllBlocks.Controls.second' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Controls.second

/-- info: 'TrustIr.GenericCoro.AllBlocks.Expansion' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Expansion

/-- info: 'TrustIr.GenericCoro.AllBlocks.Expansion.capacity' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Expansion.capacity

/-- info: 'TrustIr.GenericCoro.AllBlocks.Expansion.capacity.inj' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Expansion.capacity.inj

/-- info: 'TrustIr.GenericCoro.AllBlocks.Expansion.capacity.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Expansion.capacity.injEq

/-- info: 'TrustIr.GenericCoro.AllBlocks.Expansion.capacity.sizeOf_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Expansion.capacity.sizeOf_spec

/-- info: 'TrustIr.GenericCoro.AllBlocks.Expansion.casesOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Expansion.casesOn

/-- info: 'TrustIr.GenericCoro.AllBlocks.Expansion.expanded' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Expansion.expanded

/-- info: 'TrustIr.GenericCoro.AllBlocks.Expansion.expanded.inj' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Expansion.expanded.inj

/-- info: 'TrustIr.GenericCoro.AllBlocks.Expansion.expanded.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Expansion.expanded.injEq

/-- info: 'TrustIr.GenericCoro.AllBlocks.Expansion.expanded.sizeOf_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Expansion.expanded.sizeOf_spec

/-- info: 'TrustIr.GenericCoro.AllBlocks.Expansion.noConfusion' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Expansion.noConfusion

/-- info: 'TrustIr.GenericCoro.AllBlocks.Expansion.noConfusionType' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Expansion.noConfusionType

/-- info: 'TrustIr.GenericCoro.AllBlocks.Expansion.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Expansion.rec

/-- info: 'TrustIr.GenericCoro.AllBlocks.Expansion.recOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Expansion.recOn

/-- info: 'TrustIr.GenericCoro.AllBlocks.Expansion.unchanged' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Expansion.unchanged

/-- info: 'TrustIr.GenericCoro.AllBlocks.Expansion.unchanged.inj' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Expansion.unchanged.inj

/-- info: 'TrustIr.GenericCoro.AllBlocks.Expansion.unchanged.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Expansion.unchanged.injEq

/-- info: 'TrustIr.GenericCoro.AllBlocks.Expansion.unchanged.sizeOf_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.Expansion.unchanged.sizeOf_spec

/-- info: 'TrustIr.GenericCoro.AllBlocks.FactoryCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.FactoryCorrect

/-- info: 'TrustIr.GenericCoro.AllBlocks.FactoryCorrect.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.FactoryCorrect.match_1

/-- info: 'TrustIr.GenericCoro.AllBlocks.NoSchedule' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.NoSchedule

/-- info: 'TrustIr.GenericCoro.AllBlocks.ProofControls.actual_graph_call_equivalence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.ProofControls.actual_graph_call_equivalence

/-- info: 'TrustIr.GenericCoro.AllBlocks.ProofControls.duplicate_occurrences_have_complete_call_equivalence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.ProofControls.duplicate_occurrences_have_complete_call_equivalence

/-- info: 'TrustIr.GenericCoro.AllBlocks.ProofControls.nonentry_br_graph_has_complete_call_equivalence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.ProofControls.nonentry_br_graph_has_complete_call_equivalence

/-- info: 'TrustIr.GenericCoro.AllBlocks.functions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.functions

/-- info: 'TrustIr.GenericCoro.AllBlocks.functionsWithDomain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.functionsWithDomain

/-- info: 'TrustIr.GenericCoro.AllBlocks.functionsWithDomain.match_1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.functionsWithDomain.match_1

/-- info: 'TrustIr.GenericCoro.AllBlocks.functionsWithDomain.proof_1' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.functionsWithDomain.proof_1

/-- info: 'TrustIr.GenericCoro.AllBlocks.functions_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.functions_correct

/-- info: 'TrustIr.GenericCoro.AllBlocks.functions_defined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.functions_defined

/-- info: 'TrustIr.GenericCoro.AllBlocks.functions_expanded_of_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.functions_expanded_of_ready

/-- info: 'TrustIr.GenericCoro.AllBlocks.functions_source_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.functions_source_error

/-- info: 'TrustIr.GenericCoro.AllBlocks.functions_without_suspends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.functions_without_suspends

/-- info: 'TrustIr.GenericCoro.AllBlocks.withInferredGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.withInferredGraph

/-- info: 'TrustIr.GenericCoro.AllBlocks.withInferredGraph_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.withInferredGraph_eq

/-- info: 'TrustIr.GenericCoro.AllBlocksEffect.bind_effect' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEffect.bind_effect

/-- info: 'TrustIr.GenericCoro.AllBlocksEntry.expandedPrefix_effect_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksEntry.expandedPrefix_effect_fresh

/-- info: 'TrustIr.GenericCoro.AllBlocksInduction.PairedEffects' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInduction.PairedEffects

/-- info: 'TrustIr.GenericCoro.AllBlocksInduction.evaluator_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInduction.evaluator_simulation

/-- info: 'TrustIr.GenericCoro.AllBlocksInduction.selected_of_paired' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInduction.selected_of_paired

/-- info: 'TrustIr.GenericCoro.AllBlocksInference.Plans.inference' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.Plans.inference

/-- info: 'TrustIr.GenericCoro.AllBlocksInference.Plans.inference.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.Plans.inference.match_1

/-- info: 'TrustIr.GenericCoro.AllBlocksInference.Supported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.Supported

/-- info: 'TrustIr.GenericCoro.AllBlocksInference.TraceTyped' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.TraceTyped

/-- info: 'TrustIr.GenericCoro.AllBlocksInference.graphNames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.graphNames

/-- info: 'TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_1

/-- info: 'TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_2

/-- info: 'TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_3

/-- info: 'TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_4

/-- info: 'TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_5

/-- info: 'TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_6' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_6

/-- info: 'TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_7' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_7

/-- info: 'TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_8

/-- info: 'TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_9' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_9

/-- info: 'TrustIr.GenericCoro.AllBlocksInference.lowerRows_inference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.lowerRows_inference

/-- info: 'TrustIr.GenericCoro.AllBlocksKept.evalLayer_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksKept.evalLayer_effect

/-- info: 'TrustIr.GenericCoro.AllBlocksKept.evalLayer_effect.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksKept.evalLayer_effect.match_1

/-- info: 'TrustIr.GenericCoro.AllBlocksLayer.lowerRows_layer_of_transfer' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksLayer.lowerRows_layer_of_transfer

/-- info: 'TrustIr.GenericCoro.AllBlocksSimulation.lowerRows_layer_effect' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksSimulation.lowerRows_layer_effect

/-- info: 'TrustIr.GenericCoro.AllBlocksSimulation.lowerRows_runCallEquivalent' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksSimulation.lowerRows_runCallEquivalent

/-- info: 'TrustIr.GenericCoro.GraphViews.blockInterface' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.GraphViews.blockInterface

/-- info: 'TrustIr.GenericCoro.GraphViews.cfgOf_observation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.GraphViews.cfgOf_observation

/-- info: 'TrustIr.GenericCoro.GraphViews.cfgOf_observation_of_rows' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.GraphViews.cfgOf_observation_of_rows

/-- info: 'TrustIr.GenericCoro.GraphViews.expandFirstEntry_observation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.GraphViews.expandFirstEntry_observation

/-- info: 'TrustIr.GenericCoro.GraphViews.expandedEntry_interface' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.GraphViews.expandedEntry_interface

/-- info: 'TrustIr.GenericCoro.GraphViews.expandedEntry_pad' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.GraphViews.expandedEntry_pad

/-- info: 'TrustIr.GenericCoro.GraphViews.expandedGraph_interface' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.GraphViews.expandedGraph_interface

/-- info: 'TrustIr.GenericCoro.GraphViews.expandedGraph_padViews' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.GraphViews.expandedGraph_padViews

/-- info: 'TrustIr.GenericCoro.GraphViews.expandedGraph_params' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.GraphViews.expandedGraph_params

/-- info: 'TrustIr.GenericCoro.GraphViews.padViews_of_interface_rows' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.GraphViews.padViews_of_interface_rows

/-- info: 'TrustIr.GenericCoro.GraphViews.params_of_interface_rows' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.GraphViews.params_of_interface_rows

/-- info: 'TrustIr.GenericCoro.IndexedCFG.Controls.arbitrary_high_key_is_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.Controls.arbitrary_high_key_is_retained

/-- info: 'TrustIr.GenericCoro.IndexedCFG.Controls.duplicate_first_row_wins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.Controls.duplicate_first_row_wins

/-- info: 'TrustIr.GenericCoro.IndexedCFG.Controls.empty_graph_is_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.Controls.empty_graph_is_missing

/-- info: 'TrustIr.GenericCoro.IndexedCFG.Controls.first' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.Controls.first

/-- info: 'TrustIr.GenericCoro.IndexedCFG.Controls.high' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.Controls.high

/-- info: 'TrustIr.GenericCoro.IndexedCFG.Controls.neighboring_high_key_is_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.Controls.neighboring_high_key_is_missing

/-- info: 'TrustIr.GenericCoro.IndexedCFG.Controls.rows' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.Controls.rows

/-- info: 'TrustIr.GenericCoro.IndexedCFG.Controls.shadowed' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.Controls.shadowed

/-- info: 'TrustIr.GenericCoro.IndexedCFG.Controls.zero_key_is_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.Controls.zero_key_is_retained

/-- info: 'TrustIr.GenericCoro.IndexedCFG.PreparedCFG' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.PreparedCFG

/-- info: 'TrustIr.GenericCoro.IndexedCFG.PreparedCFG.casesOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.PreparedCFG.casesOn

/-- info: 'TrustIr.GenericCoro.IndexedCFG.PreparedCFG.cfg' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.PreparedCFG.cfg

/-- info: 'TrustIr.GenericCoro.IndexedCFG.PreparedCFG.index' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.PreparedCFG.index

/-- info: 'TrustIr.GenericCoro.IndexedCFG.PreparedCFG.mk' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.PreparedCFG.mk

/-- info: 'TrustIr.GenericCoro.IndexedCFG.PreparedCFG.mk.inj' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.PreparedCFG.mk.inj

/-- info: 'TrustIr.GenericCoro.IndexedCFG.PreparedCFG.mk.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.PreparedCFG.mk.injEq

/-- info: 'TrustIr.GenericCoro.IndexedCFG.PreparedCFG.mk.sizeOf_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.PreparedCFG.mk.sizeOf_spec

/-- info: 'TrustIr.GenericCoro.IndexedCFG.PreparedCFG.noConfusion' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.PreparedCFG.noConfusion

/-- info: 'TrustIr.GenericCoro.IndexedCFG.PreparedCFG.noConfusionType' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.PreparedCFG.noConfusionType

/-- info: 'TrustIr.GenericCoro.IndexedCFG.PreparedCFG.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.PreparedCFG.rec

/-- info: 'TrustIr.GenericCoro.IndexedCFG.PreparedCFG.recOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.PreparedCFG.recOn

/-- info: 'TrustIr.GenericCoro.IndexedCFG.indexedCFG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.indexedCFG

/-- info: 'TrustIr.GenericCoro.IndexedCFG.indexedCFG_eq_cfgOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.indexedCFG_eq_cfgOf

/-- info: 'TrustIr.GenericCoro.IndexedCFG.indexedCFG_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.indexedCFG_index

/-- info: 'TrustIr.GenericCoro.IndexedCFG.indexedCFG_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.indexedCFG_lookup

/-- info: 'TrustIr.GenericCoro.IndexedCFG.insertFirst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.insertFirst

/-- info: 'TrustIr.GenericCoro.IndexedCFG.insertFirst.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.insertFirst.match_1

/-- info: 'TrustIr.GenericCoro.IndexedCFG.insertFirst_find' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.insertFirst_find

/-- info: 'TrustIr.GenericCoro.IndexedCFG.prepare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.prepare

/-- info: 'TrustIr.GenericCoro.IndexedCFG.prepareFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.prepareFrom

/-- info: 'TrustIr.GenericCoro.IndexedCFG.prepareFrom.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.prepareFrom.eq_1

/-- info: 'TrustIr.GenericCoro.IndexedCFG.prepareFrom.eq_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.prepareFrom.eq_2

/-- info: 'TrustIr.GenericCoro.IndexedCFG.prepareFrom.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.prepareFrom.match_1

/-- info: 'TrustIr.GenericCoro.IndexedCFG.prepareFrom_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.prepareFrom_lookup

/-- info: 'TrustIr.GenericCoro.IndexedCFG.prepare_first_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.prepare_first_row

/-- info: 'TrustIr.GenericCoro.IndexedCFG.prepare_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.IndexedCFG.prepare_lookup

/-- info: 'TrustIr.GenericCoro.PadViews.Controls.absence_and_nonpad_are_distinct' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.Controls.absence_and_nonpad_are_distinct

/-- info: 'TrustIr.GenericCoro.PadViews.Controls.actual_pad_entry_ignores_other_cfg_fields' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.Controls.actual_pad_entry_ignores_other_cfg_fields

/-- info: 'TrustIr.GenericCoro.PadViews.Controls.catchAll' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.Controls.catchAll

/-- info: 'TrustIr.GenericCoro.PadViews.Controls.catch_all_selector_one' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.Controls.catch_all_selector_one

/-- info: 'TrustIr.GenericCoro.PadViews.Controls.cleanup' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.Controls.cleanup

/-- info: 'TrustIr.GenericCoro.PadViews.Controls.cleanupWithTail' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.Controls.cleanupWithTail

/-- info: 'TrustIr.GenericCoro.PadViews.Controls.cleanup_selector_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.Controls.cleanup_selector_zero

/-- info: 'TrustIr.GenericCoro.PadViews.Controls.different_cfgs_have_equal_pad_views' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.Controls.different_cfgs_have_equal_pad_views

/-- info: 'TrustIr.GenericCoro.PadViews.Controls.missing' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.Controls.missing

/-- info: 'TrustIr.GenericCoro.PadViews.Controls.missing_block_keeps_error' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.Controls.missing_block_keeps_error

/-- info: 'TrustIr.GenericCoro.PadViews.Controls.present_nonpad_keeps_error' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.Controls.present_nonpad_keeps_error

/-- info: 'TrustIr.GenericCoro.PadViews.Controls.raised' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.Controls.raised

/-- info: 'TrustIr.GenericCoro.PadViews.Controls.typedCatch' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.Controls.typedCatch

/-- info: 'TrustIr.GenericCoro.PadViews.Controls.typed_catch_checks_exception_first' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.Controls.typed_catch_checks_exception_first

/-- info: 'TrustIr.GenericCoro.PadViews.Controls.typed_catch_keeps_refusal' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.Controls.typed_catch_keeps_refusal

/-- info: 'TrustIr.GenericCoro.PadViews.Controls.withoutPad' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.Controls.withoutPad

/-- info: 'TrustIr.GenericCoro.PadViews.PadView' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.PadView

/-- info: 'TrustIr.GenericCoro.PadViews.PadViewsAgree' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.PadViewsAgree

/-- info: 'TrustIr.GenericCoro.PadViews.closureTermWithContext_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.closureTermWithContext_fresh

/-- info: 'TrustIr.GenericCoro.PadViews.padView' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.padView

/-- info: 'TrustIr.GenericCoro.PadViews.semEnterPad_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.semEnterPad_congr

/-- info: 'TrustIr.GenericCoro.PadViews.semEnterPad_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.semEnterPad_fresh

/-- info: 'TrustIr.GenericCoro.PadViews.semResumeUnwind_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.semResumeUnwind_fresh

/-- info: 'TrustIr.GenericCoro.PadViews.stepTermUnwind_congr' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.stepTermUnwind_congr

/-- info: 'TrustIr.GenericCoro.PadViews.stepTermUnwind_fresh' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.stepTermUnwind_fresh

/-- info: 'TrustIr.GenericCoro.PadViews.stepTermWithContext_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.stepTermWithContext_congr

/-- info: 'TrustIr.GenericCoro.PadViews.stepTermWithContext_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.PadViews.stepTermWithContext_fresh

/-- info: 'TrustIr.GenericCoro.Prefix.evalTransfer_call_scoped_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalTransfer_call_scoped_congr

/-- info: 'TrustIr.GenericCoro.Prefix.evalTransfer_indirect_scoped_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalTransfer_indirect_scoped_congr

/-- info: 'TrustIr.GenericCoro.Prefix.evalTransfer_invokeIndirect_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalTransfer_invokeIndirect_succ

/-- info: 'TrustIr.GenericCoro.Prefix.evalTransfer_invoke_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.Prefix.evalTransfer_invoke_succ

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.actual_expanded_metadata_has_three_new_types' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.actual_expanded_metadata_has_three_new_types

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.actual_shadowed_row_retains_full_inference_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.actual_shadowed_row_retains_full_inference_contract

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.actual_source_inference_succeeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.actual_source_inference_succeeds

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.beforeRows' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.beforeRows

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.earlier' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.earlier

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.first_lookup_still_selects_earlier_duplicate' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.first_lookup_still_selects_earlier_duplicate

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.names' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.names

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.names.proof_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.names.proof_1

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.names.proof_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.names.proof_2

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.names.proof_3' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.names.proof_3

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.names.proof_4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.names.proof_4

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.names.proof_5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.names.proof_5

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.names.proof_6' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.names.proof_6

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.names.proof_7' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.names.proof_7

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.names.proof_8' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.names.proof_8

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.names.proof_9' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.names.proof_9

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.selected' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.selected

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.sourceGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.sourceGraph

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.targetGraph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.targetGraph

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.unused_raw_rows_are_not_declarations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.unused_raw_rows_are_not_declarations

/-- info: 'TrustIr.GenericCoro.RowInference.Controls.unused_raw_rows_reserve_the_actual_first_holes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.unused_raw_rows_reserve_the_actual_first_holes

/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.currentGraph' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.currentGraph

/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.earlier_raw_tails_are_no_longer_in_current_graph' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.earlier_raw_tails_are_no_longer_in_current_graph

/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterBlock' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterBlock

/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames

/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_1

/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_2

/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_3' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_3

/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_4

/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_5

/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_6' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_6

/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_7' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_7

/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_8' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_8

/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_9' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_9

/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterTarget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterTarget

/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.later_rewrite_keeps_dropped_raw_ids_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.later_rewrite_keeps_dropped_raw_ids_none

/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.later_target_identifiers_have_supported_origin' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.later_target_identifiers_have_supported_origin

/-- info: 'TrustIr.GenericCoro.RowInference.expandedRow_inference_except_generated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.expandedRow_inference_except_generated

/-- info: 'TrustIr.GenericCoro.RowInference.expandedRow_prefix_inference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.expandedRow_prefix_inference

/-- info: 'TrustIr.GenericCoro.RowInference.expandedRow_valueIds_supported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.expandedRow_valueIds_supported

/-- info: 'TrustIr.GenericCoro.RowInference.graphParams_expandedRow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.graphParams_expandedRow

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.Controls.abort_keeps_exact_unwind_error_state' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.Controls.abort_keeps_exact_unwind_error_state

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.Controls.callee_resource_error_is_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.Controls.callee_resource_error_is_exact

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.Controls.caller' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.Controls.caller

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.Controls.caller_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.Controls.caller_fresh

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.Controls.caught_unwind_restores_from_embedded_throw_world' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.Controls.caught_unwind_restores_from_embedded_throw_world

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.Controls.checkedCorrupt' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.Controls.checkedCorrupt

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.Controls.checker' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.Controls.checker

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.Controls.checker_unwind_is_not_caught_as_callee_unwind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.Controls.checker_unwind_is_not_caught_as_callee_unwind

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.Controls.continuation_private_result_effect' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.Controls.continuation_private_result_effect

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.Controls.corrupt' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.Controls.corrupt

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.Controls.corrupt_is_not_fresh' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.Controls.corrupt_is_not_fresh

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.Controls.nonfresh_callee_and_checker_still_keep_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.Controls.nonfresh_callee_and_checker_still_keep_fresh

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.Controls.normal' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.Controls.normal

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.Controls.poison_return_nonfresh_check_restores_complete_caller_frame' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.Controls.poison_return_nonfresh_check_restores_complete_caller_frame

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.Controls.privateResult' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.Controls.privateResult

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.Controls.privateResult_effect' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.Controls.privateResult_effect

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.Controls.returning' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.Controls.returning

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.Controls.unwind' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.Controls.unwind

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_congr_on_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_congr_on_fresh

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_effect_on_fresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_effect_on_fresh

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_keepsFresh' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_keepsFresh

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_run

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_run.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_run.match_1

/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_run.match_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_run.match_2

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.CapacityProgress' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.CapacityProgress

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Completion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Completion

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Completion.capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Completion.capacity

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Completion.capacity.inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Completion.capacity.inj

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Completion.capacity.injEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Completion.capacity.injEq

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Completion.capacity.sizeOf_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Completion.capacity.sizeOf_spec

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Completion.casesOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Completion.casesOn

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Completion.noConfusion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Completion.noConfusion

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Completion.noConfusionType' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Completion.noConfusionType

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Completion.ready' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Completion.ready

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Completion.ready.sizeOf_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Completion.ready.sizeOf_spec

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Completion.rec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Completion.rec

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Completion.recOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Completion.recOn

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.below

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.below.casesOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.below.casesOn

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.below.expand' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.below.expand

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.below.keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.below.keep

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.below.nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.below.nil

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.below.rec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.below.rec

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.casesOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.casesOn

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.expand' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.expand

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.history' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.history

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.history_count' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.history_count

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.keep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.keep

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.labels' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.labels

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.nil' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.nil

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.noSuspends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.noSuspends

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.params' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.params

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.rec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.rec

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.recOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.recOn

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.suspendCount_target_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.suspendCount_target_zero

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.traceTriple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.traceTriple

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Plans.trace_count' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Plans.trace_count

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Ready' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Ready

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Ready.match_1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Ready.match_1

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Result

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Result.casesOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Result.casesOn

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Result.completion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Result.completion

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Result.cursor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Result.cursor

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Result.mk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Result.mk

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Result.mk.inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Result.mk.inj

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Result.mk.injEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Result.mk.injEq

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Result.mk.sizeOf_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Result.mk.sizeOf_spec

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Result.noConfusion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Result.noConfusion

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Result.noConfusionType' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Result.noConfusionType

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Result.pending' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Result.pending

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Result.rec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Result.rec

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Result.recOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Result.recOn

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Result.rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Result.rows

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Result.trace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Result.trace

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Result.visits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Result.visits

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Rows' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Rows

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.Trace' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.Trace

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TraceControls.actual_duplicate_trace' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TraceControls.actual_duplicate_trace

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TraceControls.actual_first_occurrence_has_original_graph_names' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TraceControls.actual_first_occurrence_has_original_graph_names

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TraceControls.actual_later_occurrence_has_original_graph_names' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TraceControls.actual_later_occurrence_has_original_graph_names

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TraceControls.entry' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TraceControls.entry

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TraceControls.later_witness_retains_recorded_fields' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TraceControls.later_witness_retains_recorded_fields

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TraceControls.sourceRows' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TraceControls.sourceRows

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TraceControls.suspend' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TraceControls.suspend

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.capacity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.capacity

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.capacity.inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.capacity.inj

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.capacity.injEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.capacity.injEq

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.capacity.sizeOf_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.capacity.sizeOf_spec

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.casesOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.casesOn

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.noConfusion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.noConfusion

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.noConfusionType' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.noConfusionType

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.ready' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.ready

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.ready.inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.ready.inj

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.ready.injEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.ready.injEq

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.ready.sizeOf_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.ready.sizeOf_spec

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.rec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.rec

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.recOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.recOn

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleReservation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleReservation

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.after' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.after

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.capacity_excludes_triple' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.capacity_excludes_triple

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.casesOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.casesOn

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.history_bound' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.history_bound

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.mk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.mk

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.mk.inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.mk.inj

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.mk.injEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.mk.injEq

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.mk.sizeOf_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.mk.sizeOf_spec

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.monotone' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.monotone

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.noConfusion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.noConfusion

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.noConfusionType' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.noConfusionType

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.outcome' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.outcome

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.rec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.rec

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.recOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.recOn

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.visits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.visits

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.work' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.work

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.duplicate_labels_get_separate_triples' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.duplicate_labels_get_separate_triples

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.example_capacity_excludes_six' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.example_capacity_excludes_six

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.expandedEntry_terminator_noSuspend' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.expandedEntry_terminator_noSuspend

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.isSuspend' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.isSuspend

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.isSuspend.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.isSuspend.match_1

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRows' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRows

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.eq_1' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.eq_1

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.eq_2' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.eq_2

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.match_1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.match_1

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.match_2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.match_2

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop_capacity_progress' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop_capacity_progress

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop_history_bound' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop_history_bound

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop_ready' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop_ready

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop_work' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop_work

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRows_capacity_excludes_schedule' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRows_capacity_excludes_schedule

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRows_capacity_excludes_schedule.match_1' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRows_capacity_excludes_schedule.match_1

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRows_distinct' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRows_distinct

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRows_in_range' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRows_in_range

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRows_ready' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRows_ready

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRows_source_unused' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRows_source_unused

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRows_visit_census_bound' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRows_visit_census_bound

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRows_visit_domain_bound' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRows_visit_domain_bound

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRows_work' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRows_work

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.no_suspend_needs_no_fresh_names' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.no_suspend_needs_no_fresh_names

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.planAllBlocks' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.planAllBlocks

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.planAllBlocks_ready_noSuspends' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.planAllBlocks_ready_noSuspends

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.planAllBlocks_traceGraphNames' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.planAllBlocks_traceGraphNames

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_1' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_1

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_10' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_10

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_11' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_11

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_12' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_12

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_13' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_13

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_14' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_14

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_15' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_15

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_16' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_16

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_17' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_17

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_18' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_18

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_19' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_19

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_2

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_20' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_20

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_21' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_21

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_22' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_22

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_23' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_23

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_24' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_24

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_25' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_25

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_26' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_26

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_27' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_27

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_28' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_28

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_29' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_29

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_3' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_3

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_30' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_30

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_31' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_31

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_32' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_32

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_33' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_33

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_34' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_34

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_4' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_4

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_5' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_5

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_6' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_6

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_7' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_7

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_8' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_8

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_9' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_9

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reverseNames' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reverseNames

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.second_row_partial_capacity' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.second_row_partial_capacity

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.suspendCount' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.suspendCount

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.suspendCount.eq_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.suspendCount.eq_1

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.suspendCount.eq_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.suspendCount.eq_2

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.suspendCount.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.suspendCount.match_1

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.suspendCount_append' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.suspendCount_append

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.traceObservation' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.traceObservation

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.tripleObservation' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.tripleObservation

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.triple_held_cursor_does_not_restart' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.triple_held_cursor_does_not_restart

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.triple_one_success_capacity' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.triple_one_success_capacity

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.triple_ready_holes' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.triple_ready_holes

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.triple_two_success_capacity' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.triple_two_success_capacity

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.triple_zero_success_capacity' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.triple_zero_success_capacity

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.two_nonentry_occurrences' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.two_nonentry_occurrences

/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.two_nonentry_rows_are_actual_expandedEntry' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.two_nonentry_rows_are_actual_expandedEntry

/-- info: 'TrustIr.GenericCoroAllBlocksTransfer.PairedCallbacks' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksTransfer.PairedCallbacks

/-- info: 'TrustIr.GenericCoroAllBlocksTransfer.effect_refl' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksTransfer.effect_refl

/-- info: 'TrustIr.GenericCoroAllBlocksTransfer.evalTransfer_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksTransfer.evalTransfer_effect

/-- info: 'TrustIr.GenericCoroAllBlocksTransfer.invokeFrame_effect' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksTransfer.invokeFrame_effect

/-- info: 'TrustIr.GenericCoroAllBlocksTransfer.invokeIndirect_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksTransfer.invokeIndirect_effect

/-- info: 'TrustIr.GenericCoroAllBlocksTransfer.invokeNormal_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksTransfer.invokeNormal_effect

/-- info: 'TrustIr.GenericCoroAllBlocksTransfer.invokeUnwind_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksTransfer.invokeUnwind_effect

/-- info: 'TrustIr.GenericCoroAllBlocksTransfer.invoke_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksTransfer.invoke_effect

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Controls.actual_cleanup_entry_keeps_selector' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Controls.actual_cleanup_entry_keeps_selector

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Controls.cleanupSuspend' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Controls.cleanupSuspend

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Controls.duplicateRows' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Controls.duplicateRows

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Controls.duplicate_first_match_actual_names' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Controls.duplicate_first_match_actual_names

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Controls.duplicate_first_match_pad' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Controls.duplicate_first_match_pad

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Controls.duplicate_first_match_parameters' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Controls.duplicate_first_match_parameters

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Controls.emptySuspend' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Controls.emptySuspend

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Controls.empty_body_present_nonpad_stays_distinct_from_absence' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Controls.empty_body_present_nonpad_stays_distinct_from_absence

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Controls.empty_graph_lookup' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Controls.empty_graph_lookup

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Controls.empty_graph_views' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Controls.empty_graph_views

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Controls.keptFirstRows' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Controls.keptFirstRows

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Controls.missing_block_stays_absent' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Controls.missing_block_stays_absent

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Controls.present_nonpad_is_not_missing' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Controls.present_nonpad_is_not_missing

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Controls.retained_first_row_lookup_contract' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Controls.retained_first_row_lookup_contract

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Controls.retained_first_row_shadows_later_expansion' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Controls.retained_first_row_shadows_later_expansion

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Controls.shadow' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Controls.shadow

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Lookup' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Lookup

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Lookup.casesOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Lookup.casesOn

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Lookup.expanded' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Lookup.expanded

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Lookup.extend' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Lookup.extend

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Lookup.kept' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Lookup.kept

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Lookup.missing' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Lookup.missing

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Lookup.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Lookup.rec

/-- info: 'TrustIr.GenericCoroAllBlocksViews.Lookup.recOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.Lookup.recOn

/-- info: 'TrustIr.GenericCoroAllBlocksViews.cfg_interface' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.cfg_interface

/-- info: 'TrustIr.GenericCoroAllBlocksViews.cfg_params' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.cfg_params

/-- info: 'TrustIr.GenericCoroAllBlocksViews.interface_rows' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.interface_rows

/-- info: 'TrustIr.GenericCoroAllBlocksViews.lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.lookup

/-- info: 'TrustIr.GenericCoroAllBlocksViews.lookup_none_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.lookup_none_iff

/-- info: 'TrustIr.GenericCoroAllBlocksViews.lookup_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.lookup_some

/-- info: 'TrustIr.GenericCoroAllBlocksViews.padViews' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.padViews

/-- info: 'TrustIr.GenericCoroAllBlocksViews.planAllBlocks_ready_lookup' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.planAllBlocks_ready_lookup

/-- info: 'TrustIr.GenericCoroAllBlocksViews.planAllBlocks_ready_padViews' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.planAllBlocks_ready_padViews

/-- info: 'TrustIr.GenericCoroAllBlocksViews.planAllBlocks_ready_params' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.planAllBlocks_ready_params

/-- info: 'TrustIr.GenericCoroAllBlocksViews.semEnterPad_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.semEnterPad_eq

/-- info: 'TrustIr.GenericCoroAllBlocksViews.stepTermUnwind_eq' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksViews.stepTermUnwind_eq

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.below

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.bound

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.casesOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.casesOn

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.contains_of_member' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.contains_of_member

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.correct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.correct

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.distinct' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.distinct

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.index' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.index

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.member_of_contains' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.member_of_contains

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.mk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.mk

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.mk.inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.mk.inj

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.mk.injEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.mk.injEq

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.mk.sizeOf_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.mk.sizeOf_spec

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.next' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.next

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.next_le_census' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.next_le_census

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.noConfusion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.noConfusion

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.noConfusionType' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.noConfusionType

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.rec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.rec

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.recOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.recOn

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.reserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.reserved

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.reservedBefore' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.reservedBefore

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.reservedBound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.reservedBound

/-- info: 'TrustIr.GenericCoroFreshCursor.Cursor.reservedUnused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Cursor.reservedUnused

/-- info: 'TrustIr.GenericCoroFreshCursor.Distinct' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Distinct

/-- info: 'TrustIr.GenericCoroFreshCursor.Distinct.below' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Distinct.below

/-- info: 'TrustIr.GenericCoroFreshCursor.Distinct.below.casesOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Distinct.below.casesOn

/-- info: 'TrustIr.GenericCoroFreshCursor.Distinct.below.cons' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Distinct.below.cons

/-- info: 'TrustIr.GenericCoroFreshCursor.Distinct.below.nil' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Distinct.below.nil

/-- info: 'TrustIr.GenericCoroFreshCursor.Distinct.below.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Distinct.below.rec

/-- info: 'TrustIr.GenericCoroFreshCursor.Distinct.brecOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Distinct.brecOn

/-- info: 'TrustIr.GenericCoroFreshCursor.Distinct.casesOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Distinct.casesOn

/-- info: 'TrustIr.GenericCoroFreshCursor.Distinct.cons' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Distinct.cons

/-- info: 'TrustIr.GenericCoroFreshCursor.Distinct.length_le_of_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Distinct.length_le_of_subset

/-- info: 'TrustIr.GenericCoroFreshCursor.Distinct.nil' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Distinct.nil

/-- info: 'TrustIr.GenericCoroFreshCursor.Distinct.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Distinct.rec

/-- info: 'TrustIr.GenericCoroFreshCursor.Distinct.recOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Distinct.recOn

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.after' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.after

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.casesOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.casesOn

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.exhausted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.exhausted

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.fresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.fresh

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.fullCursor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.fullCursor

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.full_before' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.full_before

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.history' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.history

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.inRange' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.inRange

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.key' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.key

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.keyCursor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.keyCursor

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.length' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.length

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.member_preserved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.member_preserved

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.mk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.mk

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.mk.inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.mk.inj

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.mk.injEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.mk.injEq

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.mk.sizeOf_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.mk.sizeOf_spec

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.monotone' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.monotone

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.noConfusion' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.noConfusion

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.noConfusionType' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.noConfusionType

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.rec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.rec

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.recOn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.recOn

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.visits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.visits

/-- info: 'TrustIr.GenericCoroFreshCursor.Reservation.work' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Reservation.work

/-- info: 'TrustIr.GenericCoroFreshCursor.Search' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Search

/-- info: 'TrustIr.GenericCoroFreshCursor.Search.casesOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Search.casesOn

/-- info: 'TrustIr.GenericCoroFreshCursor.Search.key' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Search.key

/-- info: 'TrustIr.GenericCoroFreshCursor.Search.mk' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Search.mk

/-- info: 'TrustIr.GenericCoroFreshCursor.Search.mk.inj' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Search.mk.inj

/-- info: 'TrustIr.GenericCoroFreshCursor.Search.mk.injEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Search.mk.injEq

/-- info: 'TrustIr.GenericCoroFreshCursor.Search.mk.sizeOf_spec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Search.mk.sizeOf_spec

/-- info: 'TrustIr.GenericCoroFreshCursor.Search.next' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Search.next

/-- info: 'TrustIr.GenericCoroFreshCursor.Search.noConfusion' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Search.noConfusion

/-- info: 'TrustIr.GenericCoroFreshCursor.Search.noConfusionType' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Search.noConfusionType

/-- info: 'TrustIr.GenericCoroFreshCursor.Search.rec' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Search.rec

/-- info: 'TrustIr.GenericCoroFreshCursor.Search.recOn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Search.recOn

/-- info: 'TrustIr.GenericCoroFreshCursor.Search.visits' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.Search.visits

/-- info: 'TrustIr.GenericCoroFreshCursor.capacity_excludes_schedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.capacity_excludes_schedule

/-- info: 'TrustIr.GenericCoroFreshCursor.duplicates_do_not_add_candidate_visits' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.duplicates_do_not_add_candidate_visits

/-- info: 'TrustIr.GenericCoroFreshCursor.exact_capacity' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.exact_capacity

/-- info: 'TrustIr.GenericCoroFreshCursor.exhausted_cursor_needs_no_repeat_visit' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.exhausted_cursor_needs_no_repeat_visit

/-- info: 'TrustIr.GenericCoroFreshCursor.first_hole' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.first_hole

/-- info: 'TrustIr.GenericCoroFreshCursor.grouped_work' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.grouped_work

/-- info: 'TrustIr.GenericCoroFreshCursor.grouped_work_control' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.grouped_work_control

/-- info: 'TrustIr.GenericCoroFreshCursor.high_keys_do_not_force_a_high_cursor' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.high_keys_do_not_force_a_high_cursor

/-- info: 'TrustIr.GenericCoroFreshCursor.next_hole_skips_no_old_prefix' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.next_hole_skips_no_old_prefix

/-- info: 'TrustIr.GenericCoroFreshCursor.observe' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.observe

/-- info: 'TrustIr.GenericCoroFreshCursor.prepare' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.prepare

/-- info: 'TrustIr.GenericCoroFreshCursor.prepare.proof_1' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.prepare.proof_1

/-- info: 'TrustIr.GenericCoroFreshCursor.prepare.proof_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.prepare.proof_2

/-- info: 'TrustIr.GenericCoroFreshCursor.prepare.proof_3' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.prepare.proof_3

/-- info: 'TrustIr.GenericCoroFreshCursor.prepare.proof_4' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.prepare.proof_4

/-- info: 'TrustIr.GenericCoroFreshCursor.prepareU32' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.prepareU32

/-- info: 'TrustIr.GenericCoroFreshCursor.prepare_many_visit_census_bound' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.prepare_many_visit_census_bound

/-- info: 'TrustIr.GenericCoroFreshCursor.requests_after_capacity_add_no_candidate_visits' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.requests_after_capacity_add_no_candidate_visits

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_1' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_1

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_10' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_10

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_11' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_11

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_12' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_12

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_13' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_13

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_14' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_14

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_15' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_15

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_16' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_16

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_17' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_17

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_18' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_18

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_19' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_19

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_2

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_20' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_20

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_21' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_21

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_22' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_22

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_23' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_23

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_24' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_24

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_25' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_25

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_26' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_26

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_27' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_27

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_28' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_28

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_29' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_29

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_3' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_3

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_30' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_30

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_31' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_31

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_32' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_32

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_33' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_33

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_4' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_4

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_5' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_5

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_6' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_6

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_7' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_7

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_8

/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_9' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_9

/-- info: 'TrustIr.GenericCoroFreshCursor.reserveMany' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserveMany

/-- info: 'TrustIr.GenericCoroFreshCursor.reserveManyLoop' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserveManyLoop

/-- info: 'TrustIr.GenericCoroFreshCursor.reserveManyLoop.eq_1' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserveManyLoop.eq_1

/-- info: 'TrustIr.GenericCoroFreshCursor.reserveManyLoop.eq_2' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserveManyLoop.eq_2

/-- info: 'TrustIr.GenericCoroFreshCursor.reserveManyLoop.match_1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserveManyLoop.match_1

/-- info: 'TrustIr.GenericCoroFreshCursor.reserveManyLoop_capacity' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserveManyLoop_capacity

/-- info: 'TrustIr.GenericCoroFreshCursor.reserveManyLoop_length' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserveManyLoop_length

/-- info: 'TrustIr.GenericCoroFreshCursor.reserveManyLoop_member_preserved' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserveManyLoop_member_preserved

/-- info: 'TrustIr.GenericCoroFreshCursor.reserveManyLoop_work' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserveManyLoop_work

/-- info: 'TrustIr.GenericCoroFreshCursor.reserveMany_capacity' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserveMany_capacity

/-- info: 'TrustIr.GenericCoroFreshCursor.reserveMany_distinct' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserveMany_distinct

/-- info: 'TrustIr.GenericCoroFreshCursor.reserveMany_in_range' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserveMany_in_range

/-- info: 'TrustIr.GenericCoroFreshCursor.reserveMany_source_unused' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserveMany_source_unused

/-- info: 'TrustIr.GenericCoroFreshCursor.reserveMany_visit_domain_bound' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserveMany_visit_domain_bound

/-- info: 'TrustIr.GenericCoroFreshCursor.reserveMany_work' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserveMany_work

/-- info: 'TrustIr.GenericCoroFreshCursor.seek' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.seek

/-- info: 'TrustIr.GenericCoroFreshCursor.seek.eq_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.seek.eq_1

/-- info: 'TrustIr.GenericCoroFreshCursor.seek.eq_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.seek.eq_2

/-- info: 'TrustIr.GenericCoroFreshCursor.seek.match_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.seek.match_1

/-- info: 'TrustIr.GenericCoroFreshCursor.seek_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.seek_before

/-- info: 'TrustIr.GenericCoroFreshCursor.seek_key' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.seek_key

/-- info: 'TrustIr.GenericCoroFreshCursor.seek_next_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.seek_next_none

/-- info: 'TrustIr.GenericCoroFreshCursor.seek_next_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.seek_next_some

/-- info: 'TrustIr.GenericCoroFreshCursor.seek_work' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.seek_work

/-- info: 'TrustIr.GenericCoroFreshCursor.two_free_ids_exclude_three' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.two_free_ids_exclude_three

/-- info: 'TrustIr.GenericCoroFreshCursor.zero_domain_needs_no_candidate_visit' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.zero_domain_needs_no_candidate_visit


-- Runtime binding-frame identity, snapshot invalidation and no-revival laws.
/-- info: 'TrustIr.FrameLifetime.close_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.close_run

/-- info: 'TrustIr.FrameLifetime.open_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.open_run

/-- info: 'TrustIr.FrameLifetime.bind_run' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.bind_run

/-- info: 'TrustIr.FrameLifetime.close_alias_load' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.close_alias_load

/-- info: 'TrustIr.FrameLifetime.close_alias_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.close_alias_bind

/-- info: 'TrustIr.FrameLifetime.close_alias_double_close' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.close_alias_double_close

/-- info: 'TrustIr.FrameLifetime.bind_close_load' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.bind_close_load

/-- info: 'TrustIr.FrameLifetime.open_does_not_revive_alias' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.open_does_not_revive_alias

/-- info: 'TrustIr.FrameLifetime.HistoryExtends.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.HistoryExtends.trans

/-- info: 'TrustIr.FrameLifetime.open_success_history' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.open_success_history

/-- info: 'TrustIr.FrameLifetime.history_restore' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.history_restore

/-- info: 'TrustIr.FrameLifetime.forged_future_identity_can_revive' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.forged_future_identity_can_revive

/-- info: 'TrustIr.FrameLifetime.nonfresh_ssa_can_overwrite_snapshot' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.nonfresh_ssa_can_overwrite_snapshot


-- Exact zero-gate bit/byte permutations and original integer unary semantics.
/-- info: 'TrustIr.AYGateCNF.WordCode.rewire_check' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.rewire_check

/-- info: 'TrustIr.AYGateCNF.WordCode.bitReverse_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.bitReverse_value

/-- info: 'TrustIr.AYGateCNF.WordCode.byteSwap_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.byteSwap_value

/-- info: 'TrustIr.AYGateCNF.WordCode.bitReverse_involution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.bitReverse_involution

/-- info: 'TrustIr.AYGateCNF.WordCode.byteSwap_involution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.byteSwap_involution

/-- info: 'TrustIr.AYGateCNF.WordCode.bitReverse_boundInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.bitReverse_boundInput

/-- info: 'TrustIr.AYGateCNF.WordCode.byteSwap_boundInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.byteSwap_boundInput

/-- info: 'TrustIr.AYGateCNF.WordCode.byteSwap_boundCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.byteSwap_boundCheck


-- Canonical extract/concat permutation targets and checked request receipts.
/-- info: 'TrustIr.TrustIrExpr.SMTTerm.reverseChunks_toNat' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTTerm.reverseChunks_toNat

/-- info: 'TrustIr.TrustIrExpr.SMTTerm.reverseChunks_bindings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTTerm.reverseChunks_bindings

/-- info: 'TrustIr.TrustIrExpr.SMTCheckedTerm.bitReverse_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTCheckedTerm.bitReverse_request

/-- info: 'TrustIr.TrustIrExpr.SMTCheckedTerm.byteSwap_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTCheckedTerm.byteSwap_request

/-- info: 'TrustIr.AYGateCNF.WordCode.bitReverse_checkedTarget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.bitReverse_checkedTarget

/-- info: 'TrustIr.AYGateCNF.WordCode.byteSwap_checkedTarget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.byteSwap_checkedTarget

/-- info: 'TrustIr.AYGateCNF.WordCode.composeBitReverse_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.composeBitReverse_target


-- Source-indexed scalar permutation instructions, input guards and actual receipts.
/-- info: 'TrustIr.IntegerPermutationOp.target_semIntUnOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.IntegerPermutationOp.target_semIntUnOp

/-- info: 'TrustIr.int_unop_step_result' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.int_unop_step_result

/-- info: 'TrustIr.int_unop_missing_operand' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.int_unop_missing_operand

/-- info: 'TrustIr.int_unop_guard_error' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.int_unop_guard_error

/-- info: 'TrustIr.IntegerPermutationSubject.ofType_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.IntegerPermutationSubject.ofType_identity

/-- info: 'TrustIr.IntegerPermutationSubject.checkedCode_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.IntegerPermutationSubject.checkedCode_eq_some

/-- info: 'TrustIr.IntegerPermutationSubject.checkedCode_number' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.IntegerPermutationSubject.checkedCode_number

/-- info: 'TrustIr.IntegerPermutationSite.request_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.IntegerPermutationSite.request_outcome

/-- info: 'TrustIr.IntegerPermutationSite.request_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.IntegerPermutationSite.request_state

/-- info: 'TrustIr.IntegerPermutationSite.gate_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.IntegerPermutationSite.gate_outcome

/-- info: 'TrustIr.IntegerPermutationSite.gate_request_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.IntegerPermutationSite.gate_request_value


-- Balanced population-count target and actual scalar opcode.
/-- info: 'TrustIr.TrustIrExpr.populationBits_capacity' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.populationBits_capacity

/-- info: 'TrustIr.TrustIrExpr.populationSlice_semantics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.populationSlice_semantics

/-- info: 'TrustIr.TrustIrExpr.PopulationPlan.target_toNat' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.PopulationPlan.target_toNat

/-- info: 'TrustIr.TrustIrExpr.PopulationPlan.target_bindings' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.PopulationPlan.target_bindings

/-- info: 'TrustIr.TrustIrExpr.SMTCheckedTerm.popCount_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTCheckedTerm.popCount_toNat

/-- info: 'TrustIr.TrustIrExpr.SMTCheckedTerm.popCount_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTCheckedTerm.popCount_bound

/-- info: 'TrustIr.TrustIrExpr.SMTCheckedTerm.popCount_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTCheckedTerm.popCount_request

/-- info: 'TrustIr.TrustIrExpr.SMTCheckedTerm.popCount_semIntUnOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTCheckedTerm.popCount_semIntUnOp


-- Original source-indexed scalar CtPop requests and full state.
/-- info: 'TrustIr.PopulationSubject.ofType_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PopulationSubject.ofType_identity

/-- info: 'TrustIr.PopulationSubject.request_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PopulationSubject.request_target

/-- info: 'TrustIr.PopulationSubject.request_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PopulationSubject.request_bound

/-- info: 'TrustIr.PopulationSubject.request_semIntUnOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PopulationSubject.request_semIntUnOp

/-- info: 'TrustIr.PopulationSite.bare_request_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PopulationSite.bare_request_outcome

/-- info: 'TrustIr.PopulationSite.request_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PopulationSite.request_outcome

/-- info: 'TrustIr.PopulationSite.request_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PopulationSite.request_state

/-- info: 'TrustIr.PopulationSite.missing_operand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PopulationSite.missing_operand

/-- info: 'TrustIr.PopulationSite.guard_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PopulationSite.guard_error


-- Balanced population-count gate programs and actual source receipts.
/-- info: 'TrustIr.AYGateCNF.WordCode.populationExtend_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.populationExtend_check

/-- info: 'TrustIr.AYGateCNF.WordCode.populationExtend_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.populationExtend_toNat

/-- info: 'TrustIr.AYGateCNF.WordCode.populationLeaf_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.populationLeaf_check

/-- info: 'TrustIr.AYGateCNF.WordCode.populationLeaf_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.populationLeaf_value

/-- info: 'TrustIr.TrustIrExpr.PopulationPlan.code_check' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.PopulationPlan.code_check

/-- info: 'TrustIr.TrustIrExpr.PopulationPlan.code_toNat' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.PopulationPlan.code_toNat

/-- info: 'TrustIr.PopulationSubject.code_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PopulationSubject.code_check

/-- info: 'TrustIr.PopulationSubject.code_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PopulationSubject.code_toNat

/-- info: 'TrustIr.PopulationSubject.checkedCode_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PopulationSubject.checkedCode_eq_some

/-- info: 'TrustIr.PopulationSubject.checkedCode_number' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PopulationSubject.checkedCode_number

/-- info: 'TrustIr.PopulationSite.gate_request_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PopulationSite.gate_request_value

/-- info: 'TrustIr.PopulationSite.gate_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PopulationSite.gate_outcome


-- Exact leading/trailing zero-count targets and actual requests.
/-- info: 'TrustIr.TrustIrExpr.zeroScan_leading' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.zeroScan_leading

/-- info: 'TrustIr.TrustIrExpr.zeroScan_trailing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.zeroScan_trailing

/-- info: 'TrustIr.TrustIrExpr.zeroScan_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.zeroScan_complete

/-- info: 'TrustIr.TrustIrExpr.SMTTerm.zeroBitSet_eval' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTTerm.zeroBitSet_eval

/-- info: 'TrustIr.TrustIrExpr.SMTTerm.zeroCountScan_toNat' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTTerm.zeroCountScan_toNat

/-- info: 'TrustIr.TrustIrExpr.SMTTerm.zeroCountScan_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTTerm.zeroCountScan_wellFormed

/-- info: 'TrustIr.TrustIrExpr.SMTTerm.zeroCountScan_bindings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTTerm.zeroCountScan_bindings

/-- info: 'TrustIr.TrustIrExpr.SMTCheckedTerm.zeroCount_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTCheckedTerm.zeroCount_toNat

/-- info: 'TrustIr.TrustIrExpr.SMTCheckedTerm.zeroCount_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTCheckedTerm.zeroCount_bound

/-- info: 'TrustIr.TrustIrExpr.SMTCheckedTerm.zeroCount_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTCheckedTerm.zeroCount_zero

/-- info: 'TrustIr.TrustIrExpr.SMTCheckedTerm.zeroCount_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTCheckedTerm.zeroCount_request

/-- info: 'TrustIr.TrustIrExpr.SMTCheckedTerm.zeroCount_semIntUnOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTCheckedTerm.zeroCount_semIntUnOp


-- Original leading/trailing zero-count instruction requests and state.
/-- info: 'TrustIr.ZeroCountSubject.ofType_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ZeroCountSubject.ofType_identity

/-- info: 'TrustIr.ZeroCountSubject.request_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ZeroCountSubject.request_target

/-- info: 'TrustIr.ZeroCountSubject.request_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ZeroCountSubject.request_bound

/-- info: 'TrustIr.ZeroCountSubject.request_semIntUnOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ZeroCountSubject.request_semIntUnOp

/-- info: 'TrustIr.ZeroCountSite.bare_request_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ZeroCountSite.bare_request_outcome

/-- info: 'TrustIr.ZeroCountSite.request_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ZeroCountSite.request_outcome

/-- info: 'TrustIr.ZeroCountSite.request_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ZeroCountSite.request_state

/-- info: 'TrustIr.ZeroCountSite.missing_operand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ZeroCountSite.missing_operand

/-- info: 'TrustIr.ZeroCountSite.guard_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ZeroCountSite.guard_error

/-- info: 'TrustIr.ZeroCountSubject.request_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ZeroCountSubject.request_zero


-- Narrow leading/trailing zero-count gate scans and original outcomes.
/-- info: 'TrustIr.AYGateCNF.WordCode.chooseConstant_check' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.chooseConstant_check

/-- info: 'TrustIr.AYGateCNF.WordCode.chooseConstant_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.chooseConstant_value

/-- info: 'TrustIr.AYGateCNF.WordCode.chooseConstant_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYGateCNF.WordCode.chooseConstant_length

/-- info: 'TrustIr.TrustIrExpr.ZeroCountDirection.scanCode_check' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.ZeroCountDirection.scanCode_check

/-- info: 'TrustIr.TrustIrExpr.ZeroCountDirection.scanCode_toNat' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.ZeroCountDirection.scanCode_toNat

/-- info: 'TrustIr.TrustIrExpr.ZeroCountDirection.scanCode_length' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.ZeroCountDirection.scanCode_length

/-- info: 'TrustIr.ZeroCountSubject.code_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ZeroCountSubject.code_check

/-- info: 'TrustIr.ZeroCountSubject.code_toNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ZeroCountSubject.code_toNat

/-- info: 'TrustIr.ZeroCountSubject.checkedCode_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ZeroCountSubject.checkedCode_eq_some

/-- info: 'TrustIr.ZeroCountSubject.checkedCode_number' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ZeroCountSubject.checkedCode_number

/-- info: 'TrustIr.ZeroCountSite.gate_request_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ZeroCountSite.gate_request_value

/-- info: 'TrustIr.ZeroCountSite.gate_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ZeroCountSite.gate_outcome


-- Original production body publication of actual unary requests/gates.
/-- info: 'TrustIr.unaryBody_of_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.unaryBody_of_step

/-- info: 'TrustIr.unaryBody_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.unaryBody_error

/-- info: 'TrustIr.IntegerPermutationSite.body_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.IntegerPermutationSite.body_request

/-- info: 'TrustIr.IntegerPermutationSite.body_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.IntegerPermutationSite.body_gate

/-- info: 'TrustIr.PopulationSite.body_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PopulationSite.body_request

/-- info: 'TrustIr.PopulationSite.body_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PopulationSite.body_gate

/-- info: 'TrustIr.ZeroCountSite.body_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ZeroCountSite.body_request

/-- info: 'TrustIr.ZeroCountSite.body_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ZeroCountSite.body_gate


-- Complete source-indexed unary body replay and continuation.
/-- info: 'TrustIr.AYUnaryReplay.Site.positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.Site.positive

/-- info: 'TrustIr.AYUnaryReplay.Site.body_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.Site.body_request

/-- info: 'TrustIr.AYUnaryReplay.Site.body_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.Site.body_error

/-- info: 'TrustIr.AYUnaryReplay.Node.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.Node.correct

/-- info: 'TrustIr.AYUnaryReplay.Trace.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.Trace.correct

/-- info: 'TrustIr.AYUnaryReplay.Trace.built_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.Trace.built_correct

/-- info: 'TrustIr.AYUnaryReplay.Trace.continuation_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.Trace.continuation_correct

/-- info: 'TrustIr.AYUnaryReplay.Trace.visited_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.Trace.visited_le


-- Actual CFG Return-block replay, parameter binding and fuel precedence.
/-- info: 'TrustIr.AYUnaryReplay.evalLayer_return' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.evalLayer_return

/-- info: 'TrustIr.AYUnaryReplay.ReturnBlock.layer_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.ReturnBlock.layer_correct

/-- info: 'TrustIr.AYUnaryReplay.ReturnBlock.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.ReturnBlock.correct

/-- info: 'TrustIr.AYUnaryReplay.ReturnBlock.built_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.ReturnBlock.built_correct


-- Original control syntax, bounded CFG replay and fuel precedence.
/-- info: 'TrustIr.AYUnaryReplay.Control.stepTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.Control.stepTerm

/-- info: 'TrustIr.AYUnaryReplay.Prefix.control_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.Prefix.control_error

/-- info: 'TrustIr.AYUnaryReplay.Prefix.unreachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.Prefix.unreachable

/-- info: 'TrustIr.AYUnaryReplay.Prefix.transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.Prefix.transfer

/-- info: 'TrustIr.AYUnaryReplay.CFGTrace.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.CFGTrace.correct

/-- info: 'TrustIr.AYUnaryReplay.CFGTrace.blocks_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.CFGTrace.blocks_le

/-- info: 'TrustIr.AYUnaryReplay.CFGTrace.build_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.CFGTrace.build_zero

/-- info: 'TrustIr.AYUnaryReplay.CFGTrace.built_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.CFGTrace.built_correct

/-- info: 'TrustIr.FrameLifetime.mintedValue_iff_shape' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.mintedValue_iff_shape

/-- info: 'TrustIr.FrameLifetime.values_handles' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.values_handles

/-- info: 'TrustIr.FrameLifetime.WellMintedState.open_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.open_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.bind_success' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.bind_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.load_success' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.load_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.close_success' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.close_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.restore' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.restore

/-- info: 'TrustIr.FrameLifetime.nested_future_rejected' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.nested_future_rejected

/-- info: 'TrustIr.FrameLifetime.SlotsTyped.length' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.SlotsTyped.length

/-- info: 'TrustIr.FrameLifetime.SlotsTyped.lookup' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.SlotsTyped.lookup

/-- info: 'TrustIr.FrameLifetime.SlotsTyped.update' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.SlotsTyped.update

/-- info: 'TrustIr.FrameLifetime.open_success_signature' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.open_success_signature

/-- info: 'TrustIr.FrameLifetime.bind_success_signature' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.bind_success_signature

/-- info: 'TrustIr.FrameLifetime.load_success_declared_signature' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.load_success_declared_signature

/-- info: 'TrustIr.FrameLifetime.load_success_signature' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.load_success_signature

/-- info: 'TrustIr.FrameLifetime.close_success_signature' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.close_success_signature

/-- info: 'TrustIr.FrameLifetime.requested_type_needs_validation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.requested_type_needs_validation

/-- info: 'TrustIr.FrameLifetime.inserted_type_needs_validation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.inserted_type_needs_validation

/-- info: 'TrustIr.FrameLifetime.single_publication_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.single_publication_run

/-- info: 'TrustIr.FrameLifetime.WellMintedState.single_publication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.single_publication

/-- info: 'TrustIr.FrameLifetime.result_checks_success_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.result_checks_success_state

/-- info: 'TrustIr.FrameLifetime.WellMintedState.bind_value_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.bind_value_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.frame_step_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.frame_step_success

/-- info: 'TrustIr.FrameLifetime.frame_body_computed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.frame_body_computed

/-- info: 'TrustIr.FrameLifetime.frame_body_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.frame_body_error

/-- info: 'TrustIr.FrameLifetime.WellMintedState.frame_body_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.frame_body_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.frame_body_list_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.frame_body_list_success

/-- info: 'TrustIr.FrameLifetime.published_frame_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.published_frame_roundtrip

/-- info: 'TrustIr.FrameLifetime.WellMintedState.params_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.params_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.checked_params_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.checked_params_success

/-- info: 'TrustIr.FrameLifetime.lookup_args_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.lookup_args_success

/-- info: 'TrustIr.FrameLifetime.br_transfer_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.br_transfer_success

/-- info: 'TrustIr.FrameLifetime.cond_transfer_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.cond_transfer_success

/-- info: 'TrustIr.FrameLifetime.switch_transfer_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.switch_transfer_success

/-- info: 'TrustIr.FrameLifetime.return_transfer_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.return_transfer_success

/-- info: 'TrustIr.FrameLifetime.FrameControl.stepTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameControl.stepTerm

/-- info: 'TrustIr.FrameLifetime.FrameControl.action_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameControl.action_success

/-- info: 'TrustIr.FrameLifetime.FrameControl.term_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameControl.term_success

/-- info: 'TrustIr.FrameLifetime.frame_layer_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.frame_layer_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.frame_cfg_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.frame_cfg_success

/-- info: 'TrustIr.FrameLifetime.transfer_example_grammar' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.transfer_example_grammar

/-- info: 'TrustIr.FrameLifetime.incoming_identity_premise_needed' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.incoming_identity_premise_needed

/-- info: 'TrustIr.FrameLifetime.WellMintedState.fresh_success' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.fresh_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.copy_step_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.copy_step_success

/-- info: 'TrustIr.FrameLifetime.select_lanes_minted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.select_lanes_minted

/-- info: 'TrustIr.FrameLifetime.vector_select_minted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.vector_select_minted

/-- info: 'TrustIr.FrameLifetime.select_step_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.select_step_eq

/-- info: 'TrustIr.FrameLifetime.select_transport_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.select_transport_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.select_step_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.select_step_success

/-- info: 'TrustIr.FrameLifetime.mintedValue_int' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.mintedValue_int

/-- info: 'TrustIr.FrameLifetime.mintedValue_float' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.mintedValue_float

/-- info: 'TrustIr.FrameLifetime.mintedValue_null' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.mintedValue_null

/-- info: 'TrustIr.FrameLifetime.unary_lane_minted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.unary_lane_minted

/-- info: 'TrustIr.FrameLifetime.unary_lanes_minted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.unary_lanes_minted

/-- info: 'TrustIr.FrameLifetime.unary_value_minted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.unary_value_minted

/-- info: 'TrustIr.FrameLifetime.WellMintedState.unary_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.unary_success

/-- info: 'TrustIr.FrameLifetime.bool_binary_minted' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.bool_binary_minted

/-- info: 'TrustIr.FrameLifetime.binary_lane_minted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.binary_lane_minted

/-- info: 'TrustIr.FrameLifetime.binary_lanes_minted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.binary_lanes_minted

/-- info: 'TrustIr.FrameLifetime.binary_value_minted' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.binary_value_minted

/-- info: 'TrustIr.FrameLifetime.WellMintedState.of_choice_erasure' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.of_choice_erasure

/-- info: 'TrustIr.FrameLifetime.WellMintedState.binary_success' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.binary_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.bool_binary_success' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.bool_binary_success

/-- info: 'TrustIr.FrameLifetime.binary_step_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.binary_step_eq

/-- info: 'TrustIr.FrameLifetime.WellMintedState.binary_action_success' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.binary_action_success


/-- info: 'TrustIr.FrameLifetime.WellMintedState.bind_result_dests_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.bind_result_dests_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.bind_values_core_success' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.bind_values_core_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.bind_values_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.bind_values_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.bind_instruction_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.bind_instruction_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.overflow_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.overflow_success

/-- info: 'TrustIr.FrameLifetime.integer_compare_lanes_minted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.integer_compare_lanes_minted

/-- info: 'TrustIr.FrameLifetime.bool_compare_lanes_minted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.bool_compare_lanes_minted

/-- info: 'TrustIr.FrameLifetime.integer_compare_value_minted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.integer_compare_value_minted

/-- info: 'TrustIr.FrameLifetime.float_compare_lanes_minted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.float_compare_lanes_minted

/-- info: 'TrustIr.FrameLifetime.float_compare_value_minted' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.float_compare_value_minted

/-- info: 'TrustIr.FrameLifetime.WellMintedState.integer_compare_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.integer_compare_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.float_compare_success' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.float_compare_success

/-- info: 'TrustIr.FrameLifetime.mintedValue_pointer' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.mintedValue_pointer

/-- info: 'TrustIr.FrameLifetime.WellMintedState.cast_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.cast_success

/-- info: 'TrustIr.FrameLifetime.field_get_minted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.field_get_minted

/-- info: 'TrustIr.FrameLifetime.field_set_minted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.field_set_minted

/-- info: 'TrustIr.FrameLifetime.element_get_minted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.element_get_minted

/-- info: 'TrustIr.FrameLifetime.element_set_minted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.element_set_minted

/-- info: 'TrustIr.FrameLifetime.array_from_lanes_minted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.array_from_lanes_minted

/-- info: 'TrustIr.FrameLifetime.array_uniform_minted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.array_uniform_minted

/-- info: 'TrustIr.FrameLifetime.vector_element_get_minted' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.vector_element_get_minted

/-- info: 'TrustIr.FrameLifetime.vector_element_set_minted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.vector_element_set_minted

/-- info: 'TrustIr.FrameLifetime.lookup_lanes_success' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.lookup_lanes_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.make_aggregate_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.make_aggregate_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.array_splat_success' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.array_splat_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.extract_field_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.extract_field_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.insert_field_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.insert_field_success

/-- info: 'TrustIr.FrameLifetime.element_index_success_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.element_index_success_state

/-- info: 'TrustIr.FrameLifetime.WellMintedState.extract_element_success' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.extract_element_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.insert_element_success' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.insert_element_success

/-- info: 'TrustIr.FrameLifetime.record_lanes_minted' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.record_lanes_minted

/-- info: 'TrustIr.FrameLifetime.enum_lanes_minted' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.enum_lanes_minted

/-- info: 'TrustIr.FrameLifetime.contextual_aggregate_value_minted' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.contextual_aggregate_value_minted

/-- info: 'TrustIr.FrameLifetime.contextual_array_value_minted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.contextual_array_value_minted

/-- info: 'TrustIr.FrameLifetime.contextual_closure_value_minted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.contextual_closure_value_minted

/-- info: 'TrustIr.FrameLifetime.WellMintedState.make_aggregate_step_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.make_aggregate_step_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.make_closure_step_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.make_closure_step_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.array_splat_step_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.array_splat_step_success

/-- info: 'TrustIr.FrameLifetime.closure_extract_minted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.closure_extract_minted

/-- info: 'TrustIr.FrameLifetime.closure_insert_minted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.closure_insert_minted

/-- info: 'TrustIr.FrameLifetime.WellMintedState.extract_field_step_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.extract_field_step_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.insert_field_step_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.insert_field_step_success

/-- info: 'TrustIr.FrameLifetime.pointer_data_minted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.pointer_data_minted

/-- info: 'TrustIr.FrameLifetime.pointer_metadata_minted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.pointer_metadata_minted

/-- info: 'TrustIr.FrameLifetime.pointer_from_parts_minted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.pointer_from_parts_minted

/-- info: 'TrustIr.FrameLifetime.WellMintedState.pointer_data_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.pointer_data_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.pointer_metadata_success' depends on axioms: [Classical.choice,
 propext,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.pointer_metadata_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.pointer_from_parts_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.pointer_from_parts_success

/-- info: 'TrustIr.FrameLifetime.set_union_minted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.set_union_minted

/-- info: 'TrustIr.FrameLifetime.set_intersection_minted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.set_intersection_minted

/-- info: 'TrustIr.FrameLifetime.sequence_concat_minted' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.sequence_concat_minted

/-- info: 'TrustIr.FrameLifetime.sequence_add_lanes_minted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.sequence_add_lanes_minted

/-- info: 'TrustIr.FrameLifetime.sequence_not_lanes_minted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.sequence_not_lanes_minted

/-- info: 'TrustIr.FrameLifetime.WellMintedState.sequence_add_success' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.sequence_add_success

/-- info: 'TrustIr.FrameLifetime.WellMintedState.sequence_not_success' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.sequence_not_success

/-- info: 'TrustIr.FrameLifetime.sequence_map_request_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.sequence_map_request_success

/-- info: 'TrustIr.FrameLifetime.HistoryEffects.bind_history' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.HistoryEffects.bind_history

/-- info: 'TrustIr.FrameLifetime.HistoryEffects.KeepsHistory.extends' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.HistoryEffects.KeepsHistory.extends

/-- info: 'TrustIr.FrameLifetime.HistoryEffects.semCast_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.HistoryEffects.semCast_history

/-- info: 'TrustIr.FrameLifetime.HistoryEffects.semBinOp_history' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.HistoryEffects.semBinOp_history

/-- info: 'TrustIr.FrameLifetime.HistoryEffects.contextual_insert_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.HistoryEffects.contextual_insert_history

/-- info: 'TrustIr.FrameLifetime.HistoryEffects.semPtrFromParts_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.HistoryEffects.semPtrFromParts_history

/-- info: 'TrustIr.FrameLifetime.HistoryEffects.lookupLanes_history' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.HistoryEffects.lookupLanes_history

/-- info: 'TrustIr.FrameLifetime.ssa_edit_history' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.ssa_edit_history

/-- info: 'TrustIr.FrameLifetime.instruction_results_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.instruction_results_history

/-- info: 'TrustIr.FrameLifetime.checked_params_history' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.checked_params_history

/-- info: 'TrustIr.FrameLifetime.frame_step_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.frame_step_history

/-- info: 'TrustIr.FrameLifetime.frame_body_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.frame_body_history

/-- info: 'TrustIr.FrameLifetime.frame_body_list_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.frame_body_list_history

/-- info: 'TrustIr.FrameLifetime.frame_layer_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.frame_layer_history

/-- info: 'TrustIr.FrameLifetime.frame_cfg_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.frame_cfg_history

/-- info: 'TrustIr.FrameLifetime.restore_after_frame_cfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.restore_after_frame_cfg

/-- info: 'TrustIr.FrameLifetime.DirectFrameCFG.forFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.DirectFrameCFG.forFunction

/-- info: 'TrustIr.FrameLifetime.DirectFrameProgram.forFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.DirectFrameProgram.forFunction

/-- info: 'TrustIr.FrameLifetime.WellMintedState.call_results_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.WellMintedState.call_results_success

/-- info: 'TrustIr.FrameLifetime.call_results_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.call_results_history

/-- info: 'TrustIr.FrameLifetime.call_frame_success' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.call_frame_success

/-- info: 'TrustIr.FrameLifetime.direct_call_body_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.direct_call_body_success

/-- info: 'TrustIr.FrameLifetime.direct_frame_body_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.direct_frame_body_success

/-- info: 'TrustIr.FrameLifetime.direct_frame_body_list_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.direct_frame_body_list_success

/-- info: 'TrustIr.FrameLifetime.direct_frame_layer_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.direct_frame_layer_success

/-- info: 'TrustIr.FrameLifetime.direct_frame_cfg_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.direct_frame_cfg_success

/-- info: 'TrustIr.FrameLifetime.FrameCFG.direct' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameCFG.direct

/-- info: 'TrustIr.FrameLifetime.check_returns_readonly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.check_returns_readonly

/-- info: 'TrustIr.FrameLifetime.checked_call_frame_success' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.checked_call_frame_success

/-- info: 'TrustIr.FrameLifetime.indirect_return_frame_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.indirect_return_frame_success

/-- info: 'TrustIr.FrameLifetime.closure_call_arguments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.closure_call_arguments

/-- info: 'TrustIr.FrameLifetime.closure_call_arguments_minted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.closure_call_arguments_minted

/-- info: 'TrustIr.FrameLifetime.raw_indirect_arguments_success' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.raw_indirect_arguments_success

/-- info: 'TrustIr.FrameLifetime.indirect_arguments_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.indirect_arguments_success

/-- info: 'TrustIr.FrameLifetime.indirect_call_body_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.indirect_call_body_success

/-- info: 'TrustIr.FrameLifetime.CallFrameCFG.forFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.CallFrameCFG.forFunction

/-- info: 'TrustIr.FrameLifetime.CallFrameProgram.forFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.CallFrameProgram.forFunction

/-- info: 'TrustIr.FrameLifetime.call_frame_body_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.call_frame_body_success

/-- info: 'TrustIr.FrameLifetime.call_frame_body_list_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.call_frame_body_list_success

/-- info: 'TrustIr.FrameLifetime.call_frame_layer_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.call_frame_layer_success

/-- info: 'TrustIr.FrameLifetime.call_frame_cfg_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.call_frame_cfg_success

/-- info: 'TrustIr.FrameLifetime.DirectFrameCFG.calls' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.DirectFrameCFG.calls

/-- info: 'TrustIr.FrameLifetime.terminal_call_request_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.terminal_call_request_success

/-- info: 'TrustIr.FrameLifetime.terminal_direct_transfer_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.terminal_direct_transfer_success

/-- info: 'TrustIr.FrameLifetime.terminal_direct_transfer_cfg_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.terminal_direct_transfer_cfg_success

/-- info: 'TrustIr.FrameLifetime.call_frame_body_with_callees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.call_frame_body_with_callees

/-- info: 'TrustIr.FrameLifetime.call_frame_body_list_with_callees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.call_frame_body_list_with_callees

/-- info: 'TrustIr.FrameLifetime.TailFrameCFG.forFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.TailFrameCFG.forFunction

/-- info: 'TrustIr.FrameLifetime.TailFrameProgram.forFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.TailFrameProgram.forFunction

/-- info: 'TrustIr.FrameLifetime.TailFrameRecursion.callees' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.TailFrameRecursion.callees

/-- info: 'TrustIr.FrameLifetime.tail_frame_layer_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.tail_frame_layer_success

/-- info: 'TrustIr.FrameLifetime.tail_frame_cfg_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.tail_frame_cfg_success

/-- info: 'TrustIr.FrameLifetime.CallFrameCFG.tail' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.CallFrameCFG.tail

/-- info: 'TrustIr.FrameLifetime.CallFrameProgram.tail' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.CallFrameProgram.tail

/-- info: 'TrustIr.FrameLifetime.raw_terminal_request_success' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.raw_terminal_request_success

/-- info: 'TrustIr.FrameLifetime.indirect_terminal_request_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.indirect_terminal_request_success

/-- info: 'TrustIr.FrameLifetime.raw_terminal_transfer_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.raw_terminal_transfer_success

/-- info: 'TrustIr.FrameLifetime.AllTailFrameCFG.forFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.AllTailFrameCFG.forFunction

/-- info: 'TrustIr.FrameLifetime.AllTailFrameProgram.forFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.AllTailFrameProgram.forFunction

/-- info: 'TrustIr.FrameLifetime.AllTailFrameRecursion.callees' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.AllTailFrameRecursion.callees

/-- info: 'TrustIr.FrameLifetime.all_tail_frame_layer_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.all_tail_frame_layer_success

/-- info: 'TrustIr.FrameLifetime.all_tail_frame_cfg_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.all_tail_frame_cfg_success

/-- info: 'TrustIr.FrameLifetime.TailFrameCFG.indirect' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.TailFrameCFG.indirect

/-- info: 'TrustIr.FrameLifetime.TailFrameProgram.indirect' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.TailFrameProgram.indirect

/-- info: 'TrustIr.FrameLifetime.invoke_catch_frame_exit' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.invoke_catch_frame_exit

/-- info: 'TrustIr.FrameLifetime.restore_frame_after_exit' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.restore_frame_after_exit

/-- info: 'TrustIr.FrameLifetime.invoke_frame_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.invoke_frame_success

/-- info: 'TrustIr.FrameLifetime.checked_invoke_frame_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.checked_invoke_frame_success

/-- info: 'TrustIr.FrameLifetime.exception_allocation_frame_success' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.exception_allocation_frame_success

/-- info: 'TrustIr.FrameLifetime.exception_allocation_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.exception_allocation_no_unwind

/-- info: 'TrustIr.FrameLifetime.raise_frame_exit' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.raise_frame_exit

/-- info: 'TrustIr.FrameLifetime.enter_pad_frame_success' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.enter_pad_frame_success

/-- info: 'TrustIr.FrameLifetime.FrameCalleeExit.history' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameCalleeExit.history

/-- info: 'TrustIr.FrameLifetime.invoke_returns_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.invoke_returns_no_unwind

/-- info: 'TrustIr.FrameLifetime.invoke_frame_exit' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.invoke_frame_exit

/-- info: 'TrustIr.FrameLifetime.checked_invoke_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.checked_invoke_frame_exit

/-- info: 'TrustIr.FrameLifetime.resume_unwind_state' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.resume_unwind_state

/-- info: 'TrustIr.FrameLifetime.enter_pad_unwind_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.enter_pad_unwind_state

/-- info: 'TrustIr.FrameLifetime.FrameActionExit.history' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameActionExit.history

/-- info: 'TrustIr.FrameLifetime.FrameActionExit.callee' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameActionExit.callee

/-- info: 'TrustIr.FrameLifetime.FrameActionValid.bind' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameActionValid.bind

/-- info: 'TrustIr.FrameLifetime.frame_action_pure' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.frame_action_pure

/-- info: 'TrustIr.FrameLifetime.frame_action_of_success_no_unwind' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.frame_action_of_success_no_unwind

/-- info: 'TrustIr.FrameLifetime.CallCheckNoUnwind.bind' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.CallCheckNoUnwind.bind

/-- info: 'TrustIr.FrameLifetime.exception_allocation_frame_action' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.exception_allocation_frame_action

/-- info: 'TrustIr.FrameLifetime.raise_frame_action' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.raise_frame_action

/-- info: 'TrustIr.FrameLifetime.enter_pad_frame_action' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.enter_pad_frame_action

/-- info: 'TrustIr.FrameLifetime.open_frame_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.open_frame_no_unwind

/-- info: 'TrustIr.FrameLifetime.bind_slot_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.bind_slot_no_unwind

/-- info: 'TrustIr.FrameLifetime.load_slot_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.load_slot_no_unwind

/-- info: 'TrustIr.FrameLifetime.close_frame_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.close_frame_no_unwind

/-- info: 'TrustIr.FrameLifetime.open_frame_action' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.open_frame_action

/-- info: 'TrustIr.FrameLifetime.bind_slot_action' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.bind_slot_action

/-- info: 'TrustIr.FrameLifetime.load_slot_action' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.load_slot_action

/-- info: 'TrustIr.FrameLifetime.close_frame_action' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.close_frame_action

/-- info: 'TrustIr.FrameLifetime.lookup_arguments_no_unwind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.lookup_arguments_no_unwind

/-- info: 'TrustIr.FrameLifetime.lookup_arguments_action' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.lookup_arguments_action

/-- info: 'TrustIr.FrameLifetime.call_frame_with_eq_invoke_abort' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.call_frame_with_eq_invoke_abort

/-- info: 'TrustIr.FrameLifetime.call_frame_with_error' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.call_frame_with_error

/-- info: 'TrustIr.FrameLifetime.call_frame_with_exit' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.call_frame_with_exit

/-- info: 'TrustIr.FrameLifetime.direct_call_frame_eq_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.direct_call_frame_eq_checked

/-- info: 'TrustIr.FrameLifetime.direct_call_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.direct_call_frame_exit

/-- info: 'TrustIr.FrameLifetime.direct_call_frame_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.direct_call_frame_error

/-- info: 'TrustIr.FrameLifetime.direct_call_frame_action' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.direct_call_frame_action

/-- info: 'TrustIr.FrameLifetime.StaticFunctionErrors.no_unwind' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.StaticFunctionErrors.no_unwind

/-- info: 'TrustIr.FrameLifetime.static_function_errors_empty' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.static_function_errors_empty

/-- info: 'TrustIr.FrameLifetime.StaticFunctionErrors.forFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.StaticFunctionErrors.forFunction

/-- info: 'TrustIr.FrameLifetime.StaticFunctionErrors.scoped' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.StaticFunctionErrors.scoped

/-- info: 'TrustIr.FrameLifetime.prepared_function_errors_static' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.prepared_function_errors_static

/-- info: 'TrustIr.FrameLifetime.decoded_context_errors_static' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decoded_context_errors_static

/-- info: 'TrustIr.FrameLifetime.function_call_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.function_call_no_unwind

/-- info: 'TrustIr.FrameLifetime.function_arguments_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.function_arguments_no_unwind

/-- info: 'TrustIr.FrameLifetime.function_arguments_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.function_arguments_frame_exit

/-- info: 'TrustIr.FrameLifetime.direct_lookup_no_unwind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.direct_lookup_no_unwind

/-- info: 'TrustIr.FrameLifetime.direct_lookup_frame_action' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.direct_lookup_frame_action

/-- info: 'TrustIr.FrameLifetime.FrameActionExit.bind' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameActionExit.bind

/-- info: 'TrustIr.FrameLifetime.ExceptNoUnwind.bind' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.ExceptNoUnwind.bind

/-- info: 'TrustIr.FrameLifetime.ExceptNoUnwind.mapM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.ExceptNoUnwind.mapM

/-- info: 'TrustIr.FrameLifetime.char_value_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.char_value_no_unwind

/-- info: 'TrustIr.FrameLifetime.char_values_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.char_values_no_unwind

/-- info: 'TrustIr.FrameLifetime.result_source_type_no_unwind' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.result_source_type_no_unwind

/-- info: 'TrustIr.FrameLifetime.instruction_types_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.instruction_types_no_unwind

/-- info: 'TrustIr.FrameLifetime.lift_validation_no_unwind' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.lift_validation_no_unwind

/-- info: 'TrustIr.FrameLifetime.result_checks_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.result_checks_no_unwind

/-- info: 'TrustIr.FrameLifetime.result_dests_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.result_dests_no_unwind

/-- info: 'TrustIr.FrameLifetime.instruction_dests_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.instruction_dests_no_unwind

/-- info: 'TrustIr.FrameLifetime.call_results_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.call_results_no_unwind

/-- info: 'TrustIr.FrameLifetime.instruction_results_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.instruction_results_no_unwind

/-- info: 'TrustIr.FrameLifetime.result_checks_frame_action' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.result_checks_frame_action

/-- info: 'TrustIr.FrameLifetime.result_dests_frame_exit' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.result_dests_frame_exit

/-- info: 'TrustIr.FrameLifetime.call_results_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.call_results_frame_exit

/-- info: 'TrustIr.FrameLifetime.instruction_results_frame_action' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.instruction_results_frame_action

/-- info: 'TrustIr.FrameLifetime.block_params_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.block_params_no_unwind

/-- info: 'TrustIr.FrameLifetime.checked_params_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.checked_params_no_unwind

/-- info: 'TrustIr.FrameLifetime.checked_params_frame_exit' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.checked_params_frame_exit

/-- info: 'TrustIr.FrameLifetime.direct_header_readonly' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.direct_header_readonly

/-- info: 'TrustIr.FrameLifetime.direct_header_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.direct_header_no_unwind

/-- info: 'TrustIr.FrameLifetime.direct_header_frame_exit' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.direct_header_frame_exit

/-- info: 'TrustIr.FrameLifetime.direct_lookup_arguments_exit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.direct_lookup_arguments_exit

/-- info: 'TrustIr.FrameLifetime.direct_body_call_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.direct_body_call_exit

/-- info: 'TrustIr.FrameLifetime.FrameControl.action_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameControl.action_no_unwind

/-- info: 'TrustIr.FrameLifetime.FrameControl.action_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameControl.action_frame_exit

/-- info: 'TrustIr.FrameLifetime.FrameControl.term_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameControl.term_no_unwind

/-- info: 'TrustIr.FrameLifetime.FrameControl.term_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameControl.term_frame_exit

/-- info: 'TrustIr.FrameLifetime.ordinary_transfer_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.ordinary_transfer_frame_exit

/-- info: 'TrustIr.FrameLifetime.FrameControl.dispatch_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameControl.dispatch_frame_exit

/-- info: 'TrustIr.FrameLifetime.target_lookup_arguments_exit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.target_lookup_arguments_exit

/-- info: 'TrustIr.FrameLifetime.invoke_normal_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.invoke_normal_frame_exit

/-- info: 'TrustIr.FrameLifetime.invoke_unwind_frame_exit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.invoke_unwind_frame_exit

/-- info: 'TrustIr.FrameLifetime.direct_invoke_transfer_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.direct_invoke_transfer_exit

/-- info: 'TrustIr.FrameLifetime.invoke_request_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.invoke_request_frame_exit

/-- info: 'TrustIr.FrameLifetime.direct_invoke_dispatch_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.direct_invoke_dispatch_exit

/-- info: 'TrustIr.FrameLifetime.indirect_invoke_transfer_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.indirect_invoke_transfer_exit

/-- info: 'TrustIr.FrameLifetime.indirect_invoke_request_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.indirect_invoke_request_success

/-- info: 'TrustIr.FrameLifetime.indirect_invoke_request_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.indirect_invoke_request_no_unwind

/-- info: 'TrustIr.FrameLifetime.indirect_invoke_request_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.indirect_invoke_request_exit

/-- info: 'TrustIr.FrameLifetime.indirect_invoke_dispatch_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.indirect_invoke_dispatch_exit

/-- info: 'TrustIr.FrameLifetime.ExceptNoUnwind.forIn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.ExceptNoUnwind.forIn

/-- info: 'TrustIr.FrameLifetime.ExceptNoUnwind.forM' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.ExceptNoUnwind.forM

/-- info: 'TrustIr.FrameLifetime.tree_range_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.tree_range_no_unwind

/-- info: 'TrustIr.FrameLifetime.tree_stored_no_unwind' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.tree_stored_no_unwind

/-- info: 'TrustIr.FrameLifetime.closure_value_at_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.closure_value_at_no_unwind

/-- info: 'TrustIr.FrameLifetime.closure_value_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.closure_value_no_unwind

/-- info: 'TrustIr.FrameLifetime.closure_contract_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.closure_contract_no_unwind

/-- info: 'TrustIr.FrameLifetime.make_closure_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.make_closure_no_unwind

/-- info: 'TrustIr.FrameLifetime.closure_call_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.closure_call_no_unwind

/-- info: 'TrustIr.FrameLifetime.CallCheckNoUnwind.forIn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.CallCheckNoUnwind.forIn

/-- info: 'TrustIr.FrameLifetime.checked_returns_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.checked_returns_no_unwind

/-- info: 'TrustIr.FrameLifetime.checked_call_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.checked_call_frame_exit

/-- info: 'TrustIr.FrameLifetime.lookup_value_frame_action' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.lookup_value_frame_action

/-- info: 'TrustIr.FrameLifetime.indirect_arguments_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.indirect_arguments_no_unwind

/-- info: 'TrustIr.FrameLifetime.indirect_arguments_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.indirect_arguments_frame_exit

/-- info: 'TrustIr.FrameLifetime.indirect_body_call_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.indirect_body_call_exit

/-- info: 'TrustIr.FrameLifetime.checked_closure_captures_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.checked_closure_captures_no_unwind

/-- info: 'TrustIr.FrameLifetime.closure_extract_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.closure_extract_no_unwind

/-- info: 'TrustIr.FrameLifetime.closure_insert_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.closure_insert_no_unwind

/-- info: 'TrustIr.FrameLifetime.unary_value_no_unwind' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.unary_value_no_unwind

/-- info: 'TrustIr.FrameLifetime.binary_values_no_unwind' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.binary_values_no_unwind

/-- info: 'TrustIr.FrameLifetime.integer_compare_values_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.integer_compare_values_no_unwind

/-- info: 'TrustIr.FrameLifetime.float_compare_values_no_unwind' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.float_compare_values_no_unwind

/-- info: 'TrustIr.FrameLifetime.unary_action_no_unwind' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.unary_action_no_unwind

/-- info: 'TrustIr.FrameLifetime.binary_action_no_unwind' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.binary_action_no_unwind

/-- info: 'TrustIr.FrameLifetime.overflow_action_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.overflow_action_no_unwind

/-- info: 'TrustIr.FrameLifetime.integer_compare_action_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.integer_compare_action_no_unwind

/-- info: 'TrustIr.FrameLifetime.float_compare_action_no_unwind' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.float_compare_action_no_unwind

/-- info: 'TrustIr.FrameLifetime.semCast_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.semCast_no_unwind

/-- info: 'TrustIr.FrameLifetime.frame_step_exit_of_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.frame_step_exit_of_no_unwind

/-- info: 'TrustIr.FrameLifetime.frame_body_exit_of_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.frame_body_exit_of_no_unwind

/-- info: 'TrustIr.FrameLifetime.FrameActionValid.forIn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameActionValid.forIn

/-- info: 'TrustIr.FrameLifetime.frame_body_list_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.frame_body_list_exit

/-- info: 'TrustIr.FrameLifetime.unary_body_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.unary_body_exit

/-- info: 'TrustIr.FrameLifetime.binary_body_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.binary_body_exit

/-- info: 'TrustIr.FrameLifetime.overflow_body_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.overflow_body_exit

/-- info: 'TrustIr.FrameLifetime.integer_compare_body_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.integer_compare_body_exit

/-- info: 'TrustIr.FrameLifetime.float_compare_body_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.float_compare_body_exit

/-- info: 'TrustIr.FrameLifetime.cast_body_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.cast_body_exit

/-- info: 'TrustIr.FrameLifetime.copy_body_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.copy_body_exit

/-- info: 'TrustIr.FrameLifetime.undef_body_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.undef_body_exit

/-- info: 'TrustIr.FrameLifetime.null_body_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.null_body_exit

/-- info: 'TrustIr.FrameLifetime.open_body_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.open_body_exit

/-- info: 'TrustIr.FrameLifetime.bind_body_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.bind_body_exit

/-- info: 'TrustIr.FrameLifetime.load_body_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.load_body_exit

/-- info: 'TrustIr.FrameLifetime.close_body_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.close_body_exit

/-- info: 'TrustIr.FrameLifetime.aggregate_lane_no_unwind' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.aggregate_lane_no_unwind

/-- info: 'TrustIr.FrameLifetime.aggregate_value_no_unwind' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.aggregate_value_no_unwind

/-- info: 'TrustIr.FrameLifetime.array_value_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.array_value_no_unwind

/-- info: 'TrustIr.FrameLifetime.declared_field_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.declared_field_no_unwind

/-- info: 'TrustIr.FrameLifetime.select_values_no_unwind' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.select_values_no_unwind

/-- info: 'TrustIr.FrameLifetime.sequence_add_values_no_unwind' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.sequence_add_values_no_unwind

/-- info: 'TrustIr.FrameLifetime.sequence_not_values_no_unwind' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.sequence_not_values_no_unwind

/-- info: 'TrustIr.FrameLifetime.context_element_index_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_element_index_no_unwind

/-- info: 'TrustIr.FrameLifetime.extract_element_action_no_unwind' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.extract_element_action_no_unwind

/-- info: 'TrustIr.FrameLifetime.insert_element_action_no_unwind' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.insert_element_action_no_unwind

/-- info: 'TrustIr.FrameLifetime.pointer_data_action_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.pointer_data_action_no_unwind

/-- info: 'TrustIr.FrameLifetime.pointer_metadata_action_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.pointer_metadata_action_no_unwind

/-- info: 'TrustIr.FrameLifetime.pointer_parts_action_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.pointer_parts_action_no_unwind

/-- info: 'TrustIr.FrameLifetime.contextual_extract_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.contextual_extract_no_unwind

/-- info: 'TrustIr.FrameLifetime.contextual_insert_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.contextual_insert_no_unwind

/-- info: 'TrustIr.FrameLifetime.contextual_splat_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.contextual_splat_no_unwind

/-- info: 'TrustIr.FrameLifetime.contextual_closure_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.contextual_closure_no_unwind

/-- info: 'TrustIr.FrameLifetime.contextual_aggregate_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.contextual_aggregate_no_unwind

/-- info: 'TrustIr.FrameLifetime.contextual_select_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.contextual_select_no_unwind

/-- info: 'TrustIr.FrameLifetime.FrameInstruction.step_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameInstruction.step_no_unwind

/-- info: 'TrustIr.FrameLifetime.FrameInstruction.step_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameInstruction.step_frame_exit

/-- info: 'TrustIr.FrameLifetime.FrameInstruction.body_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameInstruction.body_frame_exit

/-- info: 'TrustIr.FrameLifetime.frame_ordinary_body_list_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.frame_ordinary_body_list_exit

/-- info: 'TrustIr.FrameLifetime.DirectFrameInstruction.body_frame_exit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.DirectFrameInstruction.body_frame_exit

/-- info: 'TrustIr.FrameLifetime.CallFrameInstruction.body_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.CallFrameInstruction.body_frame_exit

/-- info: 'TrustIr.FrameLifetime.frame_call_body_list_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.frame_call_body_list_exit

/-- info: 'TrustIr.FrameLifetime.call_frame_layer_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.call_frame_layer_exit

/-- info: 'TrustIr.FrameLifetime.call_frame_cfg_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.call_frame_cfg_exit

/-- info: 'TrustIr.FrameLifetime.ordinary_frame_layer_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.ordinary_frame_layer_exit

/-- info: 'TrustIr.FrameLifetime.ordinary_frame_cfg_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.ordinary_frame_cfg_exit

/-- info: 'TrustIr.FrameLifetime.assert_operand_no_unwind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.assert_operand_no_unwind

/-- info: 'TrustIr.FrameLifetime.assert_message_no_unwind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.assert_message_no_unwind

/-- info: 'TrustIr.FrameLifetime.panic_location_no_unwind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.panic_location_no_unwind

/-- info: 'TrustIr.FrameLifetime.assert_failure_no_unwind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.assert_failure_no_unwind

/-- info: 'TrustIr.FrameLifetime.assert_step_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.assert_step_no_unwind

/-- info: 'TrustIr.FrameLifetime.assert_step_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.assert_step_frame_exit

/-- info: 'TrustIr.FrameLifetime.raise_if_unwind_frame_exit' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.raise_if_unwind_frame_exit

/-- info: 'TrustIr.FrameLifetime.assert_body_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.assert_body_frame_exit

/-- info: 'TrustIr.FrameLifetime.landing_pad_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.landing_pad_frame_exit

/-- info: 'TrustIr.FrameLifetime.landing_pad_body_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.landing_pad_body_frame_exit

/-- info: 'TrustIr.FrameLifetime.resume_term_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.resume_term_frame_exit

/-- info: 'TrustIr.FrameLifetime.FrameActionExit.weaken' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameActionExit.weaken

/-- info: 'TrustIr.FrameLifetime.assert_invoke_bare_frame_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.assert_invoke_bare_frame_exit

/-- info: 'TrustIr.FrameLifetime.assert_invoke_term_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.assert_invoke_term_frame_exit

/-- info: 'TrustIr.FrameLifetime.ordinary_dispatch_of_term_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.ordinary_dispatch_of_term_exit

/-- info: 'TrustIr.FrameLifetime.resume_dispatch_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.resume_dispatch_frame_exit

/-- info: 'TrustIr.FrameLifetime.UnwindFrameCFG.forFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.UnwindFrameCFG.forFunction

/-- info: 'TrustIr.FrameLifetime.UnwindFrameProgram.forFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.UnwindFrameProgram.forFunction

/-- info: 'TrustIr.FrameLifetime.CallFrameCFG.toUnwindCFG' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.CallFrameCFG.toUnwindCFG

/-- info: 'TrustIr.FrameLifetime.UnwindFrameInstruction.body_frame_exit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.UnwindFrameInstruction.body_frame_exit

/-- info: 'TrustIr.FrameLifetime.unwind_frame_body_list_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.unwind_frame_body_list_exit

/-- info: 'TrustIr.FrameLifetime.UnwindFrameControl.dispatch_frame_exit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.UnwindFrameControl.dispatch_frame_exit

/-- info: 'TrustIr.FrameLifetime.unwind_frame_layer_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.unwind_frame_layer_exit

/-- info: 'TrustIr.FrameLifetime.unwind_frame_cfg_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.unwind_frame_cfg_exit

/-- info: 'TrustIr.FrameLifetime.exit_unwinding_frame_exit' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.exit_unwinding_frame_exit

/-- info: 'TrustIr.FrameLifetime.unwind_frame_entry_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.unwind_frame_entry_exit

/-- info: 'TrustIr.FrameLifetime.terminal_direct_transfer_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.terminal_direct_transfer_exit

/-- info: 'TrustIr.FrameLifetime.raw_terminal_transfer_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.raw_terminal_transfer_exit

/-- info: 'TrustIr.FrameLifetime.terminal_direct_dispatch_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.terminal_direct_dispatch_exit

/-- info: 'TrustIr.FrameLifetime.indirect_terminal_request_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.indirect_terminal_request_no_unwind

/-- info: 'TrustIr.FrameLifetime.indirect_terminal_request_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.indirect_terminal_request_exit

/-- info: 'TrustIr.FrameLifetime.terminal_indirect_dispatch_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.terminal_indirect_dispatch_exit

/-- info: 'TrustIr.FrameLifetime.TerminalFrameCFG.forFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.TerminalFrameCFG.forFunction

/-- info: 'TrustIr.FrameLifetime.TerminalFrameProgram.forFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.TerminalFrameProgram.forFunction

/-- info: 'TrustIr.FrameLifetime.UnwindFrameCFG.toTerminalCFG' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.UnwindFrameCFG.toTerminalCFG

/-- info: 'TrustIr.FrameLifetime.AllTailFrameCFG.toTerminalCFG' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.AllTailFrameCFG.toTerminalCFG

/-- info: 'TrustIr.FrameLifetime.UnwindFrameProgram.toTerminalProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.UnwindFrameProgram.toTerminalProgram

/-- info: 'TrustIr.FrameLifetime.AllTailFrameProgram.toTerminalProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.AllTailFrameProgram.toTerminalProgram

/-- info: 'TrustIr.FrameLifetime.TerminalFrameControl.dispatch_frame_exit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.TerminalFrameControl.dispatch_frame_exit

/-- info: 'TrustIr.FrameLifetime.terminal_frame_layer_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.terminal_frame_layer_exit

/-- info: 'TrustIr.FrameLifetime.terminal_frame_cfg_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.terminal_frame_cfg_exit

/-- info: 'TrustIr.FrameLifetime.terminal_frame_entry_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.terminal_frame_entry_exit

/-- info: 'TrustIr.FrameLifetime.DecodeFrameExit.bind' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.DecodeFrameExit.bind

/-- info: 'TrustIr.FrameLifetime.DecodeFrameExit.of_no_unwind' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.DecodeFrameExit.of_no_unwind

/-- info: 'TrustIr.FrameLifetime.DecodeFrameExit.no_unwind' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.DecodeFrameExit.no_unwind

/-- info: 'TrustIr.FrameLifetime.decode_value_minted' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decode_value_minted

/-- info: 'TrustIr.FrameLifetime.decode_value_model_minted' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decode_value_model_minted

/-- info: 'TrustIr.FrameLifetime.decode_float_no_unwind' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decode_float_no_unwind

/-- info: 'TrustIr.FrameLifetime.decode_char_frame_exit' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decode_char_frame_exit

/-- info: 'TrustIr.FrameLifetime.decode_vector_lane_frame_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decode_vector_lane_frame_exit

/-- info: 'TrustIr.FrameLifetime.decode_vector_lanes_frame_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decode_vector_lanes_frame_exit

/-- info: 'TrustIr.FrameLifetime.decode_scalar_vector_frame_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decode_scalar_vector_frame_exit

/-- info: 'TrustIr.FrameLifetime.decode_image_frame_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decode_image_frame_exit

/-- info: 'TrustIr.FrameLifetime.decode_image_model_frame_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decode_image_model_frame_exit

/-- info: 'TrustIr.FrameLifetime.resolve_decoded_minted' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.resolve_decoded_minted

/-- info: 'TrustIr.FrameLifetime.decode_value_at_frame_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decode_value_at_frame_exit

/-- info: 'TrustIr.FrameLifetime.decode_typed_model_frame_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decode_typed_model_frame_exit

/-- info: 'TrustIr.FrameLifetime.decode_memory_frame_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decode_memory_frame_exit

/-- info: 'TrustIr.FrameLifetime.function_target_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.function_target_no_unwind

/-- info: 'TrustIr.FrameLifetime.decode_functions_frame_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decode_functions_frame_exit

/-- info: 'TrustIr.FrameLifetime.reject_partial_frame_action' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.reject_partial_frame_action

/-- info: 'TrustIr.FrameLifetime.expect_pointer_frame_action' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.expect_pointer_frame_action

/-- info: 'TrustIr.FrameLifetime.access_align_frame_action' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.access_align_frame_action

/-- info: 'TrustIr.FrameLifetime.checked_access_frame_action' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.checked_access_frame_action

/-- info: 'TrustIr.FrameLifetime.load_value_using_frame_exit' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.load_value_using_frame_exit

/-- info: 'TrustIr.FrameLifetime.scalar_load_value_frame_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.scalar_load_value_frame_exit

/-- info: 'TrustIr.FrameLifetime.fresh_minted_frame_exit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.fresh_minted_frame_exit

/-- info: 'TrustIr.FrameLifetime.scalar_load_step_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.scalar_load_step_frame_exit

/-- info: 'TrustIr.FrameLifetime.canonical_load_step_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.canonical_load_step_frame_exit

/-- info: 'TrustIr.FrameLifetime.scalar_load_body_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.scalar_load_body_frame_exit

/-- info: 'TrustIr.FrameLifetime.canonical_context_load_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.canonical_context_load_frame_exit

/-- info: 'TrustIr.ByteImage.BlockResult.bind' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ByteImage.BlockResult.bind

/-- info: 'TrustIr.ByteImage.BlockTreeValid.uniform' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.BlockTreeValid.uniform

/-- info: 'TrustIr.ByteImage.BlockTreeValid.empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.BlockTreeValid.empty

/-- info: 'TrustIr.ByteImage.BlockTreeValid.split' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.BlockTreeValid.split

/-- info: 'TrustIr.ByteImage.BlockTreeValid.periodic' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.BlockTreeValid.periodic

/-- info: 'TrustIr.ByteImage.mapBlocksSpec_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.mapBlocksSpec_valid

/-- info: 'TrustIr.ByteImage.mapBlocks_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.mapBlocks_valid

/-- info: 'TrustIr.FrameLifetime.block_result_frame_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.block_result_frame_iff

/-- info: 'TrustIr.FrameLifetime.map_blocks_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.map_blocks_frame_exit

/-- info: 'TrustIr.FrameLifetime.mapped_array_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.mapped_array_frame_exit

/-- info: 'TrustIr.ByteImage.BlockResult.error_of_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ByteImage.BlockResult.error_of_eq

/-- info: 'TrustIr.ByteImage.checkBlocksSpec_errors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.checkBlocksSpec_errors

/-- info: 'TrustIr.ByteImage.checkBlocks_errors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.checkBlocks_errors

/-- info: 'TrustIr.AggregateMemory.covered_errors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.covered_errors

/-- info: 'TrustIr.AggregateMemory.covered_fields_errors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.covered_fields_errors

/-- info: 'TrustIr.AggregateMemory.covered_variant_errors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.covered_variant_errors

/-- info: 'TrustIr.AggregateMemory.decode_valid' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decode_valid

/-- info: 'TrustIr.AggregateMemory.decodeUnwritten_valid' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decodeUnwritten_valid

/-- info: 'TrustIr.FrameLifetime.aggregate_covered_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.aggregate_covered_no_unwind

/-- info: 'TrustIr.FrameLifetime.aggregate_decode_frame_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.aggregate_decode_frame_exit

/-- info: 'TrustIr.FrameLifetime.aggregate_unwritten_decode_frame_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.aggregate_unwritten_decode_frame_exit

/-- info: 'TrustIr.FrameLifetime.prepared_memory_error_policy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.prepared_memory_error_policy

/-- info: 'TrustIr.FrameLifetime.aggregate_load_value_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.aggregate_load_value_frame_exit

/-- info: 'TrustIr.FrameLifetime.context_load_value_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_load_value_frame_exit

/-- info: 'TrustIr.FrameLifetime.context_load_step_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_load_step_frame_exit

/-- info: 'TrustIr.FrameLifetime.context_load_body_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_load_body_frame_exit

/-- info: 'TrustIr.FrameLifetime.prepared_memory_context_errors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.prepared_memory_context_errors

/-- info: 'TrustIr.AggregateMemory.encode_errors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_errors

/-- info: 'TrustIr.FrameLifetime.encode_functions_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.encode_functions_no_unwind

/-- info: 'TrustIr.FrameLifetime.aggregate_encode_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.aggregate_encode_no_unwind

/-- info: 'TrustIr.FrameLifetime.aggregate_store_value_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.aggregate_store_value_frame_exit

/-- info: 'TrustIr.FrameLifetime.scalar_store_value_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.scalar_store_value_frame_exit

/-- info: 'TrustIr.FrameLifetime.context_store_value_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_store_value_frame_exit

/-- info: 'TrustIr.FrameLifetime.context_store_step_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_store_step_frame_exit

/-- info: 'TrustIr.FrameLifetime.context_store_body_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_store_body_frame_exit

/-- info: 'TrustIr.AggregateMemory.equal_errors' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.equal_errors

/-- info: 'TrustIr.FrameLifetime.scalar_atomic_load_frame_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.scalar_atomic_load_frame_exit

/-- info: 'TrustIr.FrameLifetime.scalar_atomic_store_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.scalar_atomic_store_frame_exit

/-- info: 'TrustIr.FrameLifetime.scalar_atomic_rmw_frame_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.scalar_atomic_rmw_frame_exit

/-- info: 'TrustIr.FrameLifetime.scalar_exchange_frame_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.scalar_exchange_frame_exit

/-- info: 'TrustIr.FrameLifetime.aggregate_equal_no_unwind' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.aggregate_equal_no_unwind

/-- info: 'TrustIr.FrameLifetime.aggregate_rmw_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.aggregate_rmw_frame_exit

/-- info: 'TrustIr.FrameLifetime.aggregate_exchange_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.aggregate_exchange_frame_exit

/-- info: 'TrustIr.FrameLifetime.atomic_load_step_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.atomic_load_step_frame_exit

/-- info: 'TrustIr.FrameLifetime.atomic_store_step_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.atomic_store_step_frame_exit

/-- info: 'TrustIr.FrameLifetime.atomic_rmw_step_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.atomic_rmw_step_frame_exit

/-- info: 'TrustIr.FrameLifetime.cmpxchg_step_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.cmpxchg_step_frame_exit

/-- info: 'TrustIr.FrameLifetime.atomic_step_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.atomic_step_frame_exit

/-- info: 'TrustIr.FrameLifetime.atomic_body_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.atomic_body_frame_exit

/-- info: 'TrustIr.FrameLifetime.word_operand_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.word_operand_no_unwind

/-- info: 'TrustIr.FrameLifetime.word_mul_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.word_mul_no_unwind

/-- info: 'TrustIr.FrameLifetime.word_add_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.word_add_no_unwind

/-- info: 'TrustIr.FrameLifetime.memory_alignment_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.memory_alignment_no_unwind

/-- info: 'TrustIr.FrameLifetime.word_allocation_no_unwind' depends on axioms: [Quot.sound, propext, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.word_allocation_no_unwind

/-- info: 'TrustIr.FrameLifetime.carrier_integer_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.carrier_integer_no_unwind

/-- info: 'TrustIr.FrameLifetime.context_memory_layout_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_memory_layout_no_unwind

/-- info: 'TrustIr.FrameLifetime.allocate_using_frame_exit' depends on axioms: [Quot.sound, propext, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.allocate_using_frame_exit

/-- info: 'TrustIr.FrameLifetime.dealloc_frame_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.dealloc_frame_exit

/-- info: 'TrustIr.FrameLifetime.allocation_step_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.allocation_step_frame_exit

/-- info: 'TrustIr.FrameLifetime.allocation_body_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.allocation_body_frame_exit

/-- info: 'TrustIr.FrameLifetime.gep_offset_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.gep_offset_no_unwind

/-- info: 'TrustIr.FrameLifetime.gep_address_frame_exit' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.gep_address_frame_exit

/-- info: 'TrustIr.FrameLifetime.gep_values_frame_exit' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.gep_values_frame_exit

/-- info: 'TrustIr.FrameLifetime.gep_step_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.gep_step_frame_exit

/-- info: 'TrustIr.FrameLifetime.gep_body_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.gep_body_frame_exit

/-- info: 'TrustIr.FrameLifetime.frame_get_bind_exit' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.frame_get_bind_exit

/-- info: 'TrustIr.FrameLifetime.frame_carry_value_exit' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.frame_carry_value_exit

/-- info: 'TrustIr.FrameLifetime.bulk_count_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.bulk_count_frame_exit

/-- info: 'TrustIr.FrameLifetime.bulk_pointer_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.bulk_pointer_frame_exit

/-- info: 'TrustIr.FrameLifetime.memcopy_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.memcopy_frame_exit

/-- info: 'TrustIr.FrameLifetime.memset_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.memset_frame_exit

/-- info: 'TrustIr.FrameLifetime.bulk_step_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.bulk_step_frame_exit

/-- info: 'TrustIr.FrameLifetime.bulk_body_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.bulk_body_frame_exit

/-- info: 'TrustIr.FrameLifetime.borrow_operand_frame_exit' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.borrow_operand_frame_exit

/-- info: 'TrustIr.FrameLifetime.permission_get_frame_exit' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.permission_get_frame_exit

/-- info: 'TrustIr.FrameLifetime.permission_set_frame_exit' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.permission_set_frame_exit

/-- info: 'TrustIr.FrameLifetime.borrow_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.borrow_frame_exit

/-- info: 'TrustIr.FrameLifetime.borrow_mut_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.borrow_mut_frame_exit

/-- info: 'TrustIr.FrameLifetime.end_borrow_frame_exit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.end_borrow_frame_exit

/-- info: 'TrustIr.FrameLifetime.arc_pointer_frame_exit' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.arc_pointer_frame_exit

/-- info: 'TrustIr.FrameLifetime.arc_permission_frame_exit' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.arc_permission_frame_exit

/-- info: 'TrustIr.FrameLifetime.arc_object_base_frame_exit' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.arc_object_base_frame_exit

/-- info: 'TrustIr.FrameLifetime.arc_dealloc_frame_exit' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.arc_dealloc_frame_exit

/-- info: 'TrustIr.FrameLifetime.retain_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.retain_frame_exit

/-- info: 'TrustIr.FrameLifetime.release_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.release_frame_exit

/-- info: 'TrustIr.FrameLifetime.is_unique_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.is_unique_frame_exit

/-- info: 'TrustIr.FrameLifetime.ownership_step_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.ownership_step_frame_exit

/-- info: 'TrustIr.FrameLifetime.ownership_body_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.ownership_body_frame_exit

/-- info: 'TrustIr.FrameLifetime.MemoryContextErrors.forFunction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.MemoryContextErrors.forFunction

/-- info: 'TrustIr.FrameLifetime.MemoryFrameInstruction.body_frame_exit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.MemoryFrameInstruction.body_frame_exit

/-- info: 'TrustIr.FrameLifetime.memory_frame_body_list_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.memory_frame_body_list_exit

/-- info: 'TrustIr.FrameLifetime.MemoryFrameCFG.forFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.MemoryFrameCFG.forFunction

/-- info: 'TrustIr.FrameLifetime.MemoryFrameProgram.forFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.MemoryFrameProgram.forFunction

/-- info: 'TrustIr.FrameLifetime.TerminalFrameCFG.toMemoryCFG' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.TerminalFrameCFG.toMemoryCFG

/-- info: 'TrustIr.FrameLifetime.TerminalFrameProgram.toMemoryProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.TerminalFrameProgram.toMemoryProgram

/-- info: 'TrustIr.FrameLifetime.memory_frame_layer_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.memory_frame_layer_exit

/-- info: 'TrustIr.FrameLifetime.memory_frame_cfg_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.memory_frame_cfg_exit

/-- info: 'TrustIr.FrameLifetime.memory_frame_entry_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.memory_frame_entry_exit

/-- info: 'TrustIr.FrameLifetime.prepared_memory_frame_entry_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.prepared_memory_frame_entry_exit

/-- info: 'TrustIr.FrameLifetime.HeaderContextErrors.forFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.HeaderContextErrors.forFunction

/-- info: 'TrustIr.FrameLifetime.HeaderContextErrors.no_unwind' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.HeaderContextErrors.no_unwind

/-- info: 'TrustIr.FrameLifetime.header_context_errors_empty' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.header_context_errors_empty

/-- info: 'TrustIr.FrameLifetime.decoded_header_fold_errors' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decoded_header_fold_errors

/-- info: 'TrustIr.FrameLifetime.decoded_context_header_errors' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decoded_context_header_errors

/-- info: 'TrustIr.FrameLifetime.decoded_context_memory_errors' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decoded_context_memory_errors

/-- info: 'TrustIr.FrameLifetime.seqmap_cell_world_exit' depends on axioms: [Quot.sound, propext, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.seqmap_cell_world_exit

/-- info: 'TrustIr.FrameLifetime.seqmap_element_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.seqmap_element_frame_exit

/-- info: 'TrustIr.FrameLifetime.seqmap_element_check_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.seqmap_element_check_no_unwind

/-- info: 'TrustIr.FrameLifetime.seqmap_invoke_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.seqmap_invoke_frame_exit

/-- info: 'TrustIr.FrameLifetime.seqmap_apply_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.seqmap_apply_frame_exit

/-- info: 'TrustIr.FrameLifetime.seqmap_elements_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.seqmap_elements_frame_exit

/-- info: 'TrustIr.FrameLifetime.seqmap_run_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.seqmap_run_frame_exit

/-- info: 'TrustIr.FrameLifetime.seqmap_returns_readonly' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.seqmap_returns_readonly

/-- info: 'TrustIr.FrameLifetime.seqmap_returns_no_unwind' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.seqmap_returns_no_unwind

/-- info: 'TrustIr.FrameLifetime.seqmap_step_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.seqmap_step_frame_exit

/-- info: 'TrustIr.FrameLifetime.seqmap_body_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.seqmap_body_frame_exit

/-- info: 'TrustIr.FrameLifetime.SequenceFrameInstruction.body_frame_exit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.SequenceFrameInstruction.body_frame_exit

/-- info: 'TrustIr.FrameLifetime.sequence_frame_body_list_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.sequence_frame_body_list_exit

/-- info: 'TrustIr.FrameLifetime.SequenceFrameCFG.forFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.SequenceFrameCFG.forFunction

/-- info: 'TrustIr.FrameLifetime.SequenceFrameProgram.forFunction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.SequenceFrameProgram.forFunction

/-- info: 'TrustIr.FrameLifetime.MemoryFrameCFG.toSequenceCFG' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.MemoryFrameCFG.toSequenceCFG

/-- info: 'TrustIr.FrameLifetime.MemoryFrameProgram.toSequenceProgram' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.MemoryFrameProgram.toSequenceProgram

/-- info: 'TrustIr.FrameLifetime.sequence_frame_layer_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.sequence_frame_layer_exit

/-- info: 'TrustIr.FrameLifetime.sequence_frame_cfg_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.sequence_frame_cfg_exit

/-- info: 'TrustIr.FrameLifetime.sequence_frame_entry_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.sequence_frame_entry_exit

/-- info: 'TrustIr.FrameLifetime.decoded_sequence_frame_entry_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decoded_sequence_frame_entry_exit

/-- info: 'TrustIr.constValueAtWithDefsIn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.constValueAtWithDefsIn_eq

/-- info: 'TrustIr.constUninitFieldsAtWithDefsIn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.constUninitFieldsAtWithDefsIn_eq

/-- info: 'TrustIr.constFieldsAtWithDefsIn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.constFieldsAtWithDefsIn_eq

/-- info: 'TrustIr.constLanesAtWithDefsIn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.constLanesAtWithDefsIn_eq

/-- info: 'TrustIr.constRecordFieldsAtWithDefsIn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.constRecordFieldsAtWithDefsIn_eq

/-- info: 'TrustIr.FrameLifetime.checked_constant_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.checked_constant_no_unwind

/-- info: 'TrustIr.FrameLifetime.checked_fields_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.checked_fields_no_unwind

/-- info: 'TrustIr.FrameLifetime.checked_lanes_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.checked_lanes_no_unwind

/-- info: 'TrustIr.FrameLifetime.context_constant_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_constant_no_unwind

/-- info: 'TrustIr.FrameLifetime.context_uninit_fields_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_uninit_fields_no_unwind

/-- info: 'TrustIr.FrameLifetime.context_fields_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_fields_no_unwind

/-- info: 'TrustIr.FrameLifetime.context_lanes_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_lanes_no_unwind

/-- info: 'TrustIr.FrameLifetime.context_record_fields_no_unwind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_record_fields_no_unwind

/-- info: 'TrustIr.FrameLifetime.frame_readonly_bind_exit' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.frame_readonly_bind_exit

/-- info: 'TrustIr.FrameLifetime.global_using_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.global_using_frame_exit

/-- info: 'TrustIr.FrameLifetime.context_global_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_global_frame_exit

/-- info: 'TrustIr.FrameLifetime.context_global_step_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_global_step_frame_exit

/-- info: 'TrustIr.FrameLifetime.context_global_body_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_global_body_frame_exit

/-- info: 'TrustIr.FrameLifetime.checked_constant_minted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.checked_constant_minted

/-- info: 'TrustIr.FrameLifetime.checked_fields_minted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.checked_fields_minted

/-- info: 'TrustIr.FrameLifetime.checked_lanes_minted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.checked_lanes_minted

/-- info: 'TrustIr.FrameLifetime.context_constant_minted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_constant_minted

/-- info: 'TrustIr.FrameLifetime.context_uninit_fields_minted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_uninit_fields_minted

/-- info: 'TrustIr.FrameLifetime.context_fields_minted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_fields_minted

/-- info: 'TrustIr.FrameLifetime.context_lanes_minted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_lanes_minted

/-- info: 'TrustIr.FrameLifetime.context_record_fields_minted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_record_fields_minted

/-- info: 'TrustIr.FrameLifetime.checked_constant_decode_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.checked_constant_decode_exit

/-- info: 'TrustIr.FrameLifetime.context_constant_decode_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_constant_decode_exit

/-- info: 'TrustIr.FrameLifetime.checked_constant_step_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.checked_constant_step_exit

/-- info: 'TrustIr.FrameLifetime.context_constant_step_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_constant_step_exit

/-- info: 'TrustIr.FrameLifetime.context_constant_body_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.context_constant_body_exit

/-- info: 'TrustIr.FrameLifetime.scalar_layout_no_unwind' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.scalar_layout_no_unwind

/-- info: 'TrustIr.FrameLifetime.coro_suspend_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.coro_suspend_frame_exit

/-- info: 'TrustIr.FrameLifetime.coro_suspend_term_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.coro_suspend_term_frame_exit

/-- info: 'TrustIr.FrameLifetime.coro_suspend_dispatch_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.coro_suspend_dispatch_frame_exit

/-- info: 'TrustIr.FrameLifetime.static_step_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.static_step_frame_exit

/-- info: 'TrustIr.FrameLifetime.static_body_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.static_body_frame_exit

/-- info: 'TrustIr.FrameLifetime.unresolved_drop_invoke_dispatch_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.unresolved_drop_invoke_dispatch_exit

/-- info: 'TrustIr.FrameLifetime.every_body_instruction_admitted' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.every_body_instruction_admitted

/-- info: 'TrustIr.FrameLifetime.every_terminator_admitted' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.every_terminator_admitted

/-- info: 'TrustIr.FrameLifetime.resolve_drop_terminator_flag' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.resolve_drop_terminator_flag

/-- info: 'TrustIr.FrameLifetime.FrameBlockShape.admitted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameBlockShape.admitted

/-- info: 'TrustIr.FrameLifetime.FrameProgramShape.admitted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.FrameProgramShape.admitted

/-- info: 'TrustIr.FrameLifetime.shaped_frame_entry_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.shaped_frame_entry_exit

/-- info: 'TrustIr.FrameLifetime.decoded_shaped_frame_entry_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decoded_shaped_frame_entry_exit

/-- info: 'TrustIr.FrameLifetime.decoded_frame_shape_check' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decoded_frame_shape_check

/-- info: 'TrustIr.FrameLifetime.prepared_function_property' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.prepared_function_property

/-- info: 'TrustIr.FrameLifetime.converted_function_block_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.converted_function_block_shape

/-- info: 'TrustIr.FrameLifetime.decoded_context_program_shape' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decoded_context_program_shape

/-- info: 'TrustIr.FrameLifetime.shaped_function_frame_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.shaped_function_frame_exit

/-- info: 'TrustIr.FrameLifetime.decoded_module_frame_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decoded_module_frame_exit

/-- info: 'TrustIr.FrameLifetime.decoded_module_empty_frame_exit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FrameLifetime.decoded_module_empty_frame_exit

/-- info: 'TrustIr.AYUnaryReplay.entry_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.entry_decomposition

/-- info: 'TrustIr.AYUnaryReplay.finishEntry_congr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.finishEntry_congr

/-- info: 'TrustIr.AYUnaryReplay.EntryTrace.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.EntryTrace.correct

/-- info: 'TrustIr.AYUnaryReplay.EntryTrace.built_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.EntryTrace.built_correct

/-- info: 'TrustIr.AYUnaryReplay.EntryTrace.build_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.EntryTrace.build_zero

/-- info: 'TrustIr.AYUnaryReplay.EntryTrace.build_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.EntryTrace.build_rejected

/-- info: 'TrustIr.AYCastReplay.Carrier.build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYCastReplay.Carrier.build

/-- info: 'TrustIr.AYCastReplay.plan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYCastReplay.plan

/-- info: 'TrustIr.AYCastReplay.Site.build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYCastReplay.Site.build

/-- info: 'TrustIr.TrustIrExpr.SMTSourceInput.build' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TrustIrExpr.SMTSourceInput.build

/-- info: 'TrustIr.AYCastReplay.body_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYCastReplay.body_request

/-- info: 'TrustIr.AYCastReplay.body_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYCastReplay.body_error

/-- info: 'TrustIr.AYCastReplay.Node.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYCastReplay.Node.correct

/-- info: 'TrustIr.AYCastReplay.Node.build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYCastReplay.Node.build

/-- info: 'TrustIr.AYDivisionReplay.Site.build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYDivisionReplay.Site.build

/-- info: 'TrustIr.AYDivisionReplay.publishDecoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYDivisionReplay.publishDecoded

/-- info: 'TrustIr.AYDivisionReplay.body_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYDivisionReplay.body_decoded

/-- info: 'TrustIr.AYDivisionReplay.body_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYDivisionReplay.body_request

/-- info: 'TrustIr.AYDivisionReplay.body_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYDivisionReplay.body_error

/-- info: 'TrustIr.AYDivisionReplay.Node.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYDivisionReplay.Node.correct

/-- info: 'TrustIr.AYDivisionReplay.Node.build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYDivisionReplay.Node.build

/-- info: 'TrustIrEval.runDecodedBatchWith_eq_map' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIrEval.runDecodedBatchWith_eq_map

/-- info: 'TrustIr.AYUnaryReplay.DecodedEntryTrace.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.DecodedEntryTrace.correct

/-- info: 'TrustIr.AYUnaryReplay.DecodedModuleTrace.correct' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.DecodedModuleTrace.correct

/-- info: 'TrustIr.AYUnaryReplay.DecodedEntryTrace.build_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.DecodedEntryTrace.build_zero

/-- info: 'TrustIr.AYUnaryReplay.DecodedModuleTrace.build_zero' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.DecodedModuleTrace.build_zero

/-- info: 'TrustIr.AYUnaryReplay.DecodedBatchEntries.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.DecodedBatchEntries.correct

/-- info: 'TrustIr.AYUnaryReplay.DecodedBatchTrace.correct' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.DecodedBatchTrace.correct

/-- info: 'TrustIr.AYUnaryReplay.DecodedBatchTrace.consume_correct' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AYUnaryReplay.DecodedBatchTrace.consume_correct

/-- info: 'TrustIr.Ty.bitWidthAtPointerBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.Ty.bitWidthAtPointerBits

/-- info: 'TrustIr.TargetWidthDefinition.default_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TargetWidthDefinition.default_unchanged

/-- info: 'TrustIr.TargetWidthDefinition.model_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TargetWidthDefinition.model_unchanged

/-- info: 'TrustIr.TargetWidthDefinition.query_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.TargetWidthDefinition.query_unchanged

/-- info: 'TrustIr.SourceLayout.finish_result' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.finish_result

/-- info: 'TrustIr.SourceLayout.finish_ok_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.finish_ok_iff

/-- info: 'TrustIr.SourceLayout.finish_overflow_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.finish_overflow_iff

/-- info: 'TrustIr.SourceLayout.MemoDerivation.empty' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.MemoDerivation.empty

/-- info: 'TrustIr.SourceLayout.MemoDerivation.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.MemoDerivation.insert

/-- info: 'TrustIr.SourceLayout.solve_derivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.solve_derivation

/-- info: 'TrustIr.SourceLayout.Graph.query_derivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.query_derivation

/-- info: 'TrustIr.SourceLayout.NodeDerivation.present' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.present

/-- info: 'TrustIr.SourceLayout.NodeDerivation.done_result' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.done_result

/-- info: 'TrustIr.SourceLayout.Graph.query_finished_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.query_finished_bounds

/-- info: 'TrustIr.SourceLayout.DerivationControls.forged_cache_is_returned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DerivationControls.forged_cache_is_returned

/-- info: 'TrustIr.SourceLayout.DerivationControls.forged_cache_has_no_derivation' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DerivationControls.forged_cache_has_no_derivation

/-- info: 'TrustIr.SourceLayout.DerivationControls.forged_cache_is_invalid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DerivationControls.forged_cache_is_invalid

/-- info: 'TrustIr.SourceLayout.DerivationControls.fresh_missing_root_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DerivationControls.fresh_missing_root_refuses

/-- info: 'TrustIr.SourceLayout.Graph.Extends.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.Extends.refl

/-- info: 'TrustIr.SourceLayout.Graph.Extends.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.Extends.trans

/-- info: 'TrustIr.SourceLayout.NodeDerivation.weaken' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.weaken

/-- info: 'TrustIr.SourceLayout.MemoDerivation.weaken' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.MemoDerivation.weaken

/-- info: 'TrustIr.SourceLayout.Graph.Bounded.empty' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.Bounded.empty

/-- info: 'TrustIr.SourceLayout.Graph.Bounded.allocate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.Bounded.allocate

/-- info: 'TrustIr.SourceLayout.Graph.Extends.allocate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.Extends.allocate

/-- info: 'TrustIr.SourceLayout.Graph.Bounded.put' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.Bounded.put

/-- info: 'TrustIr.SourceLayout.Graph.Growth.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.Growth.refl

/-- info: 'TrustIr.SourceLayout.Graph.Growth.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.Growth.trans

/-- info: 'TrustIr.SourceLayout.PreservesGraph.bind' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreservesGraph.bind

/-- info: 'TrustIr.SourceLayout.PreservesState.forIn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreservesState.forIn

/-- info: 'TrustIr.SourceLayout.prepare_derivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.prepare_derivation

/-- info: 'TrustIr.SourceLayout.Session.query_preserves_derivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.query_preserves_derivation

/-- info: 'TrustIr.SourceLayout.Session.Reachable.invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.invariant

/-- info: 'TrustIr.SourceLayout.Session.Reachable.index_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.index_eq

/-- info: 'TrustIr.SourceLayout.Session.Reachable.extends_prepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.extends_prepared

/-- info: 'TrustIr.SourceLayout.Session.Reachable.cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.cached

/-- info: 'TrustIr.SourceLayout.query_session_derivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_session_derivation

/-- info: 'TrustIr.SourceLayout.SessionControls.stale_memo_is_derived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SessionControls.stale_memo_is_derived

/-- info: 'TrustIr.SourceLayout.SessionControls.stale_query_returns_old_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SessionControls.stale_query_returns_old_cache

/-- info: 'TrustIr.SourceLayout.SessionControls.overwritten_memo_invalid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SessionControls.overwritten_memo_invalid

/-- info: 'TrustIr.SourceLayout.SessionControls.stale_not_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SessionControls.stale_not_reachable

/-- info: 'TrustIr.SourceLayout.SessionControls.normal_first_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SessionControls.normal_first_query

/-- info: 'TrustIr.SourceLayout.SessionControls.normal_repeat_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SessionControls.normal_repeat_query

/-- info: 'TrustIr.SourceLayout.SessionControls.normal_repeat_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SessionControls.normal_repeat_invariant

/-- info: 'TrustIr.SourceLayout.NodeDerivation.execution' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.execution

/-- info: 'TrustIr.SourceLayout.Equation.Executes.to_node' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.to_node

/-- info: 'TrustIr.SourceLayout.Equation.Executes.sequence_body' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.sequence_body

/-- info: 'TrustIr.SourceLayout.Equation.Executes.alias_child' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.alias_child

/-- info: 'TrustIr.SourceLayout.enumEquation_finish_property' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enumEquation_finish_property

/-- info: 'TrustIr.SourceLayout.Equation.Executes.scaled_bounds' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.scaled_bounds

/-- info: 'TrustIr.SourceLayout.Equation.Executes.finalizes' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.finalizes

/-- info: 'TrustIr.SourceLayout.Equation.Executes.enum_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.enum_bounds

/-- info: 'TrustIr.SourceLayout.Equation.Executes.sequence_finalizes' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.sequence_finalizes

/-- info: 'TrustIr.SourceLayout.Graph.query_alias_derivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.query_alias_derivation

/-- info: 'TrustIr.SourceLayout.Graph.query_enum_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.query_enum_bounds

/-- info: 'TrustIr.SourceLayout.Graph.query_sequence_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.query_sequence_body

/-- info: 'TrustIr.SourceLayout.Graph.query_sequence_scaled_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.query_sequence_scaled_bounds

/-- info: 'TrustIr.SourceLayout.CombinatorControls.prefix_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CombinatorControls.prefix_refusal

/-- info: 'TrustIr.SourceLayout.CombinatorControls.body_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CombinatorControls.body_refusal

/-- info: 'TrustIr.SourceLayout.CombinatorControls.alias_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CombinatorControls.alias_exact

/-- info: 'TrustIr.SourceLayout.CombinatorControls.alias_child_derived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CombinatorControls.alias_child_derived

/-- info: 'TrustIr.SourceLayout.CombinatorControls.refused_enum_finalizer' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CombinatorControls.refused_enum_finalizer

/-- info: 'TrustIr.SourceLayout.CombinatorControls.refused_enum_cannot_execute' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CombinatorControls.refused_enum_cannot_execute

/-- info: 'TrustIr.SourceLayout.NodeDerivation.satisfies' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.satisfies

/-- info: 'TrustIr.SourceLayout.Graph.SummaryInvariant.empty' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.SummaryInvariant.empty

/-- info: 'TrustIr.SourceLayout.Graph.SummaryInvariant.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.SummaryInvariant.insert

/-- info: 'TrustIr.SourceLayout.solve_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.solve_satisfies

/-- info: 'TrustIr.SourceLayout.Graph.query_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.query_satisfies

/-- info: 'TrustIr.SourceLayout.Equation.WordGuarded.rule' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.WordGuarded.rule

/-- info: 'TrustIr.SourceLayout.finish_word_bounds' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.finish_word_bounds

/-- info: 'TrustIr.SourceLayout.WordBounds.unit' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.WordBounds.unit

/-- info: 'TrustIr.SourceLayout.WordBounds.never' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.WordBounds.never

/-- info: 'TrustIr.SourceLayout.Equation.WordGuarded.done' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.WordGuarded.done

/-- info: 'TrustIr.SourceLayout.Equation.WordGuarded.failed' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.WordGuarded.failed

/-- info: 'TrustIr.SourceLayout.Equation.WordGuarded.canonicalFields' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.WordGuarded.canonicalFields

/-- info: 'TrustIr.SourceLayout.Equation.WordGuarded.declaredFields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.WordGuarded.declaredFields

/-- info: 'TrustIr.SourceLayout.Equation.WordGuarded.scaled' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.WordGuarded.scaled

/-- info: 'TrustIr.SourceLayout.Equation.WordGuarded.enumeration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.WordGuarded.enumeration

/-- info: 'TrustIr.SourceLayout.Equation.WordGuarded.sequence' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.WordGuarded.sequence

/-- info: 'TrustIr.SourceLayout.Equation.WordGuarded.unit' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.WordGuarded.unit

/-- info: 'TrustIr.SourceLayout.prepare_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.prepare_word

/-- info: 'TrustIr.SourceLayout.Session.query_preserves_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.query_preserves_word

/-- info: 'TrustIr.SourceLayout.query_word_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_word_bounds

/-- info: 'TrustIr.SourceLayout.Session.Reachable.word_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.word_invariant

/-- info: 'TrustIr.SourceLayout.Session.Reachable.cached_word_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.cached_word_bounds

/-- info: 'TrustIr.SourceLayout.Session.Reachable.query_word_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.query_word_bounds

/-- info: 'TrustIr.SourceLayout.WordInvariantControls.oversized_not_bounded' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.WordInvariantControls.oversized_not_bounded

/-- info: 'TrustIr.SourceLayout.WordInvariantControls.empty_graph_invariant' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.WordInvariantControls.empty_graph_invariant

/-- info: 'TrustIr.SourceLayout.WordInvariantControls.forged_oversized_returned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.WordInvariantControls.forged_oversized_returned

/-- info: 'TrustIr.SourceLayout.WordInvariantControls.forged_memo_invalid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.WordInvariantControls.forged_memo_invalid

/-- info: 'TrustIr.SourceLayout.WordInvariantControls.cyclic_alias_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.WordInvariantControls.cyclic_alias_invariant

/-- info: 'TrustIr.SourceLayout.WordInvariantControls.cyclic_alias_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.WordInvariantControls.cyclic_alias_refuses

-- Node-indexed derivations and mixed-mode layout bounds.

/-- info: 'TrustIr.SourceLayout.NodeDerivation.satisfies_at' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.satisfies_at

/-- info: 'TrustIr.SourceLayout.Equation.IndexedRule.alias' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.IndexedRule.alias

/-- info: 'TrustIr.SourceLayout.Graph.IndexedInvariant.empty' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.IndexedInvariant.empty

/-- info: 'TrustIr.SourceLayout.Graph.IndexedInvariant.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.IndexedInvariant.insert

/-- info: 'TrustIr.SourceLayout.MemoDerivation.satisfies_at' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.MemoDerivation.satisfies_at

/-- info: 'TrustIr.SourceLayout.solve_satisfies_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.solve_satisfies_at

/-- info: 'TrustIr.SourceLayout.Graph.query_satisfies_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.query_satisfies_at

/-- info: 'TrustIr.SourceLayout.Graph.SummaryInvariant.indexed' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.SummaryInvariant.indexed

/-- info: 'TrustIr.SourceLayout.Equation.IndexedRule.done' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.IndexedRule.done

/-- info: 'TrustIr.SourceLayout.Equation.Finalizes.indexed' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Finalizes.indexed

/-- info: 'TrustIr.SourceLayout.FinishBounds.unit' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FinishBounds.unit

/-- info: 'TrustIr.SourceLayout.FinishBounds.never' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FinishBounds.never

/-- info: 'TrustIr.SourceLayout.FinishBounds.execution' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FinishBounds.execution

/-- info: 'TrustIr.SourceLayout.Equation.mode_alias' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.mode_alias

/-- info: 'TrustIr.SourceLayout.Equation.execution_alias' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.execution_alias

/-- info: 'TrustIr.SourceLayout.canonicalFields_mode_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.canonicalFields_mode_rule

/-- info: 'TrustIr.SourceLayout.declaredFields_mode_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.declaredFields_mode_rule

/-- info: 'TrustIr.SourceLayout.scaled_mode_rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.scaled_mode_rule

/-- info: 'TrustIr.SourceLayout.enum_mode_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enum_mode_rule

/-- info: 'TrustIr.SourceLayout.Graph.query_mode_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.query_mode_bounds

/-- info: 'TrustIr.SourceLayout.MemoDerivation.mode_bounds' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.MemoDerivation.mode_bounds

/-- info: 'TrustIr.SourceLayout.IndexedInvariantControls.byte_only_execution' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.IndexedInvariantControls.byte_only_execution

/-- info: 'TrustIr.SourceLayout.IndexedInvariantControls.byte_only_not_shape' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.IndexedInvariantControls.byte_only_not_shape

/-- info: 'TrustIr.SourceLayout.IndexedInvariantControls.wrong_mode_alias_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.IndexedInvariantControls.wrong_mode_alias_returns

/-- info: 'TrustIr.SourceLayout.IndexedInvariantControls.wrong_mode_alias_has_no_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.IndexedInvariantControls.wrong_mode_alias_has_no_invariant

/-- info: 'TrustIr.SourceLayout.IndexedInvariantControls.cyclic_mode_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.IndexedInvariantControls.cyclic_mode_invariant

/-- info: 'TrustIr.SourceLayout.IndexedInvariantControls.cyclic_mode_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.IndexedInvariantControls.cyclic_mode_refuses

-- Exact target-specific scalar interning and real session histories.

/-- info: 'TrustIr.SourceLayout.ScalarSummary.key_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ScalarSummary.key_injective

/-- info: 'TrustIr.SourceLayout.ScalarSummary.of_finish' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ScalarSummary.of_finish

/-- info: 'TrustIr.SourceLayout.ScalarSummary.finish_bounds' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ScalarSummary.finish_bounds

/-- info: 'TrustIr.SourceLayout.Graph.ScalarInvariant.empty' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.ScalarInvariant.empty

/-- info: 'TrustIr.SourceLayout.Graph.ScalarInvariant.lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.ScalarInvariant.lookup

/-- info: 'TrustIr.SourceLayout.Graph.ScalarInvariant.weaken' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.ScalarInvariant.weaken

/-- info: 'TrustIr.SourceLayout.Graph.ScalarInvariant.put' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.ScalarInvariant.put

/-- info: 'TrustIr.SourceLayout.Graph.ScalarInvariant.cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.ScalarInvariant.cache

/-- info: 'TrustIr.SourceLayout.Graph.ScalarInvariant.derivation_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.ScalarInvariant.derivation_value

/-- info: 'TrustIr.SourceLayout.prepare_scalars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.prepare_scalars

/-- info: 'TrustIr.SourceLayout.Session.query_preserves_scalars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.query_preserves_scalars

/-- info: 'TrustIr.SourceLayout.Session.Reachable.scalar_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.scalar_invariant

/-- info: 'TrustIr.SourceLayout.Session.Reachable.cached_scalar_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.cached_scalar_value

/-- info: 'TrustIr.SourceLayout.Session.Reachable.cached_scalar_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.cached_scalar_bounds

/-- info: 'TrustIr.SourceLayout.ScalarInvariantControls.requested_scalar' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ScalarInvariantControls.requested_scalar

/-- info: 'TrustIr.SourceLayout.ScalarInvariantControls.arbitrary_key_collision' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ScalarInvariantControls.arbitrary_key_collision

/-- info: 'TrustIr.SourceLayout.ScalarInvariantControls.colliding_values_differ' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ScalarInvariantControls.colliding_values_differ

/-- info: 'TrustIr.SourceLayout.ScalarInvariantControls.counterfeit_shape_bounded' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ScalarInvariantControls.counterfeit_shape_bounded

/-- info: 'TrustIr.SourceLayout.ScalarInvariantControls.counterfeit_query_returns' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ScalarInvariantControls.counterfeit_query_returns

/-- info: 'TrustIr.SourceLayout.ScalarInvariantControls.counterfeit_cache_invalid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ScalarInvariantControls.counterfeit_cache_invalid

-- Exact compiler origins for reachable source-layout root caches.
/-- info: 'TrustIr.SourceLayout.Session.query_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.query_selection
/-- info: 'TrustIr.SourceLayout.Session.CompiledRoot.weaken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.CompiledRoot.weaken
/-- info: 'TrustIr.SourceLayout.Session.Reachable.roots_compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.roots_compiled
/-- info: 'TrustIr.SourceLayout.Session.Reachable.query_compilation_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.query_compilation_origin
/-- info: 'TrustIr.SourceLayout.query_compilation_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_compilation_origin
/-- info: 'TrustIr.SourceLayout.RootOriginControls.different_types_same_bucket' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootOriginControls.different_types_same_bucket
/-- info: 'TrustIr.SourceLayout.RootOriginControls.first_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootOriginControls.first_query
/-- info: 'TrustIr.SourceLayout.RootOriginControls.colliding_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootOriginControls.colliding_query
/-- info: 'TrustIr.SourceLayout.RootOriginControls.colliding_entries_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootOriginControls.colliding_entries_retained
/-- info: 'TrustIr.SourceLayout.RootOriginControls.colliding_history_compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootOriginControls.colliding_history_compiled
/-- info: 'TrustIr.SourceLayout.RootOriginControls.wrong_type_entry_skipped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootOriginControls.wrong_type_entry_skipped
/-- info: 'TrustIr.SourceLayout.RootOriginControls.wrong_mode_entry_skipped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootOriginControls.wrong_mode_entry_skipped
/-- info: 'TrustIr.SourceLayout.RootOriginControls.forged_derivation_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootOriginControls.forged_derivation_valid
/-- info: 'TrustIr.SourceLayout.RootOriginControls.forged_matching_entry_returned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootOriginControls.forged_matching_entry_returned
/-- info: 'TrustIr.SourceLayout.RootOriginControls.forged_not_reachable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootOriginControls.forged_not_reachable

-- Actual aggregate construction retains mode-sensitive guards and copy obligations.
/-- info: 'TrustIr.SourceLayout.Equation.IndexedRule.reowner' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.IndexedRule.reowner
/-- info: 'TrustIr.SourceLayout.Index.nodeMode_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Index.nodeMode_node
/-- info: 'TrustIr.SourceLayout.Index.nodeMode_dynamic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Index.nodeMode_dynamic
/-- info: 'TrustIr.SourceLayout.Equation.ModeGuarded.indexed' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.ModeGuarded.indexed
/-- info: 'TrustIr.SourceLayout.Equation.ModeGuarded.execution' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.ModeGuarded.execution
/-- info: 'TrustIr.SourceLayout.Equation.ModeGuarded.done' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.ModeGuarded.done
/-- info: 'TrustIr.SourceLayout.Equation.ModeGuarded.failed' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.ModeGuarded.failed
/-- info: 'TrustIr.SourceLayout.Equation.Finalizes.mode_guarded' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Finalizes.mode_guarded
/-- info: 'TrustIr.SourceLayout.Equation.ModeGuarded.canonicalFields' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.ModeGuarded.canonicalFields
/-- info: 'TrustIr.SourceLayout.Equation.ModeGuarded.declaredFields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.ModeGuarded.declaredFields
/-- info: 'TrustIr.SourceLayout.Equation.ModeGuarded.scaled' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.ModeGuarded.scaled
/-- info: 'TrustIr.SourceLayout.Equation.ModeGuarded.enumeration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.ModeGuarded.enumeration
/-- info: 'TrustIr.SourceLayout.Equation.ModeGuarded.sequence' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.ModeGuarded.sequence
/-- info: 'TrustIr.SourceLayout.Equation.ModeGuarded.unit' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.ModeGuarded.unit
/-- info: 'TrustIr.SourceLayout.NodeDerivation.mode_guarded' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.mode_guarded
/-- info: 'TrustIr.SourceLayout.Equation.IndexedRule.copy_mode' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.IndexedRule.copy_mode
/-- info: 'TrustIr.SourceLayout.Equation.IndexedRule.copy_execution' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.IndexedRule.copy_execution
/-- info: 'TrustIr.SourceLayout.Graph.ModeInvariant.copy_same' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.ModeInvariant.copy_same
/-- info: 'TrustIr.SourceLayout.Graph.ModeInvariant.copy_execution' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.ModeInvariant.copy_execution
/-- info: 'TrustIr.SourceLayout.StructCompilation.mode_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StructCompilation.mode_guarded
/-- info: 'TrustIr.SourceLayout.StructCompilation.derivation_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StructCompilation.derivation_bounds
/-- info: 'TrustIr.SourceLayout.StructCompilation.reserved_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StructCompilation.reserved_rule
/-- info: 'TrustIr.SourceLayout.ClosureCompilation.mode_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosureCompilation.mode_guarded
/-- info: 'TrustIr.SourceLayout.ClosureCompilation.derivation_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosureCompilation.derivation_bounds
/-- info: 'TrustIr.SourceLayout.ClosureCompilation.reserved_rule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosureCompilation.reserved_rule
/-- info: 'TrustIr.SourceLayout.BuilderModeControls.actual_struct_construction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.BuilderModeControls.actual_struct_construction
/-- info: 'TrustIr.SourceLayout.BuilderModeControls.actual_struct_guarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.BuilderModeControls.actual_struct_guarded
/-- info: 'TrustIr.SourceLayout.BuilderModeControls.execution_accepts_byte_only' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.BuilderModeControls.execution_accepts_byte_only
/-- info: 'TrustIr.SourceLayout.BuilderModeControls.shape_refuses_byte_only' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.BuilderModeControls.shape_refuses_byte_only
/-- info: 'TrustIr.SourceLayout.BuilderModeControls.accepted_not_shape' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.BuilderModeControls.accepted_not_shape
/-- info: 'TrustIr.SourceLayout.BuilderModeControls.actual_shape_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.BuilderModeControls.actual_shape_reserved
/-- info: 'TrustIr.SourceLayout.BuilderModeControls.actual_execution_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.BuilderModeControls.actual_execution_reserved
/-- info: 'TrustIr.SourceLayout.BuilderModeControls.actual_closure_construction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.BuilderModeControls.actual_closure_construction
/-- info: 'TrustIr.SourceLayout.BuilderModeControls.actual_closure_guarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.BuilderModeControls.actual_closure_guarded
/-- info: 'TrustIr.SourceLayout.BuilderModeControls.shape_closure_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.BuilderModeControls.shape_closure_accepts
/-- info: 'TrustIr.SourceLayout.BuilderModeControls.execution_closure_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.BuilderModeControls.execution_closure_refuses

-- Complete actual compiler/session shape and byte bounds.
/-- info: 'TrustIr.SourceLayout.ShapeRoot.weaken' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeRoot.weaken
/-- info: 'TrustIr.SourceLayout.ShapeRoot.copy_rule' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeRoot.copy_rule
/-- info: 'TrustIr.SourceLayout.ShapeRoot.derivation_bounds' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeRoot.derivation_bounds
/-- info: 'TrustIr.SourceLayout.RootCompilation.shape_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.shape_root
/-- info: 'TrustIr.SourceLayout.RootCompilation.preserves_modes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.preserves_modes
/-- info: 'TrustIr.SourceLayout.prepare_modes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.prepare_modes
/-- info: 'TrustIr.SourceLayout.Session.query_preserves_modes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.query_preserves_modes
/-- info: 'TrustIr.SourceLayout.Session.Reachable.mode_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.mode_invariant
/-- info: 'TrustIr.SourceLayout.Session.CompiledRoot.shape_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.CompiledRoot.shape_root
/-- info: 'TrustIr.SourceLayout.Session.Reachable.query_mode_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.query_mode_bounds
/-- info: 'TrustIr.SourceLayout.Session.Reachable.cached_root_mode_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.cached_root_mode_bounds
/-- info: 'TrustIr.SourceLayout.query_mode_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_mode_bounds
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.execution_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.execution_first
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.shared_scalar_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.shared_scalar_shape
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.shape_repeated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.shape_repeated
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.shared_history_modes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.shared_history_modes
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.shared_root_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.shared_root_retained
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.typed_cached_shape_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.typed_cached_shape_bounds
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.dynamic_shape_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.dynamic_shape_query
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.dynamic_index_obligation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.dynamic_index_obligation
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.dynamic_local_shape_guard' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.dynamic_local_shape_guard
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.dynamic_result_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.dynamic_result_bounds
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.sparse_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.sparse_shape
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.sparse_missing_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.sparse_missing_refuses
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.cyclic_preparation_modes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.cyclic_preparation_modes
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.cyclic_shape_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.cyclic_shape_refuses

-- Ordered aggregate field containment and positive-storage separation.
/-- info: 'TrustIr.SourceLayout.Field.Separated.symm' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Field.Separated.symm
/-- info: 'TrustIr.SourceLayout.overlap_false_iff_separated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.overlap_false_iff_separated
/-- info: 'TrustIr.SourceLayout.hasOverlap_false_iff_separated' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.hasOverlap_false_iff_separated
/-- info: 'TrustIr.SourceLayout.FieldsSeparated.snoc' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldsSeparated.snoc
/-- info: 'TrustIr.SourceLayout.FieldsSeparated.reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldsSeparated.reverse
/-- info: 'TrustIr.SourceLayout.FieldsContained.reverse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldsContained.reverse
/-- info: 'TrustIr.SourceLayout.alignUp_lower_bound' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.alignUp_lower_bound
/-- info: 'TrustIr.SourceLayout.PlacementGeometry.empty' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PlacementGeometry.empty
/-- info: 'TrustIr.SourceLayout.canonicalFields_steps_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.canonicalFields_steps_geometry
/-- info: 'TrustIr.SourceLayout.Equation.Executes.canonicalFields_geometry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.canonicalFields_geometry
/-- info: 'TrustIr.SourceLayout.declaredFields_finish_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.declaredFields_finish_fields
/-- info: 'TrustIr.SourceLayout.declaredFields_finalizes_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.declaredFields_finalizes_separated
/-- info: 'TrustIr.SourceLayout.declaredFields_steps_contained' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.declaredFields_steps_contained
/-- info: 'TrustIr.SourceLayout.Equation.Executes.declaredFields_geometry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.declaredFields_geometry
/-- info: 'TrustIr.SourceLayout.Equation.FieldGuarded.failed' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.FieldGuarded.failed
/-- info: 'TrustIr.SourceLayout.Equation.FieldGuarded.canonicalFields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.FieldGuarded.canonicalFields
/-- info: 'TrustIr.SourceLayout.Equation.FieldGuarded.declaredFields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.FieldGuarded.declaredFields
/-- info: 'TrustIr.SourceLayout.Equation.FieldGuarded.sequence' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.FieldGuarded.sequence
/-- info: 'TrustIr.SourceLayout.NodeDerivation.field_geometry' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.field_geometry
/-- info: 'TrustIr.SourceLayout.StructCompilation.field_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StructCompilation.field_guarded
/-- info: 'TrustIr.SourceLayout.ClosureCompilation.field_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosureCompilation.field_guarded
/-- info: 'TrustIr.SourceLayout.StructCompilation.derivation_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StructCompilation.derivation_geometry
/-- info: 'TrustIr.SourceLayout.ClosureCompilation.derivation_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosureCompilation.derivation_geometry
/-- info: 'TrustIr.SourceLayout.GeometryControls.touching_shape_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.touching_shape_accepts
/-- info: 'TrustIr.SourceLayout.GeometryControls.touching_execution_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.touching_execution_accepts
/-- info: 'TrustIr.SourceLayout.GeometryControls.overlapping_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.overlapping_refuses
/-- info: 'TrustIr.SourceLayout.GeometryControls.out_of_range_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.out_of_range_refuses
/-- info: 'TrustIr.SourceLayout.GeometryControls.empty_inside_storage_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.empty_inside_storage_accepts
/-- info: 'TrustIr.SourceLayout.GeometryControls.omitted_empty_execution_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.omitted_empty_execution_accepts
/-- info: 'TrustIr.SourceLayout.GeometryControls.omitted_empty_shape_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.omitted_empty_shape_refuses
/-- info: 'TrustIr.SourceLayout.GeometryControls.unconditional_alignment_bound_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.unconditional_alignment_bound_false
/-- info: 'TrustIr.SourceLayout.GeometryControls.canonical_padding_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.canonical_padding_accepts
/-- info: 'TrustIr.SourceLayout.GeometryControls.actual_struct_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.actual_struct_pair
/-- info: 'TrustIr.SourceLayout.GeometryControls.actual_struct_derivation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.actual_struct_derivation
/-- info: 'TrustIr.SourceLayout.GeometryControls.actual_struct_geometry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.actual_struct_geometry
/-- info: 'TrustIr.SourceLayout.GeometryControls.actual_closure_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.actual_closure_pair
/-- info: 'TrustIr.SourceLayout.GeometryControls.actual_closure_derivation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.actual_closure_derivation
/-- info: 'TrustIr.SourceLayout.GeometryControls.actual_closure_geometry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.actual_closure_geometry
/-- info: 'TrustIr.SourceLayout.GeometryControls.actual_closure_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.actual_closure_query
/-- info: 'TrustIr.SourceLayout.GeometryControls.omitted_positive_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.omitted_positive_refuses
/-- info: 'TrustIr.SourceLayout.GeometryControls.canonical_finalizer_accepts_forged_state' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.canonical_finalizer_accepts_forged_state
/-- info: 'TrustIr.SourceLayout.GeometryControls.forged_geometry_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.forged_geometry_false
/-- info: 'TrustIr.SourceLayout.GeometryControls.canonical_finalizer_alone_insufficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.canonical_finalizer_alone_insufficient
/-- info: 'TrustIr.SourceLayout.GeometryControls.forged_placement_not_derived' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.GeometryControls.forged_placement_not_derived

-- Actual alignment divisibility, aggregate geometry and zero-sized omission boundaries.
/-- info: 'TrustIr.SourceLayout.alignUp_aligned' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.alignUp_aligned
/-- info: 'TrustIr.SourceLayout.FieldsAligned.reverse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldsAligned.reverse
/-- info: 'TrustIr.SourceLayout.FieldsAligned.weaken' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldsAligned.weaken
/-- info: 'TrustIr.SourceLayout.AlignmentGeometry.weaken' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentGeometry.weaken
/-- info: 'TrustIr.SourceLayout.canonicalFields_steps_aligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.canonicalFields_steps_aligned
/-- info: 'TrustIr.SourceLayout.Equation.Executes.canonicalFields_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.canonicalFields_alignment
/-- info: 'TrustIr.SourceLayout.declaredFields_steps_aligned' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.declaredFields_steps_aligned
/-- info: 'TrustIr.SourceLayout.declaredFields_finish_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.declaredFields_finish_exact
/-- info: 'TrustIr.SourceLayout.powerOfTwo_nonzero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.powerOfTwo_nonzero
/-- info: 'TrustIr.SourceLayout.declaredFields_initial_facts' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.declaredFields_initial_facts
/-- info: 'TrustIr.SourceLayout.Equation.Executes.declaredFields_power_of_two' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.declaredFields_power_of_two
/-- info: 'TrustIr.SourceLayout.Equation.Executes.declaredFields_alignment' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.declaredFields_alignment
/-- info: 'TrustIr.SourceLayout.Equation.AlignmentGuarded.failed' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.AlignmentGuarded.failed
/-- info: 'TrustIr.SourceLayout.Equation.AlignmentGuarded.canonicalFields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.AlignmentGuarded.canonicalFields
/-- info: 'TrustIr.SourceLayout.Equation.AlignmentGuarded.declaredFields' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.AlignmentGuarded.declaredFields
/-- info: 'TrustIr.SourceLayout.Equation.AlignmentGuarded.sequence' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.AlignmentGuarded.sequence
/-- info: 'TrustIr.SourceLayout.NodeDerivation.alignment_geometry' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.alignment_geometry
/-- info: 'TrustIr.SourceLayout.StructCompilation.alignment_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StructCompilation.alignment_guarded
/-- info: 'TrustIr.SourceLayout.ClosureCompilation.alignment_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosureCompilation.alignment_guarded
/-- info: 'TrustIr.SourceLayout.StructCompilation.derivation_alignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StructCompilation.derivation_alignment
/-- info: 'TrustIr.SourceLayout.ClosureCompilation.derivation_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosureCompilation.derivation_alignment
/-- info: 'TrustIr.SourceLayout.AlignmentControls.zero_divisor_refuses' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentControls.zero_divisor_refuses
/-- info: 'TrustIr.SourceLayout.AlignmentControls.rounding_overflow_refuses' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentControls.rounding_overflow_refuses
/-- info: 'TrustIr.SourceLayout.AlignmentControls.non_power_divisor_rounds' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentControls.non_power_divisor_rounds
/-- info: 'TrustIr.SourceLayout.AlignmentControls.misaligned_field_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentControls.misaligned_field_refuses
/-- info: 'TrustIr.SourceLayout.AlignmentControls.excessive_field_alignment_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentControls.excessive_field_alignment_refuses
/-- info: 'TrustIr.SourceLayout.AlignmentControls.nonmultiple_size_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentControls.nonmultiple_size_refuses
/-- info: 'TrustIr.SourceLayout.AlignmentControls.zero_aggregate_alignment_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentControls.zero_aggregate_alignment_refuses
/-- info: 'TrustIr.SourceLayout.AlignmentControls.nonpower_aggregate_alignment_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentControls.nonpower_aggregate_alignment_refuses
/-- info: 'TrustIr.SourceLayout.AlignmentControls.packed_query_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentControls.packed_query_accepts
/-- info: 'TrustIr.SourceLayout.AlignmentControls.actual_packed_construction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentControls.actual_packed_construction
/-- info: 'TrustIr.SourceLayout.AlignmentControls.actual_packed_derivation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentControls.actual_packed_derivation
/-- info: 'TrustIr.SourceLayout.AlignmentControls.actual_packed_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentControls.actual_packed_alignment
/-- info: 'TrustIr.SourceLayout.AlignmentControls.omitted_query_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentControls.omitted_query_accepts
/-- info: 'TrustIr.SourceLayout.AlignmentControls.actual_omitted_construction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentControls.actual_omitted_construction
/-- info: 'TrustIr.SourceLayout.AlignmentControls.actual_omitted_derivation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentControls.actual_omitted_derivation
/-- info: 'TrustIr.SourceLayout.AlignmentControls.omitted_alignment_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentControls.omitted_alignment_preserved
/-- info: 'TrustIr.SourceLayout.AlignmentControls.omitted_unconditional_cap_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentControls.omitted_unconditional_cap_false
/-- info: 'TrustIr.SourceLayout.AlignmentControls.closure_all_fields_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentControls.closure_all_fields_aligned

-- Canonical enum payload storage, tag separation and actual ordered child derivations.
/-- info: 'TrustIr.SourceLayout.EnumConstruction.canonical_view' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.canonical_view
/-- info: 'TrustIr.SourceLayout.Equation.Executes.canonicalEnum_view' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.canonicalEnum_view
/-- info: 'TrustIr.SourceLayout.Field.Separated.translate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Field.Separated.translate
/-- info: 'TrustIr.SourceLayout.FieldsSeparated.translate' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldsSeparated.translate
/-- info: 'TrustIr.SourceLayout.FieldsContained.translate' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldsContained.translate
/-- info: 'TrustIr.SourceLayout.FieldsContained.weaken' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldsContained.weaken
/-- info: 'TrustIr.SourceLayout.payload_field_lower_bound' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.payload_field_lower_bound
/-- info: 'TrustIr.SourceLayout.variant_size_le_payload' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.variant_size_le_payload
/-- info: 'TrustIr.SourceLayout.placePayload_geometry' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.placePayload_geometry
/-- info: 'TrustIr.SourceLayout.EnumConstruction.canonical_geometry' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.canonical_geometry
/-- info: 'TrustIr.SourceLayout.EnumConstruction.canonical_tag_separated' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.canonical_tag_separated
/-- info: 'TrustIr.SourceLayout.enum_children_geometry' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enum_children_geometry
/-- info: 'TrustIr.SourceLayout.Equation.Executes.canonicalEnum_geometry' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.canonicalEnum_geometry
/-- info: 'TrustIr.SourceLayout.EnumConstruction.canonical_tag' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.canonical_tag
/-- info: 'TrustIr.SourceLayout.Equation.Executes.canonicalEnum_tag_separated' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.canonicalEnum_tag_separated
/-- info: 'TrustIr.SourceLayout.NodeDerivation.canonicalEnum_geometry' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.canonicalEnum_geometry
/-- info: 'TrustIr.SourceLayout.NodeDerivation.canonicalEnum_tag_separated' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.canonicalEnum_tag_separated
/-- info: 'TrustIr.SourceLayout.EnumGeometryControls.variant_children_geometry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGeometryControls.variant_children_geometry
/-- info: 'TrustIr.SourceLayout.EnumGeometryControls.actual_graph_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGeometryControls.actual_graph_query
/-- info: 'TrustIr.SourceLayout.EnumGeometryControls.actual_graph_geometry' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGeometryControls.actual_graph_geometry
/-- info: 'TrustIr.SourceLayout.EnumGeometryControls.actual_graph_tag_separated' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGeometryControls.actual_graph_tag_separated
/-- info: 'TrustIr.SourceLayout.EnumGeometryControls.source_shape_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGeometryControls.source_shape_query
/-- info: 'TrustIr.SourceLayout.EnumGeometryControls.source_execution_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGeometryControls.source_execution_query
/-- info: 'TrustIr.SourceLayout.EnumGeometryControls.mutually_exclusive_variants_share_storage' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGeometryControls.mutually_exclusive_variants_share_storage
/-- info: 'TrustIr.SourceLayout.EnumGeometryControls.raw_finalizer_accepts_corrupt_child' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGeometryControls.raw_finalizer_accepts_corrupt_child
/-- info: 'TrustIr.SourceLayout.EnumGeometryControls.corrupt_child_geometry_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGeometryControls.corrupt_child_geometry_false
/-- info: 'TrustIr.SourceLayout.EnumGeometryControls.corrupt_enum_geometry_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGeometryControls.corrupt_enum_geometry_false
/-- info: 'TrustIr.SourceLayout.EnumGeometryControls.corrupt_tag_still_separated' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGeometryControls.corrupt_tag_still_separated

-- Descriptor enum storage, checked tag/niche lanes and actual child-collection contracts.
/-- info: 'TrustIr.SourceLayout.EnumConstruction.descriptor_finish' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.descriptor_finish
/-- info: 'TrustIr.SourceLayout.EnumConstruction.descriptor_checks' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.descriptor_checks
/-- info: 'TrustIr.SourceLayout.Equation.Executes.descriptorEnum_view' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.descriptorEnum_view
/-- info: 'TrustIr.SourceLayout.enum_children_property' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enum_children_property
/-- info: 'TrustIr.SourceLayout.EnumConstruction.descriptor_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.descriptor_exact
/-- info: 'TrustIr.SourceLayout.EnumConstruction.descriptor_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.descriptor_geometry
/-- info: 'TrustIr.SourceLayout.EnumConstruction.direct_lane' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.direct_lane
/-- info: 'TrustIr.SourceLayout.EnumConstruction.direct_tag_separated' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.direct_tag_separated
/-- info: 'TrustIr.SourceLayout.EnumConstruction.niche_lane' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.niche_lane
/-- info: 'TrustIr.SourceLayout.EnumConstruction.niche_carrier' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.niche_carrier
/-- info: 'TrustIr.SourceLayout.EnumConstruction.niche_other_fields_separated' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.niche_other_fields_separated
/-- info: 'TrustIr.SourceLayout.enum_children_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enum_children_length
/-- info: 'TrustIr.SourceLayout.Equation.Executes.descriptorEnum_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.descriptorEnum_header
/-- info: 'TrustIr.SourceLayout.Equation.Executes.descriptorEnum_geometry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.descriptorEnum_geometry
/-- info: 'TrustIr.SourceLayout.Equation.Executes.descriptorEnum_variant_count' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.descriptorEnum_variant_count
/-- info: 'TrustIr.SourceLayout.Equation.Executes.descriptorEnum_direct_separated' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.descriptorEnum_direct_separated
/-- info: 'TrustIr.SourceLayout.EnumConstruction.niche_range_bounds' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.niche_range_bounds
/-- info: 'TrustIr.SourceLayout.NodeDerivation.descriptorEnum_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.descriptorEnum_geometry
/-- info: 'TrustIr.SourceLayout.Equation.Executes.descriptorEnum_niche_carrier' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.descriptorEnum_niche_carrier
/-- info: 'TrustIr.SourceLayout.Equation.Executes.descriptorEnum_niche_separated' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.descriptorEnum_niche_separated
/-- info: 'TrustIr.SourceLayout.NodeDerivation.descriptorEnum_direct_separated' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.descriptorEnum_direct_separated
/-- info: 'TrustIr.SourceLayout.NodeDerivation.descriptorEnum_niche_carrier' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.descriptorEnum_niche_carrier
/-- info: 'TrustIr.SourceLayout.NodeDerivation.descriptorEnum_niche_separated' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.descriptorEnum_niche_separated
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.direct_children' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.direct_children
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.direct_graph_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.direct_graph_query
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.direct_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.direct_geometry
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.direct_source_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.direct_source_shape
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.direct_source_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.direct_source_execution
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.direct_overlap_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.direct_overlap_refuses
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.unaligned_tag_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.unaligned_tag_refuses
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.out_of_range_tag_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.out_of_range_tag_refuses
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.niche_construction' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.niche_construction
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.niche_source_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.niche_source_shape
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.niche_source_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.niche_source_execution
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.niche_lane_within_parent' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.niche_lane_within_parent
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.niche_carrier_witness' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.niche_carrier_witness
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.niche_invalid_interval_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.niche_invalid_interval_refuses
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.niche_mask_overflow_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.niche_mask_overflow_refuses
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.missing_carrier_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.missing_carrier_refuses
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.encoded_payload_overlap_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.encoded_payload_overlap_refuses
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.uncovered_inhabited_row_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.uncovered_inhabited_row_refuses
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.single_inhabited_preserves_rows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.single_inhabited_preserves_rows
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.inactive_offsets_refuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.inactive_offsets_refuse
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.one_untagged_row_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.one_untagged_row_accepts
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.multiple_untagged_rows_refuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.multiple_untagged_rows_refuse
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.own_child_geometry' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.own_child_geometry
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.raw_accepts_parent_mismatch' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.raw_accepts_parent_mismatch
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.parent_geometry_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.parent_geometry_false
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.public_parent_mismatch_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.public_parent_mismatch_refuses
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.niche_graph_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.niche_graph_query
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.niche_node_carrier' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.niche_node_carrier
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.nonempty_encoded_payload_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.nonempty_encoded_payload_accepts

/-- info: 'TrustIr.SourceLayout.StepsCertified.derivation' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StepsCertified.derivation
/-- info: 'TrustIr.SourceLayout.StepsCertified.invariant' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StepsCertified.invariant
/-- info: 'TrustIr.SourceLayout.NodeDerivation.satisfies_contextual' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.satisfies_contextual
/-- info: 'TrustIr.SourceLayout.Equation.IndexedRule.contextual' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.IndexedRule.contextual
/-- info: 'TrustIr.SourceLayout.Graph.IndexedInvariant.contextual' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.IndexedInvariant.contextual
/-- info: 'TrustIr.SourceLayout.MemoDerivation.satisfies_contextual' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.MemoDerivation.satisfies_contextual
/-- info: 'TrustIr.SourceLayout.solve_satisfies_contextual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.solve_satisfies_contextual
/-- info: 'TrustIr.SourceLayout.Graph.query_satisfies_contextual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.query_satisfies_contextual
/-- info: 'TrustIr.SourceLayout.Equation.ContextualRule.alias' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.ContextualRule.alias
/-- info: 'TrustIr.SourceLayout.Equation.ContextualRule.reowner' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.ContextualRule.reowner
/-- info: 'TrustIr.SourceLayout.Equation.ParentFieldGuarded.done' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.ParentFieldGuarded.done
/-- info: 'TrustIr.SourceLayout.Equation.ParentFieldGuarded.failed' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.ParentFieldGuarded.failed
/-- info: 'TrustIr.SourceLayout.Equation.ParentFieldGuarded.declaredFields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.ParentFieldGuarded.declaredFields
/-- info: 'TrustIr.SourceLayout.Equation.ParentFieldGuarded.descriptorVariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.ParentFieldGuarded.descriptorVariant
/-- info: 'TrustIr.SourceLayout.Graph.ParentFieldCertificates.weaken' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.ParentFieldCertificates.weaken
/-- info: 'TrustIr.SourceLayout.Graph.ParentFieldCertificates.child' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.ParentFieldCertificates.child
/-- info: 'TrustIr.SourceLayout.Equation.ContextualRule.descriptorEnum_geometry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.ContextualRule.descriptorEnum_geometry
/-- info: 'TrustIr.SourceLayout.Graph.ParentFieldCertificates.allocate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.ParentFieldCertificates.allocate
/-- info: 'TrustIr.SourceLayout.Graph.ParentFieldCertificates.put_below' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.ParentFieldCertificates.put_below
/-- info: 'TrustIr.SourceLayout.Graph.ParentFieldCertificates.reverse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.ParentFieldCertificates.reverse
/-- info: 'TrustIr.SourceLayout.enum_certified_children_property' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enum_certified_children_property
/-- info: 'TrustIr.SourceLayout.EnumConstruction.field_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.field_geometry
/-- info: 'TrustIr.SourceLayout.Equation.ContextualRule.canonicalEnum_geometry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.ContextualRule.canonicalEnum_geometry
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.direct_certificates' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.direct_certificates
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.direct_contextual_rule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.direct_contextual_rule
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.parent_mismatch_certificate_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.parent_mismatch_certificate_refuses
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.declared_variant_parent_contract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.declared_variant_parent_contract

/-- info: 'TrustIr.SourceLayout.Graph.DynamicExtends.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.DynamicExtends.refl
/-- info: 'TrustIr.SourceLayout.Graph.DynamicExtends.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.DynamicExtends.trans
/-- info: 'TrustIr.SourceLayout.Graph.Extends.dynamic' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.Extends.dynamic
/-- info: 'TrustIr.SourceLayout.Graph.DynamicExtends.put_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.DynamicExtends.put_below
/-- info: 'TrustIr.SourceLayout.Equation.StorageRule.weaken' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.StorageRule.weaken
/-- info: 'TrustIr.SourceLayout.Graph.StorageInvariant.contextual' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.StorageInvariant.contextual
/-- info: 'TrustIr.SourceLayout.Graph.StorageInvariant.empty' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.StorageInvariant.empty
/-- info: 'TrustIr.SourceLayout.Graph.StorageInvariant.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.StorageInvariant.insert
/-- info: 'TrustIr.SourceLayout.Graph.StorageInvariant.allocate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.StorageInvariant.allocate
/-- info: 'TrustIr.SourceLayout.Graph.StorageInvariant.put_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.StorageInvariant.put_below
/-- info: 'TrustIr.SourceLayout.Graph.StorageInvariant.leaves' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.StorageInvariant.leaves
/-- info: 'TrustIr.SourceLayout.Equation.StorageGuarded.rule' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.StorageGuarded.rule
/-- info: 'TrustIr.SourceLayout.StorageGeometry.empty_fields' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StorageGeometry.empty_fields
/-- info: 'TrustIr.SourceLayout.ScalarSummary.storage_geometry' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ScalarSummary.storage_geometry
/-- info: 'TrustIr.SourceLayout.Equation.StorageGuarded.done' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.StorageGuarded.done
/-- info: 'TrustIr.SourceLayout.Equation.StorageGuarded.failed' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.StorageGuarded.failed
/-- info: 'TrustIr.SourceLayout.Equation.StorageGuarded.canonicalFields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.StorageGuarded.canonicalFields
/-- info: 'TrustIr.SourceLayout.Equation.StorageGuarded.declaredFields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.StorageGuarded.declaredFields
/-- info: 'TrustIr.SourceLayout.Equation.StorageGuarded.scaled' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.StorageGuarded.scaled
/-- info: 'TrustIr.SourceLayout.Equation.StorageGuarded.sequence' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.StorageGuarded.sequence
/-- info: 'TrustIr.SourceLayout.Equation.StorageGuarded.unit' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.StorageGuarded.unit
/-- info: 'TrustIr.SourceLayout.Equation.StorageRule.alias' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.StorageRule.alias
/-- info: 'TrustIr.SourceLayout.Equation.StorageRule.canonicalEnum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.StorageRule.canonicalEnum
/-- info: 'TrustIr.SourceLayout.Equation.StorageRule.descriptorEnum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.StorageRule.descriptorEnum
/-- info: 'TrustIr.SourceLayout.Graph.query_storage_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.query_storage_geometry
/-- info: 'TrustIr.SourceLayout.prepare_storage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.prepare_storage
/-- info: 'TrustIr.SourceLayout.RootCompilation.preserves_storage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.preserves_storage
/-- info: 'TrustIr.SourceLayout.Session.query_preserves_storage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.query_preserves_storage
/-- info: 'TrustIr.SourceLayout.Session.Reachable.storage_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.storage_invariant
/-- info: 'TrustIr.SourceLayout.Session.Reachable.query_storage_geometry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.query_storage_geometry
/-- info: 'TrustIr.SourceLayout.Session.Reachable.memo_storage_geometry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.memo_storage_geometry
/-- info: 'TrustIr.SourceLayout.query_storage_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_storage_geometry
/-- info: 'TrustIr.SourceLayout.query_field_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_field_geometry
/-- info: 'TrustIr.SourceLayout.query_enumeration_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_enumeration_geometry
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.shared_history_storage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.shared_history_storage
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.repeated_cached_storage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.repeated_cached_storage
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.shared_memo_storage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.shared_memo_storage
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.dynamic_result_storage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.dynamic_result_storage
/-- info: 'TrustIr.SourceLayout.EnumGeometryControls.canonical_public_storage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGeometryControls.canonical_public_storage
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.direct_public_storage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.direct_public_storage
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.niche_public_storage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.niche_public_storage
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.single_public_storage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.single_public_storage
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.untagged_public_storage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.untagged_public_storage

/-- info: 'TrustIr.SourceLayout.Equation.IndexedRule.sequence' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.IndexedRule.sequence
/-- info: 'TrustIr.SourceLayout.powerOfTwo_iff_power' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.powerOfTwo_iff_power
/-- info: 'TrustIr.SourceLayout.powerOfTwo_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.powerOfTwo_max
/-- info: 'TrustIr.SourceLayout.powerOfTwo_dvd_of_le' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.powerOfTwo_dvd_of_le
/-- info: 'TrustIr.SourceLayout.ScalarSummary.power_alignment' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ScalarSummary.power_alignment
/-- info: 'TrustIr.SourceLayout.PowerAlignment.of_finish' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PowerAlignment.of_finish
/-- info: 'TrustIr.SourceLayout.BoundedAlignment.of_finish' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.BoundedAlignment.of_finish
/-- info: 'TrustIr.SourceLayout.canonicalFields_steps_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.canonicalFields_steps_power
/-- info: 'TrustIr.SourceLayout.Equation.PowerAlignmentRule.canonicalFields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.PowerAlignmentRule.canonicalFields
/-- info: 'TrustIr.SourceLayout.Equation.PowerAlignmentRule.declaredFields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.PowerAlignmentRule.declaredFields
/-- info: 'TrustIr.SourceLayout.Equation.PowerAlignmentRule.done' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.PowerAlignmentRule.done
/-- info: 'TrustIr.SourceLayout.Equation.PowerAlignmentRule.failed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.PowerAlignmentRule.failed
/-- info: 'TrustIr.SourceLayout.Equation.PowerAlignmentRule.scaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.PowerAlignmentRule.scaled
/-- info: 'TrustIr.SourceLayout.Equation.PowerAlignmentRule.unit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.PowerAlignmentRule.unit
/-- info: 'TrustIr.SourceLayout.tag_alignment_power' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.tag_alignment_power
/-- info: 'TrustIr.SourceLayout.payload_alignment_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.payload_alignment_power
/-- info: 'TrustIr.SourceLayout.EnumConstruction.canonical_power_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.canonical_power_alignment
/-- info: 'TrustIr.SourceLayout.Equation.PowerAlignmentRule.enumeration' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.PowerAlignmentRule.enumeration
/-- info: 'TrustIr.SourceLayout.Equation.PowerAlignmentRule.sequence' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.PowerAlignmentRule.sequence
/-- info: 'TrustIr.SourceLayout.BoundedAlignment.unit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.BoundedAlignment.unit
/-- info: 'TrustIr.SourceLayout.prepare_power_alignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.prepare_power_alignment
/-- info: 'TrustIr.SourceLayout.RootCompilation.preserves_power_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.preserves_power_alignment
/-- info: 'TrustIr.SourceLayout.Session.query_preserves_power_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.query_preserves_power_alignment
/-- info: 'TrustIr.SourceLayout.Session.Reachable.power_alignment_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.power_alignment_invariant
/-- info: 'TrustIr.SourceLayout.Session.Reachable.query_power_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.query_power_alignment
/-- info: 'TrustIr.SourceLayout.Session.Reachable.memo_power_alignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.memo_power_alignment
/-- info: 'TrustIr.SourceLayout.query_power_alignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_power_alignment
/-- info: 'TrustIr.SourceLayout.query_alignment_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_alignment_nonzero
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.shared_history_power_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.shared_history_power_alignment
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.repeated_cached_power_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.repeated_cached_power_alignment
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.shared_memo_power_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.shared_memo_power_alignment
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.dynamic_result_power_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.dynamic_result_power_alignment
/-- info: 'TrustIr.SourceLayout.EnumGeometryControls.canonical_public_power_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGeometryControls.canonical_public_power_alignment
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.direct_public_power_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.direct_public_power_alignment
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.niche_public_power_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.niche_public_power_alignment
/-- info: 'TrustIr.SourceLayout.PowerAlignmentControls.forged_child_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PowerAlignmentControls.forged_child_accepts
/-- info: 'TrustIr.SourceLayout.PowerAlignmentControls.forged_child_power_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PowerAlignmentControls.forged_child_power_false
/-- info: 'TrustIr.SourceLayout.PowerAlignmentControls.forged_scaled_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PowerAlignmentControls.forged_scaled_accepts
/-- info: 'TrustIr.SourceLayout.PowerAlignmentControls.forged_scaled_multiple_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PowerAlignmentControls.forged_scaled_multiple_false
/-- info: 'TrustIr.SourceLayout.PowerAlignmentControls.never_alignment_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PowerAlignmentControls.never_alignment_absent
/-- info: 'TrustIr.SourceLayout.PowerAlignmentControls.never_power_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PowerAlignmentControls.never_power_alignment
/-- info: 'TrustIr.SourceLayout.PowerAlignmentControls.power_six_refuses' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PowerAlignmentControls.power_six_refuses
/-- info: 'TrustIr.SourceLayout.PowerAlignmentControls.power_eight_divides_sixty_four' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PowerAlignmentControls.power_eight_divides_sixty_four

/-- info: 'TrustIr.SourceLayout.FieldPowers.reverse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldPowers.reverse
/-- info: 'TrustIr.SourceLayout.normalized_alignment_power' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.normalized_alignment_power
/-- info: 'TrustIr.SourceLayout.canonicalFields_steps_field_powers' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.canonicalFields_steps_field_powers
/-- info: 'TrustIr.SourceLayout.declaredFields_steps_field_powers' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.declaredFields_steps_field_powers
/-- info: 'TrustIr.SourceLayout.Equation.Executes.canonicalFields_field_powers' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.canonicalFields_field_powers
/-- info: 'TrustIr.SourceLayout.Equation.Executes.declaredFields_field_powers' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.declaredFields_field_powers
/-- info: 'TrustIr.SourceLayout.FieldAlignmentSummary.empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldAlignmentSummary.empty
/-- info: 'TrustIr.SourceLayout.FieldAlignmentSummary.of_geometry' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldAlignmentSummary.of_geometry
/-- info: 'TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.failed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.failed
/-- info: 'TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.done' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.done
/-- info: 'TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.canonicalFields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.canonicalFields
/-- info: 'TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.declaredFields' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.declaredFields
/-- info: 'TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.scaled' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.scaled
/-- info: 'TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.sequence' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.sequence
/-- info: 'TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.unit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.unit
/-- info: 'TrustIr.SourceLayout.ScalarSummary.field_alignment' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ScalarSummary.field_alignment
/-- info: 'TrustIr.SourceLayout.Equation.PersistentRule.weaken' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.PersistentRule.weaken
/-- info: 'TrustIr.SourceLayout.Graph.PersistentInvariant.contextual' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.PersistentInvariant.contextual
/-- info: 'TrustIr.SourceLayout.Graph.PersistentInvariant.empty' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.PersistentInvariant.empty
/-- info: 'TrustIr.SourceLayout.Graph.PersistentInvariant.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.PersistentInvariant.insert
/-- info: 'TrustIr.SourceLayout.Graph.PersistentInvariant.allocate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.PersistentInvariant.allocate
/-- info: 'TrustIr.SourceLayout.Graph.PersistentInvariant.put_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.PersistentInvariant.put_below
/-- info: 'TrustIr.SourceLayout.Graph.PersistentInvariant.leaves' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.PersistentInvariant.leaves
/-- info: 'TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.rule' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.rule
/-- info: 'TrustIr.SourceLayout.Equation.FieldAlignmentRule.alias' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.FieldAlignmentRule.alias
/-- info: 'TrustIr.SourceLayout.Equation.VariantAlignmentGuarded.failed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.VariantAlignmentGuarded.failed
/-- info: 'TrustIr.SourceLayout.Equation.VariantAlignmentGuarded.canonicalFields' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.VariantAlignmentGuarded.canonicalFields
/-- info: 'TrustIr.SourceLayout.Equation.VariantAlignmentGuarded.declaredFields' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.VariantAlignmentGuarded.declaredFields
/-- info: 'TrustIr.SourceLayout.Graph.VariantAlignmentCertificates.weaken' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.VariantAlignmentCertificates.weaken
/-- info: 'TrustIr.SourceLayout.Graph.VariantAlignmentCertificates.reverse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.VariantAlignmentCertificates.reverse
/-- info: 'TrustIr.SourceLayout.Graph.VariantAlignmentCertificates.allocate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.VariantAlignmentCertificates.allocate
/-- info: 'TrustIr.SourceLayout.Graph.VariantAlignmentCertificates.dynamic_weaken' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.VariantAlignmentCertificates.dynamic_weaken
/-- info: 'TrustIr.SourceLayout.Graph.VariantAlignmentCertificates.child' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.VariantAlignmentCertificates.child
/-- info: 'TrustIr.SourceLayout.FieldPowers.translate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldPowers.translate
/-- info: 'TrustIr.SourceLayout.FieldsAligned.translate' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldsAligned.translate
/-- info: 'TrustIr.SourceLayout.variant_alignment_le_payload' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.variant_alignment_le_payload
/-- info: 'TrustIr.SourceLayout.EnumConstruction.canonical_field_alignment' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.canonical_field_alignment
/-- info: 'TrustIr.SourceLayout.EnumConstruction.descriptor_field_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.descriptor_field_alignment
/-- info: 'TrustIr.SourceLayout.Equation.FieldAlignmentRule.enumeration' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.FieldAlignmentRule.enumeration
/-- info: 'TrustIr.SourceLayout.prepare_field_alignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.prepare_field_alignment
/-- info: 'TrustIr.SourceLayout.RootCompilation.preserves_field_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.preserves_field_alignment
/-- info: 'TrustIr.SourceLayout.Session.query_preserves_field_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.query_preserves_field_alignment
/-- info: 'TrustIr.SourceLayout.Session.Reachable.field_alignment_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.field_alignment_invariant
/-- info: 'TrustIr.SourceLayout.Session.Reachable.query_field_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.query_field_alignment
/-- info: 'TrustIr.SourceLayout.Session.Reachable.memo_field_alignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.memo_field_alignment
/-- info: 'TrustIr.SourceLayout.query_field_alignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_field_alignment
/-- info: 'TrustIr.SourceLayout.query_layout_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_layout_geometry
/-- info: 'TrustIr.SourceLayout.query_positive_field_divides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_positive_field_divides
/-- info: 'TrustIr.SourceLayout.query_enum_field_divides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_enum_field_divides
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.shared_history_field_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.shared_history_field_alignment
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.repeated_cached_field_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.repeated_cached_field_alignment
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.shared_memo_field_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.shared_memo_field_alignment
/-- info: 'TrustIr.SourceLayout.AlignmentControls.packed_public_layout_geometry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.AlignmentControls.packed_public_layout_geometry
/-- info: 'TrustIr.SourceLayout.EnumGeometryControls.canonical_public_field_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGeometryControls.canonical_public_field_alignment
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.direct_public_field_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.direct_public_field_alignment
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.niche_public_field_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.niche_public_field_alignment
/-- info: 'TrustIr.SourceLayout.FieldAlignmentControls.actual_empty_child_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldAlignmentControls.actual_empty_child_query
/-- info: 'TrustIr.SourceLayout.FieldAlignmentControls.actual_empty_child_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldAlignmentControls.actual_empty_child_alignment
/-- info: 'TrustIr.SourceLayout.FieldAlignmentControls.actual_empty_child_power' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldAlignmentControls.actual_empty_child_power
/-- info: 'TrustIr.SourceLayout.FieldAlignmentControls.raw_enum_empty_shift_accepts' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldAlignmentControls.raw_enum_empty_shift_accepts
/-- info: 'TrustIr.SourceLayout.FieldAlignmentControls.raw_enum_empty_shift_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldAlignmentControls.raw_enum_empty_shift_false
/-- info: 'TrustIr.SourceLayout.FieldAlignmentControls.actual_enum_empty_shift_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldAlignmentControls.actual_enum_empty_shift_query
/-- info: 'TrustIr.SourceLayout.FieldAlignmentControls.actual_enum_empty_shift_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldAlignmentControls.actual_enum_empty_shift_alignment
/-- info: 'TrustIr.SourceLayout.FieldAlignmentControls.empty_child_cap_exception' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldAlignmentControls.empty_child_cap_exception
/-- info: 'TrustIr.SourceLayout.FieldAlignmentControls.invalid_packed_clamp_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldAlignmentControls.invalid_packed_clamp_refuses

/-- info: 'TrustIr.SourceLayout.EnumEncodingGeometry.no_enum' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumEncodingGeometry.no_enum
/-- info: 'TrustIr.SourceLayout.EnumConstruction.canonical_encoding_geometry' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.canonical_encoding_geometry
/-- info: 'TrustIr.SourceLayout.Equation.Executes.enum_encoding_geometry' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.enum_encoding_geometry
/-- info: 'TrustIr.SourceLayout.Equation.EncodingGuarded.rule' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.EncodingGuarded.rule
/-- info: 'TrustIr.SourceLayout.Equation.EncodingGuarded.enumeration' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.EncodingGuarded.enumeration
/-- info: 'TrustIr.SourceLayout.Equation.EncodingGuarded.failed' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.EncodingGuarded.failed
/-- info: 'TrustIr.SourceLayout.Equation.EncodingGuarded.done' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.EncodingGuarded.done
/-- info: 'TrustIr.SourceLayout.Equation.EncodingGuarded.canonicalFields' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.EncodingGuarded.canonicalFields
/-- info: 'TrustIr.SourceLayout.Equation.EncodingGuarded.declaredFields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.EncodingGuarded.declaredFields
/-- info: 'TrustIr.SourceLayout.Equation.EncodingGuarded.scaled' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.EncodingGuarded.scaled
/-- info: 'TrustIr.SourceLayout.Equation.EncodingGuarded.sequence' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.EncodingGuarded.sequence
/-- info: 'TrustIr.SourceLayout.Equation.EncodingGuarded.unit' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.EncodingGuarded.unit
/-- info: 'TrustIr.SourceLayout.ScalarSummary.enum_encoding_geometry' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ScalarSummary.enum_encoding_geometry
/-- info: 'TrustIr.SourceLayout.prepare_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.prepare_encoding
/-- info: 'TrustIr.SourceLayout.RootCompilation.preserves_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.preserves_encoding
/-- info: 'TrustIr.SourceLayout.Session.query_preserves_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.query_preserves_encoding
/-- info: 'TrustIr.SourceLayout.Session.Reachable.encoding_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.encoding_invariant
/-- info: 'TrustIr.SourceLayout.Session.Reachable.query_encoding_geometry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.query_encoding_geometry
/-- info: 'TrustIr.SourceLayout.Session.Reachable.memo_encoding_geometry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.memo_encoding_geometry
/-- info: 'TrustIr.SourceLayout.query_encoding_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_encoding_geometry
/-- info: 'TrustIr.SourceLayout.query_physical_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_physical_geometry
/-- info: 'TrustIr.SourceLayout.query_direct_tag_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_direct_tag_geometry
/-- info: 'TrustIr.SourceLayout.query_niche_carrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_niche_carrier
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.shared_history_encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.shared_history_encoding
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.repeated_cached_encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.repeated_cached_encoding
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.shared_memo_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.shared_memo_encoding
/-- info: 'TrustIr.SourceLayout.EnumGeometryControls.canonical_public_encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGeometryControls.canonical_public_encoding
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.direct_public_encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.direct_public_encoding
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.niche_public_encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.niche_public_encoding
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.single_public_encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.single_public_encoding
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.untagged_public_encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.untagged_public_encoding
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.wrapping_start_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.wrapping_start_accepts
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.wrapping_geometry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.wrapping_geometry
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.wrapping_sum_exceeds_mask' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.wrapping_sum_exceeds_mask
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.forged_tag_storage_valid' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.forged_tag_storage_valid
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.forged_tag_geometry_false' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.forged_tag_geometry_false

/-- info: 'TrustIr.SourceLayout.UniqueDiscriminants.snoc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.UniqueDiscriminants.snoc
/-- info: 'TrustIr.SourceLayout.UniqueDiscriminants.reverse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.UniqueDiscriminants.reverse
/-- info: 'TrustIr.SourceLayout.metadata_range_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.metadata_range_length
/-- info: 'TrustIr.SourceLayout.discriminants_go_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.discriminants_go_facts
/-- info: 'TrustIr.SourceLayout.discriminants_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.discriminants_facts
/-- info: 'TrustIr.SourceLayout.canonicalTag_fits' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.canonicalTag_fits
/-- info: 'TrustIr.SourceLayout.EnumMetadata.no_enum' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumMetadata.no_enum
/-- info: 'TrustIr.SourceLayout.numbered_metadata_length' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.numbered_metadata_length
/-- info: 'TrustIr.SourceLayout.EnumConstruction.metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumConstruction.metadata
/-- info: 'TrustIr.SourceLayout.Equation.Executes.enum_metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.enum_metadata
/-- info: 'TrustIr.SourceLayout.Equation.MetadataGuarded.rule' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.MetadataGuarded.rule
/-- info: 'TrustIr.SourceLayout.Equation.MetadataGuarded.enumeration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.MetadataGuarded.enumeration
/-- info: 'TrustIr.SourceLayout.Equation.MetadataGuarded.failed' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.MetadataGuarded.failed
/-- info: 'TrustIr.SourceLayout.Equation.MetadataGuarded.done' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.MetadataGuarded.done
/-- info: 'TrustIr.SourceLayout.Equation.MetadataGuarded.canonicalFields' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.MetadataGuarded.canonicalFields
/-- info: 'TrustIr.SourceLayout.Equation.MetadataGuarded.declaredFields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.MetadataGuarded.declaredFields
/-- info: 'TrustIr.SourceLayout.Equation.MetadataGuarded.scaled' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.MetadataGuarded.scaled
/-- info: 'TrustIr.SourceLayout.Equation.MetadataGuarded.sequence' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.MetadataGuarded.sequence
/-- info: 'TrustIr.SourceLayout.Equation.MetadataGuarded.unit' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.MetadataGuarded.unit
/-- info: 'TrustIr.SourceLayout.ScalarSummary.enum_metadata' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ScalarSummary.enum_metadata
/-- info: 'TrustIr.SourceLayout.prepare_metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.prepare_metadata
/-- info: 'TrustIr.SourceLayout.RootCompilation.preserves_metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.preserves_metadata
/-- info: 'TrustIr.SourceLayout.Session.query_preserves_metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.query_preserves_metadata
/-- info: 'TrustIr.SourceLayout.discriminants_go_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.discriminants_go_eval
/-- info: 'TrustIr.SourceLayout.discriminants_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.discriminants_eval
/-- info: 'TrustIr.SourceLayout.tagFits_eval' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.tagFits_eval
/-- info: 'TrustIr.SourceLayout.tagBits_eval' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.tagBits_eval
/-- info: 'TrustIr.SourceLayout.Session.Reachable.metadata_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.metadata_invariant
/-- info: 'TrustIr.SourceLayout.Session.Reachable.query_metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.query_metadata
/-- info: 'TrustIr.SourceLayout.Session.Reachable.memo_metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.memo_metadata
/-- info: 'TrustIr.SourceLayout.query_metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_metadata
/-- info: 'TrustIr.SourceLayout.query_layout_invariants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_layout_invariants
/-- info: 'TrustIr.SourceLayout.query_value_tag_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_value_tag_fits
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.shared_history_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.shared_history_metadata
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.repeated_cached_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.repeated_cached_metadata
/-- info: 'TrustIr.SourceLayout.ShapeModeControls.shared_memo_metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ShapeModeControls.shared_memo_metadata
/-- info: 'TrustIr.SourceLayout.EnumGeometryControls.canonical_public_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGeometryControls.canonical_public_metadata
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.direct_public_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.direct_public_metadata
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.niche_public_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.niche_public_metadata
/-- info: 'TrustIr.SourceLayout.DescriptorEnumControls.single_public_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DescriptorEnumControls.single_public_metadata
/-- info: 'TrustIr.SourceLayout.EnumMetadataControls.mixed_effective_labels' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumMetadataControls.mixed_effective_labels
/-- info: 'TrustIr.SourceLayout.EnumMetadataControls.mixed_value_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumMetadataControls.mixed_value_agreement
/-- info: 'TrustIr.SourceLayout.EnumMetadataControls.signed_tag_selected' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumMetadataControls.signed_tag_selected
/-- info: 'TrustIr.SourceLayout.EnumMetadataControls.mixed_labels_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumMetadataControls.mixed_labels_unique
/-- info: 'TrustIr.SourceLayout.EnumMetadataControls.implicit_explicit_collision_refuses' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumMetadataControls.implicit_explicit_collision_refuses
/-- info: 'TrustIr.SourceLayout.EnumMetadataControls.collision_value_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumMetadataControls.collision_value_refuses
/-- info: 'TrustIr.SourceLayout.EnumMetadataControls.exhausted_implicit_refuses' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumMetadataControls.exhausted_implicit_refuses
/-- info: 'TrustIr.SourceLayout.EnumMetadataControls.explicit_reset_after_exhaustion' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumMetadataControls.explicit_reset_after_exhaustion
/-- info: 'TrustIr.SourceLayout.EnumMetadataControls.unsigned_tag_negative_refuses' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumMetadataControls.unsigned_tag_negative_refuses
/-- info: 'TrustIr.SourceLayout.EnumMetadataControls.actual_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumMetadataControls.actual_query
/-- info: 'TrustIr.SourceLayout.EnumMetadataControls.actual_metadata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumMetadataControls.actual_metadata
/-- info: 'TrustIr.SourceLayout.EnumMetadataControls.raw_wrong_row_count_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumMetadataControls.raw_wrong_row_count_accepts
/-- info: 'TrustIr.SourceLayout.EnumMetadataControls.raw_wrong_row_metadata_false' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumMetadataControls.raw_wrong_row_metadata_false
/-- info: 'TrustIr.SourceLayout.EnumMetadataControls.raw_wrong_flag_count_accepts' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumMetadataControls.raw_wrong_flag_count_accepts
/-- info: 'TrustIr.SourceLayout.EnumMetadataControls.raw_wrong_flag_metadata_false' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumMetadataControls.raw_wrong_flag_metadata_false

/-- info: 'TrustIr.SourceLayout.uninhabitedFacts_derivation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.uninhabitedFacts_derivation

/-- info: 'TrustIr.SourceLayout.FactDerivation.sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FactDerivation.sound

/-- info: 'TrustIr.SourceLayout.uninhabitedFacts_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.uninhabitedFacts_sound

/-- info: 'TrustIr.SourceLayout.definitionGroups_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.definitionGroups_exact

/-- info: 'TrustIr.SourceLayout.definitionGroups_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.definitionGroups_member

/-- info: 'TrustIr.SourceLayout.firstPositionIndex_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.firstPositionIndex_exact

/-- info: 'TrustIr.SourceLayout.firstPositionIndex_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.firstPositionIndex_witness

/-- info: 'TrustIr.SourceLayout.positionIndex_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.positionIndex_witness

/-- info: 'TrustIr.SourceLayout.numbered_source_member' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.numbered_source_member

/-- info: 'TrustIr.SourceLayout.positionIndex_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.positionIndex_group

/-- info: 'TrustIr.SourceLayout.firstPositionIndex_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.firstPositionIndex_group

/-- info: 'TrustIr.SourceLayout.Index.structPosition_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Index.structPosition_group

/-- info: 'TrustIr.SourceLayout.Index.enumPosition_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Index.enumPosition_group

/-- info: 'TrustIr.SourceLayout.Index.recordPosition_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Index.recordPosition_group

/-- info: 'TrustIr.SourceLayout.Index.structShapePosition_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Index.structShapePosition_group

/-- info: 'TrustIr.SourceLayout.Index.enumShapePosition_group' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Index.enumShapePosition_group

/-- info: 'TrustIr.SourceLayout.Formula.allHold_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Formula.allHold_member

/-- info: 'TrustIr.SourceLayout.groupedRule_execution_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.groupedRule_execution_selected

/-- info: 'TrustIr.SourceLayout.groupedRule_shape_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.groupedRule_shape_selected

/-- info: 'TrustIr.SourceLayout.equations_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.equations_source

/-- info: 'TrustIr.SourceLayout.uninhabitedFacts_source_induction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.uninhabitedFacts_source_induction

/-- info: 'TrustIr.SourceLayout.uninhabitedFacts_source_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.uninhabitedFacts_source_witness

/-- info: 'TrustIr.Value.Initialized.not_unwritten' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.Value.Initialized.not_unwritten

/-- info: 'TrustIr.Value.Initialized.not_poison' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.Value.Initialized.not_poison

/-- info: 'TrustIr.Value.Initialized.aggregate_child' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.Value.Initialized.aggregate_child

/-- info: 'TrustIr.Value.Initialized.array_child' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.Value.Initialized.array_child

/-- info: 'TrustIr.Value.Initialized.record_child' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.Value.Initialized.record_child

/-- info: 'TrustIr.SourceValueMembership.forM_checked_member' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.forM_checked_member

/-- info: 'TrustIr.SourceValueMembership.check_never_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.check_never_refuses

/-- info: 'TrustIr.SourceValueMembership.tuple_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.tuple_checked

/-- info: 'TrustIr.SourceValueMembership.tuple_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.tuple_child

/-- info: 'TrustIr.SourceValueMembership.array_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.array_checked

/-- info: 'TrustIr.SourceValueMembership.array_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.array_child

/-- info: 'TrustIr.SourceValueMembership.tuple_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.tuple_shape

/-- info: 'TrustIr.SourceValueMembership.array_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.array_shape

/-- info: 'TrustIr.SourceValueMembership.never_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.never_empty

/-- info: 'TrustIr.SourceValueMembership.tuple_empty_of_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.tuple_empty_of_field

/-- info: 'TrustIr.SourceValueMembership.array_empty_of_element' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.array_empty_of_element

/-- info: 'TrustIr.SourceValueMembership.struct_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.struct_checked

/-- info: 'TrustIr.SourceValueMembership.struct_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.struct_child

/-- info: 'TrustIr.SourceValueMembership.record_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.record_checked

/-- info: 'TrustIr.SourceValueMembership.record_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.record_child

/-- info: 'TrustIr.SourceValueMembership.struct_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.struct_shape

/-- info: 'TrustIr.SourceValueMembership.record_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.record_shape

/-- info: 'TrustIr.SourceValueMembership.struct_empty_of_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.struct_empty_of_field

/-- info: 'TrustIr.SourceValueMembership.record_empty_of_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.record_empty_of_field

/-- info: 'TrustIr.SourceValueMembership.enum_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.enum_checked

/-- info: 'TrustIr.SourceValueMembership.enum_initialized_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.enum_initialized_payload

/-- info: 'TrustIr.SourceValueMembership.enum_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.enum_shape

/-- info: 'TrustIr.SourceValueMembership.enum_empty_of_variants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.enum_empty_of_variants

/-- info: 'TrustIr.SourceValueMembership.Controls.unwritten_never_tuple_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.Controls.unwritten_never_tuple_accepted

/-- info: 'TrustIr.SourceValueMembership.Controls.unwritten_never_tuple_not_initialized' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.Controls.unwritten_never_tuple_not_initialized

/-- info: 'TrustIr.SourceValueMembership.Controls.initialized_never_tuple_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.Controls.initialized_never_tuple_refuses

/-- info: 'TrustIr.SourceValueMembership.Controls.empty_array_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.Controls.empty_array_initialized

/-- info: 'TrustIr.SourceValueMembership.Controls.empty_array_never_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.Controls.empty_array_never_accepted

/-- info: 'TrustIr.SourceValueMembership.Controls.empty_array_is_not_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.Controls.empty_array_is_not_empty

/-- info: 'TrustIr.SourceValueMembership.Controls.uniform_unwritten_not_initialized' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceValueMembership.Controls.uniform_unwritten_not_initialized

/-- info: 'TrustIr.SourceLayout.numbered_range_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.numbered_range_lookup

/-- info: 'TrustIr.SourceLayout.numbered_lookup' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.numbered_lookup

/-- info: 'TrustIr.SourceLayout.numbered_get' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.numbered_get

/-- info: 'TrustIr.SourceLayout.numbered_member_iff_get' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.numbered_member_iff_get

/-- info: 'TrustIr.SourceLayout.numbered_position_unique' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.numbered_position_unique

/-- info: 'TrustIr.SourceLayout.numbered_position_bound' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.numbered_position_bound

/-- info: 'TrustIr.SourceLayout.SourceNodeDenotes.lookup' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SourceNodeDenotes.lookup

/-- info: 'TrustIr.SourceLayout.SourceNodeDenotes.functional' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SourceNodeDenotes.functional

/-- info: 'TrustIr.SourceLayout.SourceNodeDenotes.of_lookup' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SourceNodeDenotes.of_lookup

/-- info: 'TrustIr.SourceLayout.sourceNodeType_iff' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.sourceNodeType_iff

/-- info: 'TrustIr.SourceLayout.SourceNodeDenotes.bound' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SourceNodeDenotes.bound

/-- info: 'TrustIr.SourceLayout.Index.structBase_ofEnvironment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Index.structBase_ofEnvironment

/-- info: 'TrustIr.SourceLayout.Index.enumBase_ofEnvironment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Index.enumBase_ofEnvironment

/-- info: 'TrustIr.SourceLayout.Index.closureBase_ofEnvironment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Index.closureBase_ofEnvironment

/-- info: 'TrustIr.SourceLayout.SourceNodeDenotes.struct_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SourceNodeDenotes.struct_alias

/-- info: 'TrustIr.SourceLayout.SourceNodeDenotes.enum_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SourceNodeDenotes.enum_alias

/-- info: 'TrustIr.SourceLayout.SourceNodeDenotes.record_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SourceNodeDenotes.record_alias

/-- info: 'TrustIr.SourceLayout.SourceEquation.has_source_type' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SourceEquation.has_source_type

/-- info: 'TrustIr.SourceLayout.uninhabitedFacts_denotes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.uninhabitedFacts_denotes

/-- info: 'TrustIr.SourceLayout.uninhabitedFacts_source_type' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.uninhabitedFacts_source_type

/-- info: 'TrustIr.SourceLayout.uninhabitedFacts_source_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.uninhabitedFacts_source_bound

/-- info: 'TrustIr.SourceLayout.uninhabitedFacts_no_source_type' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.uninhabitedFacts_no_source_type

/-- info: 'TrustIr.SourceLayout.SourceNodeControls.sparse_kinds_remain_distinct' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SourceNodeControls.sparse_kinds_remain_distinct

/-- info: 'TrustIr.SourceLayout.SourceNodeControls.canonical_alias_keeps_type' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SourceNodeControls.canonical_alias_keeps_type

/-- info: 'TrustIr.SourceLayout.SourceNodeControls.actual_alias_derives_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SourceNodeControls.actual_alias_derives_flag

/-- info: 'TrustIr.SourceLayout.SourceNodeControls.actual_never_seed_derives_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SourceNodeControls.actual_never_seed_derives_flag

/-- info: 'TrustIr.SourceLayout.SourceNodeControls.actual_type_hole_has_no_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SourceNodeControls.actual_type_hole_has_no_flag

/-- info: 'TrustIr.SourceLayout.SourceNodeControls.outside_all_regions_has_no_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.SourceNodeControls.outside_all_regions_has_no_flag

/-- info: 'TrustIr.SourceLayout.inhabitFormula_capture_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.inhabitFormula_capture_sound

/-- info: 'TrustIr.SourceLayout.inhabitFormulas_capture_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.inhabitFormulas_capture_sound

/-- info: 'TrustIr.SourceLayout.source_equation_capture_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.source_equation_capture_sound

/-- info: 'TrustIr.SourceLayout.uninhabitedFacts_capture_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.uninhabitedFacts_capture_sound

/-- info: 'TrustIr.SourceLayout.source_type_uninhabited_capture_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.source_type_uninhabited_capture_empty

/-- info: 'TrustIr.SourceLayout.variant_uninhabited_capture_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.variant_uninhabited_capture_field

/-- info: 'TrustIr.SourceLayout.variant_uninhabited_no_initialized_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.variant_uninhabited_no_initialized_payload

/-- info: 'TrustIr.SourceLayout.contextOf_capture_service' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.contextOf_capture_service

/-- info: 'TrustIr.SourceLayout.contextOf_capture_source' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.contextOf_capture_source

/-- info: 'TrustIr.SourceLayout.contextOf_uninhabited_capture_empty' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.contextOf_uninhabited_capture_empty

/-- info: 'TrustIr.SourceLayout.CaptureSoundControls.actual_context_prepares' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CaptureSoundControls.actual_context_prepares

/-- info: 'TrustIr.SourceLayout.CaptureSoundControls.actual_record_keys' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CaptureSoundControls.actual_record_keys

/-- info: 'TrustIr.SourceLayout.CaptureSoundControls.actual_first_struct_resolves' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CaptureSoundControls.actual_first_struct_resolves

/-- info: 'TrustIr.SourceLayout.CaptureSoundControls.actual_canonical_position_differs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CaptureSoundControls.actual_canonical_position_differs

/-- info: 'TrustIr.SourceLayout.CaptureSoundControls.actual_alias_struct_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CaptureSoundControls.actual_alias_struct_empty

/-- info: 'TrustIr.SourceLayout.CaptureSoundControls.actual_record_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CaptureSoundControls.actual_record_empty

/-- info: 'TrustIr.SourceLayout.CaptureSoundControls.actual_enum_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CaptureSoundControls.actual_enum_empty

/-- info: 'TrustIr.SourceLayout.CaptureSoundControls.actual_array_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CaptureSoundControls.actual_array_empty

/-- info: 'TrustIr.SourceLayout.CaptureSoundControls.flagged_struct_payload_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CaptureSoundControls.flagged_struct_payload_refuses

/-- info: 'TrustIr.SourceLayout.CaptureSoundControls.skewed_context_prepares' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CaptureSoundControls.skewed_context_prepares

/-- info: 'TrustIr.SourceLayout.CaptureSoundControls.skewed_source_flag_is_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CaptureSoundControls.skewed_source_flag_is_true

/-- info: 'TrustIr.SourceLayout.CaptureSoundControls.skewed_value_is_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CaptureSoundControls.skewed_value_is_accepted

/-- info: 'TrustIr.SourceLayout.CaptureSoundControls.skewed_keys_disagree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CaptureSoundControls.skewed_keys_disagree

/-- info: 'TrustIr.SourceLayout.CaptureSoundControls.skewed_context_not_associated' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CaptureSoundControls.skewed_context_not_associated

/-- info: 'TrustIr.SourceLayout.CaptureSoundControls.skewed_type_not_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CaptureSoundControls.skewed_type_not_empty

/-- info: 'TrustIr.SourceLayout.CaptureSoundControls.unsupported_first_record_stays_missing' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CaptureSoundControls.unsupported_first_record_stays_missing

/-- info: 'TrustIr.SourceLayout.CaptureSoundControls.unsupported_first_record_keys_agree' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CaptureSoundControls.unsupported_first_record_keys_agree

/-- info: 'TrustIr.SourceLayout.CaptureSoundControls.unsupported_first_record_associated' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CaptureSoundControls.unsupported_first_record_associated

/-- info: 'TrustIr.SourceLayout.EnumTagSelects.functional' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumTagSelects.functional

/-- info: 'TrustIr.SourceLayout.enum_checked_tag_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enum_checked_tag_selection

/-- info: 'TrustIr.SourceLayout.enum_capture_active_flag_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enum_capture_active_flag_false

/-- info: 'TrustIr.SourceLayout.singleInhabitedValid_inactive_flag' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.singleInhabitedValid_inactive_flag

/-- info: 'TrustIr.SourceLayout.enum_capture_single_inhabited_active' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enum_capture_single_inhabited_active

/-- info: 'TrustIr.SourceLayout.enum_execution_position_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enum_execution_position_resolves

/-- info: 'TrustIr.SourceLayout.enum_shape_position_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enum_shape_position_resolves

/-- info: 'TrustIr.SourceLayout.enum_execution_single_inhabited_active' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enum_execution_single_inhabited_active

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.duplicate_context_prepares' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.duplicate_context_prepares

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.duplicate_capture_source' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.duplicate_capture_source

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.duplicate_evaluator_selects_first' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.duplicate_evaluator_selects_first

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.duplicate_execution_selects_second' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.duplicate_execution_selects_second

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.duplicate_shape_selects_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.duplicate_shape_selects_first

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.duplicate_selected_row' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.duplicate_selected_row

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.duplicate_layout_guard_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.duplicate_layout_guard_accepts

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.duplicate_evaluator_guard_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.duplicate_evaluator_guard_refuses

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.duplicate_inactive_value_initialized' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.duplicate_inactive_value_initialized

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.duplicate_inactive_value_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.duplicate_inactive_value_accepted

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.duplicate_lookup_agreement_fails' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.duplicate_lookup_agreement_fails

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.equal_duplicates_agree' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.equal_duplicates_agree

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.equal_duplicates_execution_resolves' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.equal_duplicates_execution_resolves

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.equal_duplicates_shape_resolves' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.equal_duplicates_shape_resolves

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.positive_context_prepares' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.positive_context_prepares

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.positive_capture_source' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.positive_capture_source

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.positive_lookup_agrees' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.positive_lookup_agrees

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.positive_selected_value_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.positive_selected_value_accepted

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.positive_selected_value_initialized' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.positive_selected_value_initialized

/-- info: 'TrustIr.SourceLayout.ActiveEnumControls.positive_guard_selects_actual_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ActiveEnumControls.positive_guard_selects_actual_payload

/-- info: 'TrustIr.SourceLayout.enumIdScan_spec' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enumIdScan_spec

/-- info: 'TrustIr.SourceLayout.enumIdsAdmitted_iff' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enumIdsAdmitted_iff

/-- info: 'TrustIr.SourceLayout.enum_lookup_agrees_of_admission' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enum_lookup_agrees_of_admission

/-- info: 'TrustIr.SourceLayout.enum_execution_active_of_admission' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enum_execution_active_of_admission

/-- info: 'TrustIr.SourceLayout.EnumAdmissionControls.empty_admitted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumAdmissionControls.empty_admitted

/-- info: 'TrustIr.SourceLayout.EnumAdmissionControls.sparse_ids_admitted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumAdmissionControls.sparse_ids_admitted

/-- info: 'TrustIr.SourceLayout.EnumAdmissionControls.sparse_permutation_admitted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumAdmissionControls.sparse_permutation_admitted

/-- info: 'TrustIr.SourceLayout.EnumAdmissionControls.identical_duplicate_refused' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumAdmissionControls.identical_duplicate_refused

/-- info: 'TrustIr.SourceLayout.EnumAdmissionControls.altered_duplicate_refused' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumAdmissionControls.altered_duplicate_refused

/-- info: 'TrustIr.SourceLayout.EnumAdmissionControls.nonadjacent_duplicate_refused' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumAdmissionControls.nonadjacent_duplicate_refused

/-- info: 'TrustIr.SourceLayout.EnumAdmissionControls.reserved_key_refused' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumAdmissionControls.reserved_key_refused

/-- info: 'TrustIr.SourceLayout.EnumAdmissionControls.other_reserved_key_admitted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumAdmissionControls.other_reserved_key_admitted

/-- info: 'TrustIr.SourceLayout.EnumAdmissionControls.sparse_rows_distinct' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumAdmissionControls.sparse_rows_distinct

/-- info: 'TrustIr.SourceLayout.EnumAdmissionControls.raw_duplicate_context_still_prepares' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumAdmissionControls.raw_duplicate_context_still_prepares

/-- info: 'TrustIr.SourceLayout.EnumAdmissionControls.raw_duplicate_context_has_no_admission' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumAdmissionControls.raw_duplicate_context_has_no_admission

/-- info: 'TrustIr.SourceLayout.EnumAdmissionControls.raw_duplicate_distinctness_impossible' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumAdmissionControls.raw_duplicate_distinctness_impossible

/-- info: 'TrustIr.SourceLayout.EnumAdmissionControls.out_of_range_refused' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumAdmissionControls.out_of_range_refused

/-- info: 'TrustIr.SourceLayout.EnumAdmissionControls.wide_out_of_range_refused' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumAdmissionControls.wide_out_of_range_refused

/-- info: 'TrustIr.SourceLayout.enumPhysicalSelection_eq_original' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enumPhysicalSelection_eq_original

/-- info: 'TrustIr.SourceLayout.enumPhysicalSelection_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enumPhysicalSelection_some

/-- info: 'TrustIr.SourceLayout.enum_physical_omission_refuses_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enum_physical_omission_refuses_initialized

/-- info: 'TrustIr.SourceLayout.enum_execution_omission_refuses_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enum_execution_omission_refuses_initialized

/-- info: 'TrustIr.SourceLayout.enum_capture_active_not_omitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.enum_capture_active_not_omitted

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.actual_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.actual_selection

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.actual_dead_omitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.actual_dead_omitted

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.actual_live_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.actual_live_retained

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.active_value_initialized' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.active_value_initialized

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.active_value_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.active_value_accepted

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.actual_capture_never_omits_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.actual_capture_never_omits_active

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.unwritten_inactive_value_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.unwritten_inactive_value_accepted

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.unwritten_inactive_not_initialized' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.unwritten_inactive_not_initialized

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.unwritten_definition_omits_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.unwritten_definition_omits_inactive

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.inactive_offset_blocks_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.inactive_offset_blocks_selection

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.selected_never_blocks_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.selected_never_blocks_selection

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.canonical_has_no_physical_skip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.canonical_has_no_physical_skip

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.duplicate_context_prepares' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.duplicate_context_prepares

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.duplicate_execution_selects_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.duplicate_execution_selects_other

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.duplicate_layout_omits_live_capture_row' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.duplicate_layout_omits_live_capture_row

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.duplicate_value_initialized' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.duplicate_value_initialized

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.duplicate_live_capture_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.duplicate_live_capture_accepted

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.duplicate_has_no_admission' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.duplicate_has_no_admission

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.initialization_hypothesis_needed' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.initialization_hypothesis_needed

/-- info: 'TrustIr.SourceLayout.PhysicalOmissionControls.nominal_admission_hypothesis_needed' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PhysicalOmissionControls.nominal_admission_hypothesis_needed

/-- info: 'TrustIr.SourceLayout.Index.node_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Index.node_injective

/-- info: 'TrustIr.SourceLayout.EnumSourceAt.above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumSourceAt.above

/-- info: 'TrustIr.SourceLayout.EnumSourceAt.other_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumSourceAt.other_slot

/-- info: 'TrustIr.SourceLayout.Equation.Executes.enum_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.enum_origin

/-- info: 'TrustIr.SourceLayout.Equation.IndexedRule.enum_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.IndexedRule.enum_origin

/-- info: 'TrustIr.SourceLayout.EnumOrigin.flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumOrigin.flags

/-- info: 'TrustIr.SourceLayout.Session.Reachable.enum_origin_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.enum_origin_invariant

/-- info: 'TrustIr.SourceLayout.Index.enum_selected_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Index.enum_selected_source

/-- info: 'TrustIr.SourceLayout.Session.CompiledRoot.enum_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.CompiledRoot.enum_selected

/-- info: 'TrustIr.SourceLayout.Session.Reachable.enum_value_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.enum_value_origin

/-- info: 'TrustIr.SourceLayout.Session.Reachable.query_enum_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.query_enum_origin

/-- info: 'TrustIr.SourceLayout.Session.Reachable.memo_enum_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.memo_enum_origin

/-- info: 'TrustIr.SourceLayout.query_enum_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_enum_origin

/-- info: 'TrustIr.SourceLayout.Session.Reachable.query_enum_flags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.query_enum_flags

/-- info: 'TrustIr.SourceLayout.Session.Reachable.query_enum_capture_active_flag_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.query_enum_capture_active_flag_false

/-- info: 'TrustIr.SourceLayout.query_enum_capture_active_flag_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.query_enum_capture_active_flag_false

/-- info: 'TrustIr.SourceLayout.EnumGraphControls.forged_flags_pass_metadata' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGraphControls.forged_flags_pass_metadata

/-- info: 'TrustIr.SourceLayout.EnumGraphControls.forged_flags_have_no_source_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGraphControls.forged_flags_have_no_source_origin

/-- info: 'TrustIr.SourceLayout.EnumGraphControls.raw_forged_graph_derives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGraphControls.raw_forged_graph_derives

/-- info: 'TrustIr.SourceLayout.EnumGraphControls.forged_graph_fails_origin_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGraphControls.forged_graph_fails_origin_invariant

/-- info: 'TrustIr.SourceLayout.EnumGraphControls.raw_forged_memo_is_returned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGraphControls.raw_forged_memo_is_returned

/-- info: 'TrustIr.SourceLayout.EnumGraphControls.forged_memo_has_no_derivation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGraphControls.forged_memo_has_no_derivation

/-- info: 'TrustIr.SourceLayout.EnumGraphControls.shape_selects_original_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGraphControls.shape_selects_original_first

/-- info: 'TrustIr.SourceLayout.EnumGraphControls.execution_selects_original_matching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGraphControls.execution_selects_original_matching

/-- info: 'TrustIr.SourceLayout.EnumGraphControls.duplicate_shape_position_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGraphControls.duplicate_shape_position_witness

/-- info: 'TrustIr.SourceLayout.EnumGraphControls.duplicate_execution_position_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumGraphControls.duplicate_execution_position_witness

/-- info: 'TrustIr.SourceLayout.prepare_enum_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.prepare_enum_origin

/-- info: 'TrustIr.SourceLayout.RootCompilation.preserves_enum_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.preserves_enum_origin

/-- info: 'TrustIr.SourceLayout.Session.query_preserves_enum_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.query_preserves_enum_origin

/-- info: 'TrustIr.SourceLayout.RootCompilation.enum_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.enum_selected

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.type' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.type

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.own' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.own

/-- info: 'TrustIr.AggregateMemory.prepare_query_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepare_query_origin

/-- info: 'TrustIr.AggregateMemory.Service.queryWithWork_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Service.queryWithWork_result

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.enum_view' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.enum_view

/-- info: 'TrustIr.AggregateMemory.VariantOrigins.live_at' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantOrigins.live_at

/-- info: 'TrustIr.AggregateMemory.VariantOrigins.absent_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantOrigins.absent_iff

/-- info: 'TrustIr.AggregateMemory.VariantOrigins.length' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantOrigins.length

/-- info: 'TrustIr.AggregateMemory.actual_summary_policy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.actual_summary_policy

/-- info: 'TrustIr.AggregateMemory.prepared_plan_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_plan_origin

/-- info: 'TrustIr.AggregateMemory.prepared_enum_plan_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_enum_plan_view

/-- info: 'TrustIr.AggregateMemory.prepared_enum_plan_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_enum_plan_source

/-- info: 'TrustIr.AggregateMemory.prepared_enum_active_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_enum_active_payload

/-- info: 'TrustIr.AggregateMemory.PlanOriginControls.live_unit_payload' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.PlanOriginControls.live_unit_payload

/-- info: 'TrustIr.AggregateMemory.PlanOriginControls.ordered_payloads' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.PlanOriginControls.ordered_payloads

/-- info: 'TrustIr.AggregateMemory.PlanOriginControls.false_flag_cannot_be_absent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.PlanOriginControls.false_flag_cannot_be_absent

/-- info: 'TrustIr.AggregateMemory.PlanOriginControls.true_flag_cannot_be_present' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.PlanOriginControls.true_flag_cannot_be_present

/-- info: 'TrustIr.AggregateMemory.PlanOriginControls.equal_lengths_do_not_authenticate_order' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.PlanOriginControls.equal_lengths_do_not_authenticate_order

/-- info: 'TrustIr.AggregateMemory.PlanOriginControls.enum_cannot_use_scalar_plan' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.PlanOriginControls.enum_cannot_use_scalar_plan

/-- info: 'TrustIr.AggregateMemory.PlanOriginControls.forged_flags_have_no_actual_summary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.PlanOriginControls.forged_flags_have_no_actual_summary

/-- info: 'TrustIr.AggregateMemory.PlanOriginControls.forged_plan_has_no_actual_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.PlanOriginControls.forged_plan_has_no_actual_origin

/-- info: 'TrustIr.SourceLayout.EnumOrigin.tag_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumOrigin.tag_data

/-- info: 'TrustIr.AggregateMemory.discriminantIndex' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.discriminantIndex

/-- info: 'TrustIr.AggregateMemory.enumTagValue' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.enumTagValue

/-- info: 'TrustIr.AggregateMemory.enumTagValue_inline' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.enumTagValue_inline

/-- info: 'TrustIr.AggregateMemory.EnumEncodingSelects' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumEncodingSelects

/-- info: 'TrustIr.AggregateMemory.EnumEncodingSelects.of_lookup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumEncodingSelects.of_lookup

/-- info: 'TrustIr.SourceLayout.canonicalTag_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.canonicalTag_eval

/-- info: 'TrustIr.AggregateMemory.enumTagValue_fitted' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.enumTagValue_fitted

/-- info: 'TrustIr.AggregateMemory.enumTagValue_residue' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.enumTagValue_residue

/-- info: 'TrustIr.AggregateMemory.discriminantIndex_residue' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.discriminantIndex_residue

/-- info: 'TrustIr.AggregateMemory.discriminantIndex_eval' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.discriminantIndex_eval

/-- info: 'TrustIr.AggregateMemory.enum_checked_tag_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.enum_checked_tag_contract

/-- info: 'TrustIr.AggregateMemory.enum_tag_integer_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.enum_tag_integer_contract

/-- info: 'TrustIr.AggregateMemory.enum_encoding_of_checked_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.enum_encoding_of_checked_selection

/-- info: 'TrustIr.AggregateMemory.prepared_enum_capture_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_enum_capture_encoding

/-- info: 'TrustIr.AggregateMemory.CodecSelectionControls.wrong_width_has_selector_witness' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.CodecSelectionControls.wrong_width_has_selector_witness

/-- info: 'TrustIr.AggregateMemory.CodecSelectionControls.wrong_width_refuses_encoding' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.CodecSelectionControls.wrong_width_refuses_encoding

/-- info: 'TrustIr.AggregateMemory.CodecSelectionControls.wrong_width_refuses_checker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.CodecSelectionControls.wrong_width_refuses_checker

/-- info: 'TrustIr.AggregateMemory.CodecSelectionControls.encoder_alone_accepts_oversized_raw' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.CodecSelectionControls.encoder_alone_accepts_oversized_raw

/-- info: 'TrustIr.AggregateMemory.CodecSelectionControls.oversized_raw_refuses_checker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.CodecSelectionControls.oversized_raw_refuses_checker

/-- info: 'TrustIr.AggregateMemory.CodecSelectionControls.oversized_raw_has_no_selector' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.CodecSelectionControls.oversized_raw_has_no_selector

/-- info: 'TrustIr.AggregateMemory.CodecSelectionControls.signed_residue_reads_negative' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.CodecSelectionControls.signed_residue_reads_negative

/-- info: 'TrustIr.AggregateMemory.CodecSelectionControls.unsigned_residue_stays_positive' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.CodecSelectionControls.unsigned_residue_stays_positive

/-- info: 'TrustIr.AggregateMemory.CodecSelectionControls.signed_128_residue_reads_negative' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.CodecSelectionControls.signed_128_residue_reads_negative

/-- info: 'TrustIr.AggregateMemory.CodecSelectionControls.nonfitting_table_breaks_residue_lookup' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.CodecSelectionControls.nonfitting_table_breaks_residue_lookup

/-- info: 'TrustIr.AggregateMemory.CodecSelectionControls.wrong_tag_has_no_source_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.CodecSelectionControls.wrong_tag_has_no_source_origin

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.enum_layout_view' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.enum_layout_view

/-- info: 'TrustIr.AggregateMemory.ByteLane' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteLane

/-- info: 'TrustIr.AggregateMemory.ImageOverwrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ImageOverwrite

/-- info: 'TrustIr.AggregateMemory.ImageOverwrite.extent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ImageOverwrite.extent

/-- info: 'TrustIr.AggregateMemory.ImageOverwrite.lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ImageOverwrite.lane

/-- info: 'TrustIr.AggregateMemory.ImageOverwrite.outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ImageOverwrite.outside

/-- info: 'TrustIr.AggregateMemory.EnumTagPrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumTagPrefix

/-- info: 'TrustIr.AggregateMemory.EnumTagPrefix.direct_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumTagPrefix.direct_lane

/-- info: 'TrustIr.AggregateMemory.EnumTagPrefix.direct_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumTagPrefix.direct_exists

/-- info: 'TrustIr.AggregateMemory.EnumTagPrefix.untagged_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumTagPrefix.untagged_index

/-- info: 'TrustIr.AggregateMemory.EnumTagPrefix.single_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumTagPrefix.single_index

/-- info: 'TrustIr.AggregateMemory.EnumTagPrefix.niche_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumTagPrefix.niche_lane

/-- info: 'TrustIr.AggregateMemory.NichePayloadChecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.NichePayloadChecked

/-- info: 'TrustIr.AggregateMemory.NichePayloadChecked.untagged_outside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.NichePayloadChecked.untagged_outside

/-- info: 'TrustIr.AggregateMemory.EnumEncodingSelects.lookup' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumEncodingSelects.lookup

/-- info: 'TrustIr.AggregateMemory.ByteLane.after_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteLane.after_write

/-- info: 'TrustIr.AggregateMemory.EnumTagPrefix.untagged_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumTagPrefix.untagged_exists

/-- info: 'TrustIr.AggregateMemory.EnumTagPrefix.single_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumTagPrefix.single_exists

/-- info: 'TrustIr.AggregateMemory.EnumTagPrefix.niche_untagged_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumTagPrefix.niche_untagged_exists

/-- info: 'TrustIr.AggregateMemory.EnumTagPrefix.niche_tagged_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumTagPrefix.niche_tagged_exists

/-- info: 'TrustIr.AggregateMemory.InitializedLane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.InitializedLane

/-- info: 'TrustIr.AggregateMemory.EnumDecodingSelects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecodingSelects

/-- info: 'TrustIr.AggregateMemory.EnumDecodingSelects.untagged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecodingSelects.untagged

/-- info: 'TrustIr.AggregateMemory.EnumDecodingSelects.single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecodingSelects.single

/-- info: 'TrustIr.AggregateMemory.EnumDecodingSelects.direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecodingSelects.direct

/-- info: 'TrustIr.AggregateMemory.EnumDecodingSelects.niche_tagged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecodingSelects.niche_tagged

/-- info: 'TrustIr.AggregateMemory.EnumDecodingSelects.niche_untagged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecodingSelects.niche_untagged

/-- info: 'TrustIr.AggregateMemory.InitializedLane.of_materialized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.InitializedLane.of_materialized

/-- info: 'TrustIr.AggregateMemory.InitializedLane.materialized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.InitializedLane.materialized

/-- info: 'TrustIr.AggregateMemory.InitializedLane.defaulted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.InitializedLane.defaulted

/-- info: 'TrustIr.AggregateMemory.image_materialized_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.image_materialized_length

/-- info: 'TrustIr.AggregateMemory.image_materialized_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.image_materialized_lookup

/-- info: 'TrustIr.AggregateMemory.ByteLane.initialized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteLane.initialized

/-- info: 'TrustIr.AggregateMemory.decode_encode_integer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decode_encode_integer

/-- info: 'TrustIr.AggregateMemory.tag_byte_capacity' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.tag_byte_capacity

/-- info: 'TrustIr.AggregateMemory.direct_prefix_decoding_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.direct_prefix_decoding_agrees

/-- info: 'TrustIr.AggregateMemory.untagged_prefix_decoding_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.untagged_prefix_decoding_agrees

/-- info: 'TrustIr.AggregateMemory.single_prefix_decoding_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.single_prefix_decoding_agrees

/-- info: 'TrustIr.AggregateMemory.niche_relative_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.niche_relative_roundtrip

/-- info: 'TrustIr.AggregateMemory.niche_prefix_decoding_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.niche_prefix_decoding_agrees

/-- info: 'TrustIr.AggregateMemory.niche_payload_decoding_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.niche_payload_decoding_agrees

/-- info: 'TrustIr.AggregateMemory.EnumPrefixSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumPrefixSound

/-- info: 'TrustIr.AggregateMemory.enum_prefix_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.enum_prefix_sound

/-- info: 'TrustIr.AggregateMemory.prepared_enum_capture_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_enum_capture_prefix

/-- info: 'TrustIr.AggregateMemory.DecoderPrefixControls.initialized_empty_slice_is_not_a_full_lane' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.DecoderPrefixControls.initialized_empty_slice_is_not_a_full_lane

/-- info: 'TrustIr.AggregateMemory.DecoderPrefixControls.empty_image_cannot_contain_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.DecoderPrefixControls.empty_image_cannot_contain_byte

/-- info: 'TrustIr.AggregateMemory.DecoderPrefixControls.overlapping_write_changes_tag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.DecoderPrefixControls.overlapping_write_changes_tag

/-- info: 'TrustIr.AggregateMemory.DecoderPrefixControls.disjoint_write_preserves_actual_tag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.DecoderPrefixControls.disjoint_write_preserves_actual_tag

/-- info: 'TrustIr.AggregateMemory.DecoderPrefixControls.niche_wraparound_reconstructs_position' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.DecoderPrefixControls.niche_wraparound_reconstructs_position

/-- info: 'TrustIr.AggregateMemory.DecoderPrefixControls.out_of_range_first_breaks_inverse' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.DecoderPrefixControls.out_of_range_first_breaks_inverse

/-- info: 'TrustIr.AggregateMemory.DecoderPrefixControls.out_of_range_relative_breaks_inverse' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.DecoderPrefixControls.out_of_range_relative_breaks_inverse

/-- info: 'TrustIr.AggregateMemory.DecoderPrefixControls.missing_carrier_can_pass_encoder_guard' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.DecoderPrefixControls.missing_carrier_can_pass_encoder_guard

/-- info: 'TrustIr.AggregateMemory.DecoderPrefixControls.missing_carrier_refuses_decoder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.DecoderPrefixControls.missing_carrier_refuses_decoder

/-- info: 'TrustIr.AggregateMemory.DecoderPrefixControls.wrong_extent_has_no_origin' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.DecoderPrefixControls.wrong_extent_has_no_origin

/-- info: 'TrustIr.AggregateMemory.DecoderPrefixControls.wrong_alignment_has_no_origin' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.DecoderPrefixControls.wrong_alignment_has_no_origin

/-- info: 'TrustIr.AggregateMemory.FieldsEncoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsEncoded

/-- info: 'TrustIr.AggregateMemory.VariantEncoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantEncoded

/-- info: 'TrustIr.AggregateMemory.FieldsEncoded.extent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsEncoded.extent

/-- info: 'TrustIr.AggregateMemory.VariantEncoded.extent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantEncoded.extent

/-- info: 'TrustIr.AggregateMemory.EnumTagPrefix.extent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumTagPrefix.extent

/-- info: 'TrustIr.AggregateMemory.encode_enumeration_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_enumeration_steps

/-- info: 'TrustIr.AggregateMemory.encode_enumeration_extent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_enumeration_extent

/-- info: 'TrustIr.AggregateMemory.encode_extent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_extent

/-- info: 'TrustIr.AggregateMemory.FieldsAvoidLane' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsAvoidLane

/-- info: 'TrustIr.AggregateMemory.FieldsEncoded.preserves_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsEncoded.preserves_lane

/-- info: 'TrustIr.AggregateMemory.VariantEncoded.fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantEncoded.fields

/-- info: 'TrustIr.AggregateMemory.VariantEncoded.preserves_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantEncoded.preserves_lane

/-- info: 'TrustIr.AggregateMemory.EnumEncodingSelects.functional' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumEncodingSelects.functional

/-- info: 'TrustIr.AggregateMemory.EnumTagPrefix.direct_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumTagPrefix.direct_tag

/-- info: 'TrustIr.AggregateMemory.EnumDecodingSelects.transfer_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecodingSelects.transfer_direct

/-- info: 'TrustIr.AggregateMemory.EnumDecodingSelects.transfer_niche' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecodingSelects.transfer_niche

/-- info: 'TrustIr.AggregateMemory.EnumPayloadAvoidsTag' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumPayloadAvoidsTag

/-- info: 'TrustIr.AggregateMemory.EnumUntaggedCarrierReady' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumUntaggedCarrierReady

/-- info: 'TrustIr.AggregateMemory.enum_encoded_selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.enum_encoded_selection

/-- info: 'TrustIr.AggregateMemory.prepared_enum_capture_encoded_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_enum_capture_encoded_selection

/-- info: 'TrustIr.AggregateMemory.EnumImageControls.overlapping_payload_changes_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumImageControls.overlapping_payload_changes_selection

/-- info: 'TrustIr.AggregateMemory.EnumImageControls.overlapping_retained_range_is_not_separated' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumImageControls.overlapping_retained_range_is_not_separated

/-- info: 'TrustIr.AggregateMemory.EnumImageControls.disjoint_payload_keeps_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumImageControls.disjoint_payload_keeps_selection

/-- info: 'TrustIr.AggregateMemory.EnumImageControls.wrong_child_extent_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumImageControls.wrong_child_extent_refuses

/-- info: 'TrustIr.AggregateMemory.EnumImageControls.wrong_payload_census_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumImageControls.wrong_payload_census_refuses

/-- info: 'TrustIr.AggregateMemory.EnumImageControls.unwritten_transport_retains_extent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumImageControls.unwritten_transport_retains_extent

/-- info: 'TrustIr.AggregateMemory.EnumImageControls.forbidden_unwritten_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumImageControls.forbidden_unwritten_refuses

/-- info: 'TrustIr.AggregateMemory.EnumImageControls.successful_encoding_does_not_imply_carrier_initialization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumImageControls.successful_encoding_does_not_imply_carrier_initialization

/-- info: 'TrustIr.AggregateMemory.EnumImageControls.reserved_default_payload_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumImageControls.reserved_default_payload_refuses

/-- info: 'TrustIr.AggregateMemory.Plan.fieldInputTypes' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.fieldInputTypes

/-- info: 'TrustIr.AggregateMemory.FieldBindings' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindings

/-- info: 'TrustIr.AggregateMemory.VariantBindings' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantBindings

/-- info: 'TrustIr.AggregateMemory.VariantBindings.nil' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantBindings.nil

/-- info: 'TrustIr.AggregateMemory.VariantBindings.omitted' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantBindings.omitted

/-- info: 'TrustIr.AggregateMemory.VariantBindings.live' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantBindings.live

/-- info: 'TrustIr.AggregateMemory.Plan.Origin' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.leaf' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.leaf

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.fields' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.fields

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.array' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.array

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.enumeration' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.enumeration

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.layout_view' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.layout_view

/-- info: 'TrustIr.AggregateMemory.FieldBindings.length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindings.length

/-- info: 'TrustIr.AggregateMemory.FieldBindings.at' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindings.at

/-- info: 'TrustIr.AggregateMemory.FieldBindings.source_at' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindings.source_at

/-- info: 'TrustIr.AggregateMemory.VariantBindings.fields_at' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantBindings.fields_at

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.enum_binding_view' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.enum_binding_view

/-- info: 'TrustIr.AggregateMemory.FieldBindings.source_child' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindings.source_child

/-- info: 'TrustIr.AggregateMemory.VariantBindings.source_at' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantBindings.source_at

/-- info: 'TrustIr.AggregateMemory.VariantOrigins.children_at' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantOrigins.children_at

/-- info: 'TrustIr.AggregateMemory.prepared_plan_query_extent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_plan_query_extent

/-- info: 'TrustIr.AggregateMemory.prepared_enum_field_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_enum_field_queries

/-- info: 'TrustIr.AggregateMemory.FieldBindingControls.same_size_wrong_type_refuses' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindingControls.same_size_wrong_type_refuses

/-- info: 'TrustIr.AggregateMemory.FieldBindingControls.wrong_offset_refuses' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindingControls.wrong_offset_refuses

/-- info: 'TrustIr.AggregateMemory.FieldBindingControls.swapped_same_size_fields_refuse' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindingControls.swapped_same_size_fields_refuse

/-- info: 'TrustIr.AggregateMemory.FieldBindingControls.missing_child_refuses' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindingControls.missing_child_refuses

/-- info: 'TrustIr.AggregateMemory.FieldBindingControls.dead_row_does_not_compile_never' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindingControls.dead_row_does_not_compile_never

/-- info: 'TrustIr.AggregateMemory.FieldBindingControls.live_row_cannot_disappear' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindingControls.live_row_cannot_disappear

/-- info: 'TrustIr.AggregateMemory.FieldBindingControls.right_type_and_offset_do_not_authenticate_size' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindingControls.right_type_and_offset_do_not_authenticate_size

/-- info: 'TrustIr.AggregateMemory.FieldBindingControls.wrong_child_alignment_refuses' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindingControls.wrong_child_alignment_refuses

/-- info: 'TrustIr.AggregateMemory.FieldBindingControls.tuple_types_follow_original_input' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindingControls.tuple_types_follow_original_input

/-- info: 'TrustIr.AggregateMemory.FieldExtents' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldExtents

/-- info: 'TrustIr.AggregateMemory.VariantExtents' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantExtents

/-- info: 'TrustIr.AggregateMemory.VariantExtents.nil' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantExtents.nil

/-- info: 'TrustIr.AggregateMemory.VariantExtents.omitted' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantExtents.omitted

/-- info: 'TrustIr.AggregateMemory.VariantExtents.live' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantExtents.live

/-- info: 'TrustIr.AggregateMemory.FieldExtents.at' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldExtents.at

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.enum_extent_view' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.enum_extent_view

/-- info: 'TrustIr.AggregateMemory.ByteLane.after_disjoint_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteLane.after_disjoint_write

/-- info: 'TrustIr.AggregateMemory.FieldBindings.avoids_lane' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindings.avoids_lane

/-- info: 'TrustIr.AggregateMemory.enum_checked_fields_avoid_tag' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.enum_checked_fields_avoid_tag

/-- info: 'TrustIr.AggregateMemory.prepared_enum_payload_avoids_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_enum_payload_avoids_tag

/-- info: 'TrustIr.AggregateMemory.prepared_enum_capture_coherent_encoded_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_enum_capture_coherent_encoded_selection

/-- info: 'TrustIr.AggregateMemory.ByteLane.compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteLane.compose

/-- info: 'TrustIr.AggregateMemory.ByteLane.materialized_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteLane.materialized_slice

/-- info: 'TrustIr.AggregateMemory.InitializedLane.after_placement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.InitializedLane.after_placement

/-- info: 'TrustIr.AggregateMemory.ImageOverwrite.initialized_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ImageOverwrite.initialized_child

/-- info: 'TrustIr.AggregateMemory.InitializedLane.byte_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.InitializedLane.byte_lane

/-- info: 'TrustIr.AggregateMemory.FieldsEncoded.preserves_initialized_lane' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsEncoded.preserves_initialized_lane

/-- info: 'TrustIr.AggregateMemory.FieldsEncoded.retains_initialized_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsEncoded.retains_initialized_child

/-- info: 'TrustIr.AggregateMemory.EnumUntaggedCarrierReady.of_retained_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumUntaggedCarrierReady.of_retained_child

/-- info: 'TrustIr.AggregateMemory.ByteCoverageControls.actual_child_placement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteCoverageControls.actual_child_placement

/-- info: 'TrustIr.AggregateMemory.ByteCoverageControls.actual_later_write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteCoverageControls.actual_later_write

/-- info: 'TrustIr.AggregateMemory.ByteCoverageControls.nested_carrier_survives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteCoverageControls.nested_carrier_survives

/-- info: 'TrustIr.AggregateMemory.ByteCoverageControls.padding_is_not_authorized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteCoverageControls.padding_is_not_authorized

/-- info: 'TrustIr.AggregateMemory.ByteCoverageControls.clipped_read_needs_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteCoverageControls.clipped_read_needs_bound

/-- info: 'TrustIr.AggregateMemory.encode_leaf_materialized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_leaf_materialized

/-- info: 'TrustIr.AggregateMemory.initialized_ofList_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.initialized_ofList_range

/-- info: 'TrustIr.AggregateMemory.encode_leaf_range_initialized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_leaf_range_initialized

/-- info: 'TrustIr.AggregateMemory.FieldsEncoded.retains_encoded_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsEncoded.retains_encoded_leaf

/-- info: 'TrustIr.AggregateMemory.EnumUntaggedCarrierReady.of_encoded_leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumUntaggedCarrierReady.of_encoded_leaf

/-- info: 'TrustIr.AggregateMemory.LeafCoverageControls.encoded_leaf_carrier_survives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.LeafCoverageControls.encoded_leaf_carrier_survives

/-- info: 'TrustIr.AggregateMemory.LeafCoverageControls.interior_byte_is_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.LeafCoverageControls.interior_byte_is_actual

/-- info: 'TrustIr.AggregateMemory.LeafCoverageControls.wrong_leaf_extent_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.LeafCoverageControls.wrong_leaf_extent_refuses

/-- info: 'TrustIr.AggregateMemory.LeafCoverageControls.ordinary_unwritten_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.LeafCoverageControls.ordinary_unwritten_refuses

/-- info: 'TrustIr.AggregateMemory.LeafCoverageControls.allowed_unwritten_does_not_initialize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.LeafCoverageControls.allowed_unwritten_does_not_initialize

/-- info: 'TrustIr.AggregateMemory.FieldsEncoded.nil_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsEncoded.nil_iff

/-- info: 'TrustIr.AggregateMemory.FieldsEncoded.cons_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsEncoded.cons_iff

/-- info: 'TrustIr.AggregateMemory.FieldsEncoded.head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsEncoded.head

/-- info: 'TrustIr.AggregateMemory.FieldsEncoded.length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsEncoded.length

/-- info: 'TrustIr.AggregateMemory.FieldsEncoded.at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsEncoded.at

/-- info: 'TrustIr.AggregateMemory.encode_fields_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_fields_steps

/-- info: 'TrustIr.AggregateMemory.Plan.CoversLane' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.CoversLane

/-- info: 'TrustIr.AggregateMemory.Plan.CoversLane.leaf' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.CoversLane.leaf

/-- info: 'TrustIr.AggregateMemory.Plan.CoversLane.fields' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.CoversLane.fields

/-- info: 'TrustIr.AggregateMemory.Plan.CoversLane.bounds' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.CoversLane.bounds

/-- info: 'TrustIr.AggregateMemory.Plan.CoversLane.initialized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.CoversLane.initialized

/-- info: 'TrustIr.AggregateMemory.FieldsEncoded.covered_at_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsEncoded.covered_at_initialized

/-- info: 'TrustIr.AggregateMemory.EnumUntaggedCarrierReady.of_covered_field_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumUntaggedCarrierReady.of_covered_field_run

/-- info: 'TrustIr.AggregateMemory.enum_encoded_covered_carrier_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.enum_encoded_covered_carrier_ready

/-- info: 'TrustIr.AggregateMemory.prepared_enum_capture_covered_encoded_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_enum_capture_covered_encoded_selection

/-- info: 'TrustIr.AggregateMemory.FieldStepControls.nested_coverage_path' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldStepControls.nested_coverage_path

/-- info: 'TrustIr.AggregateMemory.FieldStepControls.actual_nested_encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldStepControls.actual_nested_encoding

/-- info: 'TrustIr.AggregateMemory.FieldStepControls.actual_full_field_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldStepControls.actual_full_field_run

/-- info: 'TrustIr.AggregateMemory.FieldStepControls.nested_read_from_actual_encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldStepControls.nested_read_from_actual_encoding

/-- info: 'TrustIr.AggregateMemory.FieldStepControls.adjacent_padding_has_no_coverage_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldStepControls.adjacent_padding_has_no_coverage_path

/-- info: 'TrustIr.AggregateMemory.FieldStepControls.selected_middle_field_coverage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldStepControls.selected_middle_field_coverage

/-- info: 'TrustIr.AggregateMemory.FieldStepControls.unwritten_step_retains_shifted_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldStepControls.unwritten_step_retains_shifted_metadata

/-- info: 'TrustIr.AggregateMemory.FieldStepControls.extra_values_refuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldStepControls.extra_values_refuse

/-- info: 'TrustIr.AggregateMemory.FieldStepControls.missing_values_refuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldStepControls.missing_values_refuse

/-- info: 'TrustIr.SourceLayout.Field.Separated.subrange' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Field.Separated.subrange

/-- info: 'TrustIr.SourceLayout.FieldsSeparated.later_at' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldsSeparated.later_at

/-- info: 'TrustIr.AggregateMemory.FieldBindings.drop_metadata' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindings.drop_metadata

/-- info: 'TrustIr.AggregateMemory.FieldExtents.drop_metadata' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldExtents.drop_metadata

/-- info: 'TrustIr.AggregateMemory.FieldBindings.later_avoids_subrange' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindings.later_avoids_subrange

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.fields_metadata_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.fields_metadata_view

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.covers_fields_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.covers_fields_child

/-- info: 'TrustIr.AggregateMemory.Plan.LanePath' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.LanePath

/-- info: 'TrustIr.AggregateMemory.Plan.LanePath.leaf' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.LanePath.leaf

/-- info: 'TrustIr.AggregateMemory.Plan.LanePath.fields' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.LanePath.fields

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.lane_path_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.lane_path_covers

/-- info: 'TrustIr.AggregateMemory.prepared_lane_path_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_lane_path_covers

/-- info: 'TrustIr.AggregateMemory.prepared_enum_field_siblings_avoid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_enum_field_siblings_avoid

/-- info: 'TrustIr.AggregateMemory.prepared_enum_capture_path_encoded_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_enum_capture_path_encoded_selection

/-- info: 'TrustIr.AggregateMemory.SiblingGeometryControls.checked_row_separated' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SiblingGeometryControls.checked_row_separated

/-- info: 'TrustIr.AggregateMemory.SiblingGeometryControls.actual_siblings_avoid_interior_lane' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SiblingGeometryControls.actual_siblings_avoid_interior_lane

/-- info: 'TrustIr.AggregateMemory.SiblingGeometryControls.path_needs_no_parent_layout_premises' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SiblingGeometryControls.path_needs_no_parent_layout_premises

/-- info: 'TrustIr.AggregateMemory.SiblingGeometryControls.nonempty_overlap_refuses_separation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SiblingGeometryControls.nonempty_overlap_refuses_separation

/-- info: 'TrustIr.AggregateMemory.SiblingGeometryControls.type_and_offset_do_not_replace_extent_check' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SiblingGeometryControls.type_and_offset_do_not_replace_extent_check

/-- info: 'TrustIr.AggregateMemory.SiblingGeometryControls.empty_selected_subrange_is_disjoint' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SiblingGeometryControls.empty_selected_subrange_is_disjoint

/-- info: 'TrustIr.AggregateMemory.ArrayImageEncoded.preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayImageEncoded.preserves

/-- info: 'TrustIr.AggregateMemory.encode_array_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_array_steps

/-- info: 'TrustIr.ByteImage.FullyInitialized.empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.FullyInitialized.empty

/-- info: 'TrustIr.ByteImage.FullyInitialized.append' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.FullyInitialized.append

/-- info: 'TrustIr.ByteImage.FullyInitialized.tile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.FullyInitialized.tile

/-- info: 'TrustIr.AggregateMemory.encode_leaf_fully_initialized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_leaf_fully_initialized

/-- info: 'TrustIr.AggregateMemory.encode_array_fully_initialized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_array_fully_initialized

/-- info: 'TrustIr.AggregateMemory.Plan.LeafArrays.fully_initialized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.LeafArrays.fully_initialized

/-- info: 'TrustIr.AggregateMemory.fully_initialized_padding_refusal' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.fully_initialized_padding_refusal

/-- info: 'TrustIr.AggregateMemory.fully_initialized_empty_tile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.fully_initialized_empty_tile

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.array_type' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.array_type

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.array_view' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.array_view

/-- info: 'TrustIr.AggregateMemory.prepared_array_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_array_identity

/-- info: 'TrustIr.AggregateMemory.prepared_array_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_array_count

/-- info: 'TrustIr.AggregateMemory.prepared_array_encoded_census' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_array_encoded_census

/-- info: 'TrustIr.AggregateMemory.prepared_scalar_array_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_scalar_array_refusal

/-- info: 'TrustIr.AggregateMemory.prepared_wrong_array_count_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_wrong_array_count_refusal

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.array_binding_view' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.array_binding_view

/-- info: 'TrustIr.AggregateMemory.QueryOriginPolicy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.QueryOriginPolicy

/-- info: 'TrustIr.AggregateMemory.QueryOriginPolicy.query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.QueryOriginPolicy.query

/-- info: 'TrustIr.AggregateMemory.QueryOriginPolicy.resolve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.QueryOriginPolicy.resolve

/-- info: 'TrustIr.AggregateMemory.SourceElement' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceElement

/-- info: 'TrustIr.AggregateMemory.SourceElement.row' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceElement.row

/-- info: 'TrustIr.AggregateMemory.SourceElement.functional' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceElement.functional

/-- info: 'TrustIr.AggregateMemory.prepared_array_element_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_array_element_binding

/-- info: 'TrustIr.AggregateMemory.prepared_array_element_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_array_element_query

/-- info: 'TrustIr.AggregateMemory.prepared_wrong_element_refusal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_wrong_element_refusal

/-- info: 'TrustIr.AggregateMemory.prepared_array_context_element' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_array_context_element

/-- info: 'TrustIr.AggregateMemory.source_element_signed_byte_refusal' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.source_element_signed_byte_refusal

/-- info: 'TrustIr.AggregateMemory.source_element_missing_refusal' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.source_element_missing_refusal

/-- info: 'TrustIr.AggregateMemory.Plan.LeafType' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.LeafType

/-- info: 'TrustIr.AggregateMemory.Plan.FieldsType' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.FieldsType

/-- info: 'TrustIr.AggregateMemory.Plan.LeafType.not_fields' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.LeafType.not_fields

/-- info: 'TrustIr.AggregateMemory.Plan.SourceShape' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.SourceShape

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.source_shape' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.source_shape

/-- info: 'TrustIr.AggregateMemory.prepared_plan_source_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_plan_source_shape

/-- info: 'TrustIr.AggregateMemory.prepared_array_source_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_array_source_view

/-- info: 'TrustIr.AggregateMemory.prepared_source_array_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_source_array_encoding

/-- info: 'TrustIr.AggregateMemory.source_array_leaf_refusal' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.source_array_leaf_refusal

/-- info: 'TrustIr.AggregateMemory.source_scalar_fields_refusal' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.source_scalar_fields_refusal

/-- info: 'TrustIr.AggregateMemory.empty_tuple_field_shape' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.empty_tuple_field_shape

/-- info: 'TrustIr.AggregateMemory.source_empty_tuple_leaf_refusal' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.source_empty_tuple_leaf_refusal

/-- info: 'TrustIr.ByteImage.StridedInitialized' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ByteImage.StridedInitialized

/-- info: 'TrustIr.ByteImage.StridedInitialized.empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.StridedInitialized.empty

/-- info: 'TrustIr.ByteImage.StridedInitialized.append' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.StridedInitialized.append

/-- info: 'TrustIr.ByteImage.StridedInitialized.tile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.StridedInitialized.tile

/-- info: 'TrustIr.AggregateMemory.InitializedLane.present' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.InitializedLane.present

/-- info: 'TrustIr.AggregateMemory.initialized_of_present' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.initialized_of_present

/-- info: 'TrustIr.AggregateMemory.InitializedLane.strided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.InitializedLane.strided

/-- info: 'TrustIr.AggregateMemory.strided_initialized_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.strided_initialized_window

/-- info: 'TrustIr.AggregateMemory.encode_array_strided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_array_strided

/-- info: 'TrustIr.AggregateMemory.encode_array_initialized_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_array_initialized_slot

/-- info: 'TrustIr.AggregateMemory.Plan.CoversLane.array' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.CoversLane.array

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.element_lane' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.element_lane

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.nested_array_field_path' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.nested_array_field_path

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.uniform_retains_lane_and_padding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.uniform_retains_lane_and_padding

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.dense_retains_lane_and_padding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.dense_retains_lane_and_padding

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.split_retains_lane_and_padding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.split_retains_lane_and_padding

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.shifted_periodic_retains_lane_and_padding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.shifted_periodic_retains_lane_and_padding

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.periodic_hidden_poison_not_forced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.periodic_hidden_poison_not_forced

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.visible_unwritten_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.visible_unwritten_refuses

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.empty_array_has_no_coverage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.empty_array_has_no_coverage

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.zero_stride_empty_lane' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.zero_stride_empty_lane

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.misaligned_repeat_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.misaligned_repeat_refuses

/-- info: 'TrustIr.SourceLayout.NodeDerivation.functional' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.functional

/-- info: 'TrustIr.SourceLayout.StepsDerivation.functional' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StepsDerivation.functional

/-- info: 'TrustIr.SourceLayout.Equation.Executes.functional' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.functional

/-- info: 'TrustIr.SourceLayout.NodeDerivation.unique_after_growth' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.unique_after_growth

/-- info: 'TrustIr.SourceLayout.Equation.Executes.scaled_extent' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.scaled_extent

/-- info: 'TrustIr.SourceLayout.Equation.Executes.scaled_prior_child' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.scaled_prior_child

/-- info: 'TrustIr.SourceLayout.Session.QueryChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.QueryChain

/-- info: 'TrustIr.SourceLayout.Session.QueryChain.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.QueryChain.refl

/-- info: 'TrustIr.SourceLayout.Session.QueryChain.queried' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.QueryChain.queried

/-- info: 'TrustIr.SourceLayout.Session.QueryChain.reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.QueryChain.reachable

/-- info: 'TrustIr.SourceLayout.Session.QueryChain.graph_extends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.QueryChain.graph_extends

/-- info: 'TrustIr.SourceLayout.Session.QueryChain.memo_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.QueryChain.memo_agrees

/-- info: 'TrustIr.SourceLayout.Session.QueryChain.query_agrees_with_prior_memo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.QueryChain.query_agrees_with_prior_memo

/-- info: 'TrustIr.SourceLayout.DeterminismControls.actual_forward_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DeterminismControls.actual_forward_query

/-- info: 'TrustIr.SourceLayout.DeterminismControls.actual_cycle_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DeterminismControls.actual_cycle_refuses

/-- info: 'TrustIr.SourceLayout.DeterminismControls.actual_ordered_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DeterminismControls.actual_ordered_query

/-- info: 'TrustIr.SourceLayout.DeterminismControls.ordered_result_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DeterminismControls.ordered_result_unique

/-- info: 'TrustIr.SourceLayout.DeterminismControls.unrelated_graph_growth_preserves_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DeterminismControls.unrelated_graph_growth_preserves_query

/-- info: 'TrustIr.SourceLayout.DeterminismControls.rewritten_equation_is_not_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DeterminismControls.rewritten_equation_is_not_growth

/-- info: 'TrustIr.SourceLayout.DeterminismControls.forged_cache_returns_wrong_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DeterminismControls.forged_cache_returns_wrong_result

/-- info: 'TrustIr.SourceLayout.DeterminismControls.forged_cache_is_invalid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DeterminismControls.forged_cache_is_invalid

/-- info: 'TrustIr.SourceLayout.DeterminismControls.actual_source_query_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DeterminismControls.actual_source_query_chain

/-- info: 'TrustIr.SourceLayout.DeterminismControls.actual_repeat_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DeterminismControls.actual_repeat_result

/-- info: 'TrustIr.SourceLayout.DeterminismControls.actual_scaled_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DeterminismControls.actual_scaled_product

/-- info: 'TrustIr.SourceLayout.DeterminismControls.actual_zero_count_product' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DeterminismControls.actual_zero_count_product

/-- info: 'TrustIr.SourceLayout.DeterminismControls.actual_seed_memo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DeterminismControls.actual_seed_memo

/-- info: 'TrustIr.SourceLayout.DeterminismControls.actual_typed_query_prior_memo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.DeterminismControls.actual_typed_query_prior_memo

/-- info: 'TrustIr.SourceLayout.RootCompilation.array_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.array_equation

/-- info: 'TrustIr.SourceLayout.RootCompilation.array_scaled_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.array_scaled_execution

/-- info: 'TrustIr.SourceLayout.Session.CompiledRoot.array_scaled_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.CompiledRoot.array_scaled_execution

/-- info: 'TrustIr.SourceLayout.Session.Reachable.query_array_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.query_array_child

/-- info: 'TrustIr.SourceLayout.Session.Reachable.query_array_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.query_array_geometry

/-- info: 'TrustIr.SourceLayout.Session.Reachable.query_array_prior_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.query_array_prior_child

/-- info: 'TrustIr.SourceLayout.Session.QueryChain.array_count_scaling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.QueryChain.array_count_scaling

/-- info: 'TrustIr.SourceLayout.ArrayOriginControls.actual_array_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ArrayOriginControls.actual_array_query

/-- info: 'TrustIr.SourceLayout.ArrayOriginControls.actual_shape_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ArrayOriginControls.actual_shape_query

/-- info: 'TrustIr.SourceLayout.ArrayOriginControls.actual_cached_array_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ArrayOriginControls.actual_cached_array_query

/-- info: 'TrustIr.SourceLayout.ArrayOriginControls.actual_child_memo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ArrayOriginControls.actual_child_memo

/-- info: 'TrustIr.SourceLayout.ArrayOriginControls.actual_prior_child_any_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ArrayOriginControls.actual_prior_child_any_count

/-- info: 'TrustIr.SourceLayout.ArrayOriginControls.actual_interleaved_scaling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ArrayOriginControls.actual_interleaved_scaling

/-- info: 'TrustIr.SourceLayout.ArrayOriginControls.actual_zero_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ArrayOriginControls.actual_zero_count

/-- info: 'TrustIr.SourceLayout.ArrayOriginControls.actual_zero_stride' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ArrayOriginControls.actual_zero_stride

/-- info: 'TrustIr.SourceLayout.ArrayOriginControls.actual_missing_type_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ArrayOriginControls.actual_missing_type_refuses

/-- info: 'TrustIr.SourceLayout.ArrayOriginControls.actual_overflow_count_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ArrayOriginControls.actual_overflow_count_refuses

/-- info: 'TrustIr.SourceLayout.ArrayOriginControls.actual_noncanonical_target_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ArrayOriginControls.actual_noncanonical_target_refuses

/-- info: 'TrustIr.SourceLayout.StepsIn' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StepsIn

/-- info: 'TrustIr.SourceLayout.Graph.ClosedRegion' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.ClosedRegion

/-- info: 'TrustIr.SourceLayout.NodeDerivation.restrict_region' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.restrict_region

/-- info: 'TrustIr.SourceLayout.NodeDerivation.closed_region_agrees' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.closed_region_agrees

/-- info: 'TrustIr.SourceLayout.Session.Reachable.prepared_region_derivation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.prepared_region_derivation

/-- info: 'TrustIr.SourceLayout.Session.Reachable.forked_region_memo_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.forked_region_memo_agrees

/-- info: 'TrustIr.SourceLayout.Session.Reachable.forked_array_scaling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.forked_array_scaling

/-- info: 'TrustIr.SourceLayout.ClosedRegionControls.actual_prepared_scalar_region' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosedRegionControls.actual_prepared_scalar_region

/-- info: 'TrustIr.SourceLayout.ClosedRegionControls.actual_forked_arrays' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosedRegionControls.actual_forked_arrays

/-- info: 'TrustIr.SourceLayout.ClosedRegionControls.actual_forks_not_extensions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosedRegionControls.actual_forks_not_extensions

/-- info: 'TrustIr.SourceLayout.ClosedRegionControls.actual_prepared_array_region' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosedRegionControls.actual_prepared_array_region

/-- info: 'TrustIr.SourceLayout.ClosedRegionControls.actual_forked_nested_arrays' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosedRegionControls.actual_forked_nested_arrays

/-- info: 'TrustIr.SourceLayout.ClosedRegionControls.missing_dependency_can_be_added' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosedRegionControls.missing_dependency_can_be_added

/-- info: 'TrustIr.SourceLayout.ClosedRegionControls.original_missing_dependency_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosedRegionControls.original_missing_dependency_refuses

/-- info: 'TrustIr.SourceLayout.ClosedRegionControls.extension_fills_dependency' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosedRegionControls.extension_fills_dependency

/-- info: 'TrustIr.SourceLayout.ClosedRegionControls.original_has_no_derivation' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosedRegionControls.original_has_no_derivation

/-- info: 'TrustIr.SourceLayout.ClosedRegionControls.open_region_is_not_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosedRegionControls.open_region_is_not_closed

/-- info: 'TrustIr.SourceLayout.ClosedRegionControls.cycle_is_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosedRegionControls.cycle_is_closed

/-- info: 'TrustIr.SourceLayout.ClosedRegionControls.closed_cycle_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosedRegionControls.closed_cycle_refuses

/-- info: 'TrustIr.SourceLayout.TypesCompilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypesCompilation

/-- info: 'TrustIr.SourceLayout.TypesCompilation.roots_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypesCompilation.roots_bound

/-- info: 'TrustIr.SourceLayout.RootCompilation.root_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.root_bound

/-- info: 'TrustIr.SourceLayout.Session.Reachable.compiled_root_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.compiled_root_bound

/-- info: 'TrustIr.SourceLayout.Session.Reachable.compiled_types_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.compiled_types_bounds

/-- info: 'TrustIr.SourceLayout.RootFrontierControls.actual_nested_vector_compilation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootFrontierControls.actual_nested_vector_compilation

/-- info: 'TrustIr.SourceLayout.RootFrontierControls.actual_nested_vector_root_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootFrontierControls.actual_nested_vector_root_bound

/-- info: 'TrustIr.SourceLayout.RootFrontierControls.actual_repeated_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootFrontierControls.actual_repeated_children

/-- info: 'TrustIr.SourceLayout.RootFrontierControls.actual_repeated_children_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootFrontierControls.actual_repeated_children_bounded

/-- info: 'TrustIr.SourceLayout.RootFrontierControls.actual_scalar_cache_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootFrontierControls.actual_scalar_cache_hit

/-- info: 'TrustIr.SourceLayout.RootFrontierControls.actual_cached_root_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootFrontierControls.actual_cached_root_bound

/-- info: 'TrustIr.SourceLayout.RootFrontierControls.actual_nominal_execution_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootFrontierControls.actual_nominal_execution_root

/-- info: 'TrustIr.SourceLayout.RootFrontierControls.actual_nominal_shape_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootFrontierControls.actual_nominal_shape_root

/-- info: 'TrustIr.SourceLayout.RootFrontierControls.actual_nominal_both_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootFrontierControls.actual_nominal_both_bounded

/-- info: 'TrustIr.SourceLayout.RootFrontierControls.bounded_nominal_root_can_be_absent' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootFrontierControls.bounded_nominal_root_can_be_absent

/-- info: 'TrustIr.SourceLayout.RootFrontierControls.actual_refinement_shape_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootFrontierControls.actual_refinement_shape_root

/-- info: 'TrustIr.SourceLayout.RootFrontierControls.actual_closure_shape_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootFrontierControls.actual_closure_shape_root

/-- info: 'TrustIr.SourceLayout.RootFrontierControls.actual_checked_failure_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootFrontierControls.actual_checked_failure_root

/-- info: 'TrustIr.SourceLayout.RootFrontierControls.actual_failure_root_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootFrontierControls.actual_failure_root_bounded

/-- info: 'TrustIr.SourceLayout.RootFrontierControls.forged_cache_returns_outside_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootFrontierControls.forged_cache_returns_outside_root

/-- info: 'TrustIr.SourceLayout.RootFrontierControls.forged_cache_breaks_scalar_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootFrontierControls.forged_cache_breaks_scalar_invariant

/-- info: 'TrustIr.SourceLayout.Graph.ReferenceBounds' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.ReferenceBounds

/-- info: 'TrustIr.SourceLayout.Graph.Complete' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.Complete

/-- info: 'TrustIr.SourceLayout.StepsIn.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StepsIn.mono

/-- info: 'TrustIr.SourceLayout.StepsIn.append' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StepsIn.append

/-- info: 'TrustIr.SourceLayout.StepsIn.children' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StepsIn.children

/-- info: 'TrustIr.SourceLayout.Equation.references_done' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.references_done

/-- info: 'TrustIr.SourceLayout.Equation.references_alias' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.references_alias

/-- info: 'TrustIr.SourceLayout.Equation.references_scaled' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.references_scaled

/-- info: 'TrustIr.SourceLayout.Equation.references_canonicalFields' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.references_canonicalFields

/-- info: 'TrustIr.SourceLayout.Equation.references_declaredFields' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.references_declaredFields

/-- info: 'TrustIr.SourceLayout.Equation.references_enum' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.references_enum

/-- info: 'TrustIr.SourceLayout.Equation.references_sequence' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.references_sequence

/-- info: 'TrustIr.SourceLayout.Equation.references_canonicalZip' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.references_canonicalZip

/-- info: 'TrustIr.SourceLayout.Equation.references_declaredZip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.references_declaredZip

/-- info: 'TrustIr.SourceLayout.Equation.references_declaredMapZip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.references_declaredMapZip

/-- info: 'TrustIr.SourceLayout.Graph.ReferenceBounds.empty' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.ReferenceBounds.empty

/-- info: 'TrustIr.SourceLayout.Graph.ReferenceBounds.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.ReferenceBounds.insert

/-- info: 'TrustIr.SourceLayout.Graph.closed_prefix' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.closed_prefix

/-- info: 'TrustIr.SourceLayout.RootCompilation.preserves_references' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.preserves_references

/-- info: 'TrustIr.SourceLayout.TypesCompilation.preserves_references' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypesCompilation.preserves_references

/-- info: 'TrustIr.SourceLayout.StructCompilation.references' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StructCompilation.references

/-- info: 'TrustIr.SourceLayout.ClosureCompilation.references' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ClosureCompilation.references

/-- info: 'TrustIr.SourceLayout.Session.Reachable.query_reference_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.query_reference_bounds

/-- info: 'TrustIr.SourceLayout.Session.QueryChain.reference_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.QueryChain.reference_bounds

/-- info: 'TrustIr.SourceLayout.ReferenceControls.actual_prepared_graph' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ReferenceControls.actual_prepared_graph

/-- info: 'TrustIr.SourceLayout.ReferenceControls.actual_prepared_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ReferenceControls.actual_prepared_references

/-- info: 'TrustIr.SourceLayout.ReferenceControls.actual_array_query_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ReferenceControls.actual_array_query_references

/-- info: 'TrustIr.SourceLayout.ReferenceControls.actual_cached_query_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ReferenceControls.actual_cached_query_references

/-- info: 'TrustIr.SourceLayout.ReferenceControls.actual_nested_vector_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ReferenceControls.actual_nested_vector_references

/-- info: 'TrustIr.SourceLayout.ReferenceControls.actual_struct_construction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ReferenceControls.actual_struct_construction

/-- info: 'TrustIr.SourceLayout.ReferenceControls.actual_struct_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ReferenceControls.actual_struct_references

/-- info: 'TrustIr.SourceLayout.ReferenceControls.actual_closure_construction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ReferenceControls.actual_closure_construction

/-- info: 'TrustIr.SourceLayout.ReferenceControls.actual_closure_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ReferenceControls.actual_closure_references

/-- info: 'TrustIr.SourceLayout.ReferenceControls.complete_does_not_bound_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ReferenceControls.complete_does_not_bound_references

/-- info: 'TrustIr.SourceLayout.ReferenceControls.outside_reference_is_rejected' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ReferenceControls.outside_reference_is_rejected

/-- info: 'TrustIr.SourceLayout.ReferenceControls.bounds_do_not_install_equations' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ReferenceControls.bounds_do_not_install_equations

/-- info: 'TrustIr.SourceLayout.ReferenceControls.empty_reserved_prefix_is_incomplete' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ReferenceControls.empty_reserved_prefix_is_incomplete

/-- info: 'TrustIr.SourceLayout.ReferenceControls.cycle_references_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ReferenceControls.cycle_references_bounded

/-- info: 'TrustIr.SourceLayout.ReferenceControls.cycle_prefix_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ReferenceControls.cycle_prefix_complete

/-- info: 'TrustIr.SourceLayout.ReferenceControls.cycle_closed_without_termination' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.ReferenceControls.cycle_closed_without_termination

/-- info: 'TrustIr.SourceLayout.Equation.references_variantFields' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.references_variantFields

/-- info: 'TrustIr.SourceLayout.EnumNodesCompilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumNodesCompilation

/-- info: 'TrustIr.SourceLayout.EnumNodesCompilation.references' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.EnumNodesCompilation.references

/-- info: 'TrustIr.SourceLayout.prepare_references' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.prepare_references

/-- info: 'TrustIr.SourceLayout.Session.Reachable.reference_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.reference_invariant

/-- info: 'TrustIr.SourceLayout.Session.Reachable.query_reference_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.query_reference_invariant

/-- info: 'TrustIr.SourceLayout.prepared_closed_if_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.prepared_closed_if_complete

/-- info: 'TrustIr.SourceLayout.Session.Reachable.restrict_prepared_if_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.restrict_prepared_if_complete

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.physical_never_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.physical_never_children

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.logical_never_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.logical_never_children

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.physical_and_logical_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.physical_and_logical_references

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.ordinary_execution_never_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.ordinary_execution_never_refuses

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.refused_execution_never_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.refused_execution_never_references

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.refused_field_still_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.refused_field_still_bounded

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.refused_field_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.refused_field_references

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.actual_enum_extent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.actual_enum_extent

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.actual_enum_prepared_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.actual_enum_prepared_references

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.missing_tuple_validator_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.missing_tuple_validator_refuses

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.missing_closure_validator_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.missing_closure_validator_refuses

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.refusing_validators_still_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.refusing_validators_still_bounded

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.source_cycle_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.source_cycle_refuses

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.source_cycle_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.source_cycle_references

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.forward_array_extent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.forward_array_extent

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.forward_query_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.forward_query_references

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.forward_cached_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.forward_cached_references

/-- info: 'TrustIr.SourceLayout.Graph.Present' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.Present

/-- info: 'TrustIr.SourceLayout.Graph.DomainCovers' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.DomainCovers

/-- info: 'TrustIr.SourceLayout.Graph.DomainCovers.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.DomainCovers.refl

/-- info: 'TrustIr.SourceLayout.Graph.DomainCovers.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.DomainCovers.trans

/-- info: 'TrustIr.SourceLayout.Graph.present_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.present_insert

/-- info: 'TrustIr.SourceLayout.Graph.DomainCovers.write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.DomainCovers.write

/-- info: 'TrustIr.SourceLayout.Graph.DomainCovers.allocate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.DomainCovers.allocate

/-- info: 'TrustIr.SourceLayout.Graph.DomainCovers.complete_with_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.DomainCovers.complete_with_reserved

/-- info: 'TrustIr.SourceLayout.Graph.DomainCovers.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.DomainCovers.complete

/-- info: 'TrustIr.SourceLayout.CoversGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CoversGraph

/-- info: 'TrustIr.SourceLayout.CoversGraph.pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CoversGraph.pure

/-- info: 'TrustIr.SourceLayout.CoversGraph.get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CoversGraph.get

/-- info: 'TrustIr.SourceLayout.CoversGraph.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CoversGraph.bind

/-- info: 'TrustIr.SourceLayout.CoversGraph.forIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CoversGraph.forIn

/-- info: 'TrustIr.SourceLayout.Installs' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Installs

/-- info: 'TrustIr.SourceLayout.Installs.bind_left' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Installs.bind_left

/-- info: 'TrustIr.SourceLayout.Installs.bind_right' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Installs.bind_right

/-- info: 'TrustIr.SourceLayout.Installs.forIn_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Installs.forIn_member

/-- info: 'TrustIr.SourceLayout.RootCompilation.domain_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.domain_covers

/-- info: 'TrustIr.SourceLayout.TypesCompilation.domain_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypesCompilation.domain_covers

/-- info: 'TrustIr.SourceLayout.RootCompilation.preserves_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.preserves_complete

/-- info: 'TrustIr.SourceLayout.TypesCompilation.preserves_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypesCompilation.preserves_complete

/-- info: 'TrustIr.SourceLayout.prepare_allocated_present' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.prepare_allocated_present

/-- info: 'TrustIr.SourceLayout.prepare_validators_present' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.prepare_validators_present

/-- info: 'TrustIr.SourceLayout.prepare_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.prepare_complete

/-- info: 'TrustIr.SourceLayout.Session.Reachable.query_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.query_complete

/-- info: 'TrustIr.SourceLayout.Session.Reachable.complete_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.complete_invariant

/-- info: 'TrustIr.SourceLayout.Session.Reachable.closed_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.closed_invariant

/-- info: 'TrustIr.SourceLayout.prepared_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.prepared_closed

/-- info: 'TrustIr.SourceLayout.Session.Reachable.restrict_prepared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.restrict_prepared

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.mixed_reserved_lookups' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.mixed_reserved_lookups

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.mixed_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.mixed_complete

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.refusing_validators_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.refusing_validators_complete

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.cyclic_source_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.cyclic_source_complete

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.cyclic_source_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.cyclic_source_closed

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.forward_query_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.forward_query_complete

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.forward_cached_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.forward_cached_complete

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.forward_query_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.forward_query_closed

/-- info: 'TrustIr.SourceLayout.RootCompilation.array_equation_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.array_equation_source

/-- info: 'TrustIr.SourceLayout.Session.CompiledRoot.array_source_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.CompiledRoot.array_source_bounds

/-- info: 'TrustIr.SourceLayout.Session.Reachable.query_array_prepared_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.query_array_prepared_child

/-- info: 'TrustIr.SourceLayout.Session.Reachable.forked_array_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.forked_array_prepared

/-- info: 'TrustIr.SourceLayout.Session.Reachable.forked_array_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.forked_array_layout

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.automatic_forked_array_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.automatic_forked_array_origin

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.automatic_cached_array_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.automatic_cached_array_origin

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.missing_zero_array_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.missing_zero_array_refuses

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.empty_source_row_zero_array_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.empty_source_row_zero_array_refuses

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.cyclic_zero_array_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.cyclic_zero_array_refuses

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.excessive_count_refuses_before_zero_stride' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.excessive_count_refuses_before_zero_stride

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.zero_stride_array_succeeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.zero_stride_array_succeeds

/-- info: 'TrustIr.SourceLayout.PreparedReferenceControls.scalar_target_refusal_precedes_array_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedReferenceControls.scalar_target_refusal_precedes_array_source

/-- info: 'TrustIr.SourceLayout.StepsCorrespond' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StepsCorrespond

/-- info: 'TrustIr.SourceLayout.Equation.Corresponds' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Corresponds

/-- info: 'TrustIr.SourceLayout.Graph.Correspondence' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.Correspondence

/-- info: 'TrustIr.SourceLayout.StepsCorrespond.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StepsCorrespond.mono

/-- info: 'TrustIr.SourceLayout.Equation.Corresponds.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Corresponds.mono

/-- info: 'TrustIr.SourceLayout.StepsCorrespond.self_on' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StepsCorrespond.self_on

/-- info: 'TrustIr.SourceLayout.Equation.Corresponds.self_on' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Corresponds.self_on

/-- info: 'TrustIr.SourceLayout.Graph.Correspondence.grow' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.Correspondence.grow

/-- info: 'TrustIr.SourceLayout.Graph.Correspondence.adjoin' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.Correspondence.adjoin

/-- info: 'TrustIr.SourceLayout.Graph.Correspondence.closed_region' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.Correspondence.closed_region

/-- info: 'TrustIr.SourceLayout.NodeDerivation.transport_nodes' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.transport_nodes

/-- info: 'TrustIr.SourceLayout.NodeDerivation.corresponding_unique' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.corresponding_unique

/-- info: 'TrustIr.SourceLayout.NodeDerivation.below_frontier' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.NodeDerivation.below_frontier

/-- info: 'TrustIr.SourceLayout.Equation.Corresponds.scaled' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Corresponds.scaled

/-- info: 'TrustIr.SourceLayout.Equation.Corresponds.alias' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Corresponds.alias

/-- info: 'TrustIr.SourceLayout.Equation.Corresponds.done' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Corresponds.done

/-- info: 'TrustIr.SourceLayout.Graph.Correspondence.scaled_roots' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.Correspondence.scaled_roots

/-- info: 'TrustIr.SourceLayout.Session.CompiledRoot.array_success_equation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.CompiledRoot.array_success_equation

/-- info: 'TrustIr.SourceLayout.Session.Reachable.forked_array_summary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.forked_array_summary

/-- info: 'TrustIr.SourceLayout.CorrespondenceControls.aliases_with_colliding_numbers' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CorrespondenceControls.aliases_with_colliding_numbers

/-- info: 'TrustIr.SourceLayout.CorrespondenceControls.complete_metadata_transports' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CorrespondenceControls.complete_metadata_transports

/-- info: 'TrustIr.SourceLayout.CorrespondenceControls.same_extent_different_metadata' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CorrespondenceControls.same_extent_different_metadata

/-- info: 'TrustIr.SourceLayout.CorrespondenceControls.metadata_mismatch_rejects_correspondence' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CorrespondenceControls.metadata_mismatch_rejects_correspondence

/-- info: 'TrustIr.SourceLayout.CorrespondenceControls.reversed_children_reject_diagonal' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CorrespondenceControls.reversed_children_reject_diagonal

/-- info: 'TrustIr.SourceLayout.CorrespondenceControls.checks_cannot_be_replaced_by_children' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CorrespondenceControls.checks_cannot_be_replaced_by_children

/-- info: 'TrustIr.SourceLayout.CorrespondenceControls.cyclic_graphs_can_correspond' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CorrespondenceControls.cyclic_graphs_can_correspond

/-- info: 'TrustIr.SourceLayout.CorrespondenceControls.cycle_refusals_keep_local_ids' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CorrespondenceControls.cycle_refusals_keep_local_ids

/-- info: 'TrustIr.SourceLayout.CorrespondenceControls.actual_forks_disagree_outside_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CorrespondenceControls.actual_forks_disagree_outside_source

/-- info: 'TrustIr.SourceLayout.CorrespondenceControls.actual_array_forks_succeed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CorrespondenceControls.actual_array_forks_succeed

/-- info: 'TrustIr.SourceLayout.CorrespondenceControls.actual_array_forks_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CorrespondenceControls.actual_array_forks_unique

/-- info: 'TrustIr.AggregateMemory.ActualSummary.array_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ActualSummary.array_unique

/-- info: 'TrustIr.AggregateMemory.prepared_array_layout_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_array_layout_unique

/-- info: 'TrustIr.AggregateMemory.FieldBindingControls.array_plan_after_byte_preparation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindingControls.array_plan_after_byte_preparation

/-- info: 'TrustIr.AggregateMemory.FieldBindingControls.array_plan_after_wide_and_other_count_preparation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindingControls.array_plan_after_wide_and_other_count_preparation

/-- info: 'TrustIr.SourceLayout.RowsCorrespond' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RowsCorrespond

/-- info: 'TrustIr.SourceLayout.RowsCorrespond.same_length' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RowsCorrespond.same_length

/-- info: 'TrustIr.SourceLayout.RowsCorrespond.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RowsCorrespond.mono

/-- info: 'TrustIr.SourceLayout.RowsCorrespond.map' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RowsCorrespond.map

/-- info: 'TrustIr.SourceLayout.RowsCorrespond.zip_left_same' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RowsCorrespond.zip_left_same

/-- info: 'TrustIr.SourceLayout.RowsCorrespond.zip_right_same' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RowsCorrespond.zip_right_same

/-- info: 'TrustIr.SourceLayout.StepsCorrespond.append' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StepsCorrespond.append

/-- info: 'TrustIr.SourceLayout.Graph.Correspondence.allocate_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.Correspondence.allocate_pair

/-- info: 'TrustIr.SourceLayout.Equation.Corresponds.canonicalFields' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Corresponds.canonicalFields

/-- info: 'TrustIr.SourceLayout.Equation.Corresponds.declaredFields' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Corresponds.declaredFields

/-- info: 'TrustIr.SourceLayout.Equation.Corresponds.canonicalZip' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Corresponds.canonicalZip

/-- info: 'TrustIr.SourceLayout.Equation.Corresponds.declaredMapZip' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Corresponds.declaredMapZip

/-- info: 'TrustIr.SourceLayout.Equation.Corresponds.sequence' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Corresponds.sequence

/-- info: 'TrustIr.SourceLayout.FieldCorrespondenceControls.shared_scalar_rows' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldCorrespondenceControls.shared_scalar_rows

/-- info: 'TrustIr.SourceLayout.FieldCorrespondenceControls.canonical_field_equations' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldCorrespondenceControls.canonical_field_equations

/-- info: 'TrustIr.SourceLayout.FieldCorrespondenceControls.allocated_canonical_parents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldCorrespondenceControls.allocated_canonical_parents

/-- info: 'TrustIr.SourceLayout.FieldCorrespondenceControls.canonical_queries_keep_types_and_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldCorrespondenceControls.canonical_queries_keep_types_and_order

/-- info: 'TrustIr.SourceLayout.FieldCorrespondenceControls.canonical_metadata_transports' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldCorrespondenceControls.canonical_metadata_transports

/-- info: 'TrustIr.SourceLayout.FieldCorrespondenceControls.packed_field_equations' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldCorrespondenceControls.packed_field_equations

/-- info: 'TrustIr.SourceLayout.FieldCorrespondenceControls.packed_queries_keep_effective_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldCorrespondenceControls.packed_queries_keep_effective_alignment

/-- info: 'TrustIr.SourceLayout.FieldCorrespondenceControls.missing_nonzero_offset_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldCorrespondenceControls.missing_nonzero_offset_refuses

/-- info: 'TrustIr.SourceLayout.FieldCorrespondenceControls.omitted_zero_field_retains_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldCorrespondenceControls.omitted_zero_field_retains_metadata

/-- info: 'TrustIr.SourceLayout.FieldCorrespondenceControls.transparent_multiple_carriers_refuse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldCorrespondenceControls.transparent_multiple_carriers_refuse

/-- info: 'TrustIr.SourceLayout.FieldCorrespondenceControls.prefix_sequences_correspond_before_initial_failure' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldCorrespondenceControls.prefix_sequences_correspond_before_initial_failure

/-- info: 'TrustIr.SourceLayout.FieldCorrespondenceControls.prefix_refusal_precedes_deferred_initial_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldCorrespondenceControls.prefix_refusal_precedes_deferred_initial_failure

/-- info: 'TrustIr.SourceLayout.FieldCorrespondenceControls.same_extent_field_types_cannot_be_substituted' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldCorrespondenceControls.same_extent_field_types_cannot_be_substituted

/-- info: 'TrustIr.SourceLayout.FieldCorrespondenceControls.declared_offsets_cannot_be_shifted' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldCorrespondenceControls.declared_offsets_cannot_be_shifted

/-- info: 'TrustIr.SourceLayout.FieldCorrespondenceControls.truncated_child_rows_are_rejected' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.FieldCorrespondenceControls.truncated_child_rows_are_rejected

/-- info: 'TrustIr.SourceLayout.RootCompilation.corresponds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.corresponds

/-- info: 'TrustIr.SourceLayout.TypesCompilation.corresponds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypesCompilation.corresponds

/-- info: 'TrustIr.SourceLayout.Session.CompiledRoot.corresponds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.CompiledRoot.corresponds

/-- info: 'TrustIr.SourceLayout.Session.Reachable.forked_typed_summary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.forked_typed_summary

/-- info: 'TrustIr.SourceLayout.TypedCorrespondenceControls.scalar_hit_and_miss_return_same_summary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypedCorrespondenceControls.scalar_hit_and_miss_return_same_summary

/-- info: 'TrustIr.SourceLayout.TypedCorrespondenceControls.scalar_hit_and_miss_have_different_frontiers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypedCorrespondenceControls.scalar_hit_and_miss_have_different_frontiers

/-- info: 'TrustIr.SourceLayout.TypedCorrespondenceControls.cached_scalar_root_is_reused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypedCorrespondenceControls.cached_scalar_root_is_reused

/-- info: 'TrustIr.SourceLayout.TypedCorrespondenceControls.cached_scalar_and_fresh_query_are_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypedCorrespondenceControls.cached_scalar_and_fresh_query_are_unique

/-- info: 'TrustIr.SourceLayout.TypedCorrespondenceControls.scalar_hit_and_miss_are_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypedCorrespondenceControls.scalar_hit_and_miss_are_unique

/-- info: 'TrustIr.SourceLayout.TypedCorrespondenceControls.nested_vectors_in_disagreeing_graphs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypedCorrespondenceControls.nested_vectors_in_disagreeing_graphs

/-- info: 'TrustIr.SourceLayout.TypedCorrespondenceControls.canonical_tuple_keeps_all_child_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypedCorrespondenceControls.canonical_tuple_keeps_all_child_metadata

/-- info: 'TrustIr.SourceLayout.TypedCorrespondenceControls.canonical_tuple_full_summary_is_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypedCorrespondenceControls.canonical_tuple_full_summary_is_unique

/-- info: 'TrustIr.SourceLayout.TypedCorrespondenceControls.declared_tuple_uses_shape_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypedCorrespondenceControls.declared_tuple_uses_shape_children

/-- info: 'TrustIr.SourceLayout.TypedCorrespondenceControls.nominal_lookup_modes_are_not_conflated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypedCorrespondenceControls.nominal_lookup_modes_are_not_conflated

/-- info: 'TrustIr.SourceLayout.TypedCorrespondenceControls.refinement_shape_keeps_original_reference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypedCorrespondenceControls.refinement_shape_keeps_original_reference

/-- info: 'TrustIr.SourceLayout.TypedCorrespondenceControls.refinement_execution_still_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypedCorrespondenceControls.refinement_execution_still_refuses

/-- info: 'TrustIr.SourceLayout.TypedCorrespondenceControls.typed_closure_shape_retains_capture_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypedCorrespondenceControls.typed_closure_shape_retains_capture_metadata

/-- info: 'TrustIr.SourceLayout.TypedCorrespondenceControls.typed_closure_execution_still_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypedCorrespondenceControls.typed_closure_execution_still_refuses

/-- info: 'TrustIr.SourceLayout.TypedCorrespondenceControls.unsupported_shape_tuple_still_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypedCorrespondenceControls.unsupported_shape_tuple_still_refuses

/-- info: 'TrustIr.SourceLayout.TypedCorrespondenceControls.invalid_global_tuple_metadata_still_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypedCorrespondenceControls.invalid_global_tuple_metadata_still_refuses

/-- info: 'TrustIr.SourceLayout.TypedCorrespondenceControls.cyclic_nested_array_still_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypedCorrespondenceControls.cyclic_nested_array_still_refuses

/-- info: 'TrustIr.AggregateMemory.ActualSummary.functional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ActualSummary.functional

/-- info: 'TrustIr.AggregateMemory.prepared_plan_layout_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_plan_layout_unique

/-- info: 'TrustIr.AggregateMemory.FieldBindingControls.tuple_plan_after_byte_preparation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindingControls.tuple_plan_after_byte_preparation

/-- info: 'TrustIr.AggregateMemory.FieldBindingControls.tuple_plan_after_wide_and_array_preparation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldBindingControls.tuple_plan_after_wide_and_array_preparation

/-- info: 'TrustIr.SourceLayout.Graph.Extends.insert_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Graph.Extends.insert_fresh

/-- info: 'TrustIr.SourceLayout.RootCompilation.corresponds_in_extensions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.corresponds_in_extensions

/-- info: 'TrustIr.SourceLayout.TypesCompilation.corresponds_in_extensions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypesCompilation.corresponds_in_extensions

/-- info: 'TrustIr.SourceLayout.RootCompilation.preserves_reserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.preserves_reserved

/-- info: 'TrustIr.SourceLayout.TypesCompilation.preserves_reserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypesCompilation.preserves_reserved

/-- info: 'TrustIr.SourceLayout.CompletionCorrespondenceControls.early_original_correspondence_is_unavailable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CompletionCorrespondenceControls.early_original_correspondence_is_unavailable

/-- info: 'TrustIr.SourceLayout.CompletionCorrespondenceControls.array_compilation_keeps_unfilled_reference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CompletionCorrespondenceControls.array_compilation_keeps_unfilled_reference

/-- info: 'TrustIr.SourceLayout.CompletionCorrespondenceControls.array_compilation_keeps_installed_originals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CompletionCorrespondenceControls.array_compilation_keeps_installed_originals

/-- info: 'TrustIr.SourceLayout.CompletionCorrespondenceControls.array_outputs_correspond_after_filling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CompletionCorrespondenceControls.array_outputs_correspond_after_filling

/-- info: 'TrustIr.SourceLayout.CompletionCorrespondenceControls.completed_array_queries_succeed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CompletionCorrespondenceControls.completed_array_queries_succeed

/-- info: 'TrustIr.SourceLayout.CompletionCorrespondenceControls.completed_array_derivation_transports' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CompletionCorrespondenceControls.completed_array_derivation_transports

/-- info: 'TrustIr.SourceLayout.CompletionCorrespondenceControls.replacing_emitted_equation_is_not_an_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CompletionCorrespondenceControls.replacing_emitted_equation_is_not_an_extension

/-- info: 'TrustIr.SourceLayout.CompletionCorrespondenceControls.missing_reference_compiles_before_installation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CompletionCorrespondenceControls.missing_reference_compiles_before_installation

/-- info: 'TrustIr.SourceLayout.CompletionCorrespondenceControls.reference_outputs_correspond_after_installation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CompletionCorrespondenceControls.reference_outputs_correspond_after_installation

/-- info: 'TrustIr.SourceLayout.CompletionCorrespondenceControls.installed_reference_query_succeeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CompletionCorrespondenceControls.installed_reference_query_succeeds

/-- info: 'TrustIr.SourceLayout.CompletionCorrespondenceControls.late_cyclic_reference_remains_a_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.CompletionCorrespondenceControls.late_cyclic_reference_remains_a_refusal

/-- info: 'TrustIr.SourceLayout.prepare_type_compilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.prepare_type_compilation

/-- info: 'TrustIr.SourceLayout.Session.Reachable.prepared_type_summary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.prepared_type_summary

/-- info: 'TrustIr.AggregateMemory.ActualSummary.prepared_type_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ActualSummary.prepared_type_row

/-- info: 'TrustIr.AggregateMemory.ActualSummary.array_element_extent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ActualSummary.array_element_extent

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.source_array_extent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.source_array_extent

/-- info: 'TrustIr.AggregateMemory.prepared_array_element_extent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_array_element_extent

/-- info: 'TrustIr.AggregateMemory.Plan.LanePath.array' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.LanePath.array

/-- info: 'TrustIr.SourceLayout.PreparedRowControls.backward_row_copies_installed_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedRowControls.backward_row_copies_installed_body

/-- info: 'TrustIr.SourceLayout.PreparedRowControls.forward_row_installs_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedRowControls.forward_row_installs_alias

/-- info: 'TrustIr.SourceLayout.PreparedRowControls.copied_row_agrees_with_any_actual_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedRowControls.copied_row_agrees_with_any_actual_query

/-- info: 'TrustIr.SourceLayout.PreparedRowControls.forward_alias_agrees_with_any_actual_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedRowControls.forward_alias_agrees_with_any_actual_query

/-- info: 'TrustIr.SourceLayout.PreparedRowControls.self_alias_still_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedRowControls.self_alias_still_refuses

/-- info: 'TrustIr.SourceLayout.PreparedRowControls.cyclic_source_row_has_no_finite_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedRowControls.cyclic_source_row_has_no_finite_success

/-- info: 'TrustIr.SourceLayout.PreparedRowControls.execution_row_aliases_later_nominal_definition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedRowControls.execution_row_aliases_later_nominal_definition

/-- info: 'TrustIr.SourceLayout.PreparedRowControls.execution_nominal_row_agrees_with_any_actual_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.PreparedRowControls.execution_nominal_row_agrees_with_any_actual_query

/-- info: 'TrustIr.AggregateMemory.SourceArrayExtentControls.nested_array_path_without_parent_bound' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceArrayExtentControls.nested_array_path_without_parent_bound

/-- info: 'TrustIr.AggregateMemory.SourceArrayExtentControls.actual_nested_array_path_is_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceArrayExtentControls.actual_nested_array_path_is_covered

/-- info: 'TrustIr.AggregateMemory.SourceArrayExtentControls.actual_nested_array_path_is_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceArrayExtentControls.actual_nested_array_path_is_bounded

/-- info: 'TrustIr.AggregateMemory.SourceArrayExtentControls.actual_nested_array_path_initializes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceArrayExtentControls.actual_nested_array_path_initializes

/-- info: 'TrustIr.AggregateMemory.SourceArrayExtentControls.undersized_parent_has_no_actual_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceArrayExtentControls.undersized_parent_has_no_actual_origin

/-- info: 'TrustIr.AggregateMemory.SourceArrayExtentControls.forged_child_stride_has_no_actual_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceArrayExtentControls.forged_child_stride_has_no_actual_origin

/-- info: 'TrustIr.AggregateMemory.SourceArrayExtentControls.zero_sized_elements_keep_exact_extent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceArrayExtentControls.zero_sized_elements_keep_exact_extent

/-- info: 'TrustIr.AggregateMemory.SourceArrayExtentControls.zero_count_has_no_logical_lane' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceArrayExtentControls.zero_count_has_no_logical_lane

/-- info: 'TrustIr.integer_encoding_residue' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.integer_encoding_residue

/-- info: 'TrustIr.decode_encode_integer_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.decode_encode_integer_residue

/-- info: 'TrustIr.integer_memory_width_aligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.integer_memory_width_aligned

/-- info: 'TrustIr.encodeMemory_integer_residue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.encodeMemory_integer_residue

/-- info: 'TrustIr.decodeMemory_integer_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.decodeMemory_integer_bytes

/-- info: 'TrustIr.integer_memory_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.integer_memory_roundtrip

/-- info: 'TrustIr.boolean_memory_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.boolean_memory_roundtrip

/-- info: 'TrustIr.integer_memory_roundtrip_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.integer_memory_roundtrip_valid

/-- info: 'TrustIr.integer_aggregate_leaf_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.integer_aggregate_leaf_roundtrip

/-- info: 'TrustIr.boolean_aggregate_leaf_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.boolean_aggregate_leaf_roundtrip

/-- info: 'TrustIr.ScalarCodecControls.negative_i128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ScalarCodecControls.negative_i128

/-- info: 'TrustIr.ScalarCodecControls.target_sized_32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ScalarCodecControls.target_sized_32

/-- info: 'TrustIr.ScalarCodecControls.target_sized_64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ScalarCodecControls.target_sized_64

/-- info: 'TrustIr.ScalarCodecControls.oversized_u8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ScalarCodecControls.oversized_u8

/-- info: 'TrustIr.ScalarCodecControls.char_surrogate_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ScalarCodecControls.char_surrogate_refuses

/-- info: 'TrustIr.ScalarCodecControls.valid_char' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ScalarCodecControls.valid_char

/-- info: 'TrustIr.ScalarCodecControls.wrong_leaf_width_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ScalarCodecControls.wrong_leaf_width_refuses

/-- info: 'TrustIr.ScalarCodecControls.wrong_leaf_extent_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ScalarCodecControls.wrong_leaf_extent_refuses

/-- info: 'TrustIr.AggregateMemory.encode_integer_leaf_of_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_integer_leaf_of_memory

/-- info: 'TrustIr.AggregateMemory.decode_leaf_of_bytes' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decode_leaf_of_bytes

/-- info: 'TrustIr.encodeMemory_pointer_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.encodeMemory_pointer_word

/-- info: 'TrustIr.decodeMemory_pointer_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.decodeMemory_pointer_bytes

/-- info: 'TrustIr.pointer_memory_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.pointer_memory_roundtrip

/-- info: 'TrustIr.pointer_memory_refuses_overflow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.pointer_memory_refuses_overflow

/-- info: 'TrustIr.pointer_memory_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.pointer_memory_result

/-- info: 'TrustIr.null_pointer_memory_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.null_pointer_memory_roundtrip

/-- info: 'TrustIr.decodeMemory_fat_pointer_words' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.decodeMemory_fat_pointer_words

/-- info: 'TrustIr.encodeMemory_fat_length_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.encodeMemory_fat_length_words

/-- info: 'TrustIr.fat_length_memory_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.fat_length_memory_roundtrip

/-- info: 'TrustIr.encodeMemory_fat_vtable_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.encodeMemory_fat_vtable_words

/-- info: 'TrustIr.fat_vtable_memory_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.fat_vtable_memory_roundtrip

/-- info: 'TrustIr.fat_null_metadata_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.fat_null_metadata_image

/-- info: 'TrustIr.fat_null_vtable_memory_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.fat_null_vtable_memory_roundtrip

/-- info: 'TrustIr.fat_pointer_memory_refuses_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.fat_pointer_memory_refuses_data

/-- info: 'TrustIr.fat_pointer_memory_refuses_vtable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.fat_pointer_memory_refuses_vtable

/-- info: 'TrustIr.fat_length_store_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.fat_length_store_valid

/-- info: 'TrustIr.fat_vtable_store_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.fat_vtable_store_valid

/-- info: 'TrustIr.pointer_aggregate_leaf_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.pointer_aggregate_leaf_roundtrip

/-- info: 'TrustIr.null_pointer_aggregate_leaf_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.null_pointer_aggregate_leaf_roundtrip

/-- info: 'TrustIr.fat_length_aggregate_leaf_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.fat_length_aggregate_leaf_roundtrip

/-- info: 'TrustIr.fat_vtable_aggregate_leaf_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.fat_vtable_aggregate_leaf_roundtrip

/-- info: 'TrustIr.fat_null_store_valid' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.fat_null_store_valid

/-- info: 'TrustIr.fat_null_vtable_aggregate_leaf_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.fat_null_vtable_aggregate_leaf_roundtrip

/-- info: 'TrustIr.PointerCodecControls.zero_pointer_canonicalizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PointerCodecControls.zero_pointer_canonicalizes

/-- info: 'TrustIr.PointerCodecControls.forged_provenance_is_not_restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PointerCodecControls.forged_provenance_is_not_restored

/-- info: 'TrustIr.PointerCodecControls.dead_allocation_provenance_recovers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PointerCodecControls.dead_allocation_provenance_recovers

/-- info: 'TrustIr.PointerCodecControls.one_past_provenance_recovers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PointerCodecControls.one_past_provenance_recovers

/-- info: 'TrustIr.PointerCodecControls.containment_precedes_one_past' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PointerCodecControls.containment_precedes_one_past

/-- info: 'TrustIr.PointerCodecControls.reference_leaf_recovers_by_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PointerCodecControls.reference_leaf_recovers_by_address

/-- info: 'TrustIr.PointerCodecControls.length_metadata_is_32_bit_residue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PointerCodecControls.length_metadata_is_32_bit_residue

/-- info: 'TrustIr.PointerCodecControls.null_data_retains_length_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PointerCodecControls.null_data_retains_length_lane

/-- info: 'TrustIr.PointerCodecControls.data_and_vtable_provenance_are_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PointerCodecControls.data_and_vtable_provenance_are_independent

/-- info: 'TrustIr.PointerCodecControls.null_vtable_leaf_roundtrips' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PointerCodecControls.null_vtable_leaf_roundtrips

/-- info: 'TrustIr.PointerCodecControls.thin_overflow_is_not_truncated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PointerCodecControls.thin_overflow_is_not_truncated

/-- info: 'TrustIr.PointerCodecControls.fat_data_overflow_is_not_truncated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PointerCodecControls.fat_data_overflow_is_not_truncated

/-- info: 'TrustIr.PointerCodecControls.vtable_overflow_is_not_truncated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PointerCodecControls.vtable_overflow_is_not_truncated

/-- info: 'TrustIr.PointerCodecControls.wrong_metadata_kind_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PointerCodecControls.wrong_metadata_kind_refuses

/-- info: 'TrustIr.PointerCodecControls.wrong_thin_leaf_extent_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PointerCodecControls.wrong_thin_leaf_extent_refuses

/-- info: 'TrustIr.PointerCodecControls.target32_aggregate_fat_guard_precedes_word_overflow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PointerCodecControls.target32_aggregate_fat_guard_precedes_word_overflow

/-- info: 'TrustIr.PointerCodecControls.target64_aggregate_fat_word_overflow_is_ub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PointerCodecControls.target64_aggregate_fat_word_overflow_is_ub

/-- info: 'TrustIr.PointerCodecControls.target32_length_metadata_rejects_64_bit_carrier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PointerCodecControls.target32_length_metadata_rejects_64_bit_carrier

/-- info: 'TrustIr.PointerCodecControls.target64_length_metadata_rejects_32_bit_carrier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.PointerCodecControls.target64_length_metadata_rejects_32_bit_carrier

/-- info: 'TrustIr.AggregateMemory.encode_pointer_leaf_of_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_pointer_leaf_of_memory

/-- info: 'TrustIr.AggregateMemory.encode_fat_pointer_leaf_of_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_fat_pointer_leaf_of_memory

/-- info: 'TrustIr.AggregateMemory.ByteLane.append_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteLane.append_left

/-- info: 'TrustIr.AggregateMemory.ByteLane.append_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteLane.append_right

/-- info: 'TrustIr.AggregateMemory.ByteLane.tile_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteLane.tile_copy

/-- info: 'TrustIr.AggregateMemory.ByteLane.tile_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteLane.tile_slot

/-- info: 'TrustIr.AggregateMemory.ArrayImageEncoded.dense_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayImageEncoded.dense_slots

/-- info: 'TrustIr.AggregateMemory.ArrayImageEncoded.uniform_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayImageEncoded.uniform_image

/-- info: 'TrustIr.AggregateMemory.encode_dense_array_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_dense_array_slot

/-- info: 'TrustIr.AggregateMemory.encode_uniform_array_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_uniform_array_slot

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.zero_stride_visible_poison_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.zero_stride_visible_poison_refuses

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.zero_count_hidden_poison_is_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.zero_count_hidden_poison_is_unused

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.zero_stride_uniform_slot_has_actual_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.zero_stride_uniform_slot_has_actual_child

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.dense_second_slot_has_selected_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.dense_second_slot_has_selected_child

/-- info: 'TrustIr.AggregateMemory.ArrayImageEncoded.slots_of_repetition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayImageEncoded.slots_of_repetition

/-- info: 'TrustIr.AggregateMemory.ArrayImageEncoded.slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayImageEncoded.slots

/-- info: 'TrustIr.AggregateMemory.encode_array_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_array_slot

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.split_left_boundary_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.split_left_boundary_child

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.split_right_boundary_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.split_right_boundary_child

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.cyclic_prefix_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.cyclic_prefix_child

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.cyclic_middle_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.cyclic_middle_child

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.cyclic_tail_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.cyclic_tail_child

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.cyclic_tail_value_and_padding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.cyclic_tail_value_and_padding

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.clipped_cycle_does_not_force_poison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.clipped_cycle_does_not_force_poison

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.clipped_cycle_selected_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.clipped_cycle_selected_child

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.complete_cycle_forces_visible_poison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.complete_cycle_forces_visible_poison

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.clipped_tail_forces_visible_poison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.clipped_tail_forces_visible_poison

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.zero_stride_cyclic_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.zero_stride_cyclic_success

/-- info: 'TrustIr.AggregateMemory.ArrayLaneControls.zero_stride_cyclic_selected_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayLaneControls.zero_stride_cyclic_selected_child

/-- info: 'TrustIr.ByteImage.WindowRuntime.canonicalImage_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.WindowRuntime.canonicalImage_size

/-- info: 'TrustIr.ByteImage.WindowRuntime.canonicalImage_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.WindowRuntime.canonicalImage_get

/-- info: 'TrustIr.ByteImage.WindowRuntime.canonicalImage_toList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.WindowRuntime.canonicalImage_toList

/-- info: 'TrustIr.ByteImage.WindowRuntime.canonicalImage_slice_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.WindowRuntime.canonicalImage_slice_get

/-- info: 'TrustIr.ByteImage.WindowRuntime.canonicalImage_slice_toList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.WindowRuntime.canonicalImage_slice_toList

/-- info: 'TrustIr.ByteImage.CanonicalWindowControls.nested_views_preserve_source_and_padding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.CanonicalWindowControls.nested_views_preserve_source_and_padding

/-- info: 'TrustIr.ByteImage.CanonicalWindowControls.left_branch_window_preserves_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.CanonicalWindowControls.left_branch_window_preserves_bytes

/-- info: 'TrustIr.ByteImage.CanonicalWindowControls.right_branch_window_preserves_absence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.CanonicalWindowControls.right_branch_window_preserves_absence

/-- info: 'TrustIr.ByteImage.CanonicalWindowControls.crossing_window_retains_both_branches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.CanonicalWindowControls.crossing_window_retains_both_branches

/-- info: 'TrustIr.ByteImage.CanonicalWindowControls.oversized_request_stays_clipped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.CanonicalWindowControls.oversized_request_stays_clipped

/-- info: 'TrustIr.ByteImage.CanonicalWindowControls.empty_window_has_no_invented_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.CanonicalWindowControls.empty_window_has_no_invented_bytes

/-- info: 'TrustIr.ByteImage.CanonicalWindowControls.byte_equality_does_not_equate_constructor_callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.CanonicalWindowControls.byte_equality_does_not_equate_constructor_callbacks

/-- info: 'TrustIr.ByteImage.mapBlocksSpec_decoded_of_periods' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.mapBlocksSpec_decoded_of_periods

/-- info: 'TrustIr.ByteImage.mapBlocksSpec_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.mapBlocksSpec_decoded

/-- info: 'TrustIr.ByteImage.mapBlocks_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.mapBlocks_decoded

/-- info: 'TrustIr.AggregateMemory.decode_array_slots_of_mapper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decode_array_slots_of_mapper

/-- info: 'TrustIr.AggregateMemory.decode_array_slots' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decode_array_slots

/-- info: 'TrustIr.AggregateMemory.decode_array_slot' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decode_array_slot

/-- info: 'TrustIr.AggregateMemory.decode_source_array_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decode_source_array_slot

/-- info: 'TrustIr.AggregateMemory.prepared_array_decoded_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_array_decoded_slot

/-- info: 'TrustIr.AggregateMemory.array_slot_codec_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.array_slot_codec_bytes

/-- info: 'TrustIr.AggregateMemory.prepared_array_slot_codec_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_array_slot_codec_bytes

/-- info: 'TrustIr.ByteImage.DecoderSlotControls.periodic_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.DecoderSlotControls.periodic_prefix

/-- info: 'TrustIr.ByteImage.DecoderSlotControls.periodic_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.DecoderSlotControls.periodic_middle

/-- info: 'TrustIr.ByteImage.DecoderSlotControls.periodic_tail_and_outside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.DecoderSlotControls.periodic_tail_and_outside

/-- info: 'TrustIr.ByteImage.DecoderSlotControls.nontrivial_gcd_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.DecoderSlotControls.nontrivial_gcd_cycle

/-- info: 'TrustIr.ByteImage.DecoderSlotControls.whole_period_width' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.DecoderSlotControls.whole_period_width

/-- info: 'TrustIr.ByteImage.DecoderSlotControls.ordinary_nested_views' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.DecoderSlotControls.ordinary_nested_views

/-- info: 'TrustIr.ByteImage.DecoderSlotControls.append_descent_and_padding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.DecoderSlotControls.append_descent_and_padding

/-- info: 'TrustIr.ByteImage.DecoderSlotControls.zero_width_has_logical_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.DecoderSlotControls.zero_width_has_logical_slots

/-- info: 'TrustIr.ByteImage.DecoderSlotControls.zero_count_ignores_callback_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.DecoderSlotControls.zero_count_ignores_callback_error

/-- info: 'TrustIr.ByteImage.DecoderSlotControls.nonempty_zero_width_forces_callback_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.DecoderSlotControls.nonempty_zero_width_forces_callback_error

/-- info: 'TrustIr.ByteImage.DecoderSlotControls.periodic_errors_keep_left_to_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.DecoderSlotControls.periodic_errors_keep_left_to_right

/-- info: 'TrustIr.ByteImage.DecoderSlotControls.incorrect_extent_can_clip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.DecoderSlotControls.incorrect_extent_can_clip

/-- info: 'TrustIr.ByteImage.DecoderSlotControls.periodic_slot_has_actual_callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.DecoderSlotControls.periodic_slot_has_actual_callback

/-- info: 'TrustIr.ByteImage.DecoderSlotControls.ordinary_slot_has_actual_callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.DecoderSlotControls.ordinary_slot_has_actual_callback

/-- info: 'TrustIr.AggregateMemory.ArrayDecoderControls.tuple_array_keeps_padding_absent' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayDecoderControls.tuple_array_keeps_padding_absent

/-- info: 'TrustIr.AggregateMemory.ArrayDecoderControls.nested_char_retains_raw_word' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayDecoderControls.nested_char_retains_raw_word

/-- info: 'TrustIr.AggregateMemory.ArrayDecoderControls.top_level_char_validation_stays_distinct' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayDecoderControls.top_level_char_validation_stays_distinct

/-- info: 'TrustIr.AggregateMemory.ArrayDecoderControls.zero_stride_decoder_has_actual_slots' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayDecoderControls.zero_stride_decoder_has_actual_slots

/-- info: 'TrustIr.AggregateMemory.ArrayDecoderControls.zero_count_decoder_does_not_force_child' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayDecoderControls.zero_count_decoder_does_not_force_child

/-- info: 'TrustIr.AggregateMemory.ArrayDecoderControls.missing_covered_byte_refuses' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayDecoderControls.missing_covered_byte_refuses

/-- info: 'TrustIr.AggregateMemory.ArrayDecoderControls.parent_extent_mismatch_refuses' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayDecoderControls.parent_extent_mismatch_refuses

/-- info: 'TrustIr.AggregateMemory.ArrayDecoderControls.selected_child_keeps_padding' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayDecoderControls.selected_child_keeps_padding

/-- info: 'TrustIr.AggregateMemory.ChildDecoded.extent' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ChildDecoded.extent

/-- info: 'TrustIr.AggregateMemory.FieldsDecoded.nil_iff' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsDecoded.nil_iff

/-- info: 'TrustIr.AggregateMemory.FieldsDecoded.head' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsDecoded.head

/-- info: 'TrustIr.AggregateMemory.decode_fields_steps' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decode_fields_steps

/-- info: 'TrustIr.AggregateMemory.FieldsDecoded.length' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsDecoded.length

/-- info: 'TrustIr.AggregateMemory.FieldsDecoded.at' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsDecoded.at

/-- info: 'TrustIr.AggregateMemory.ByteLane.slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteLane.slice

/-- info: 'TrustIr.AggregateMemory.decode_field_slot' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decode_field_slot

/-- info: 'TrustIr.AggregateMemory.field_slot_codec_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.field_slot_codec_bytes

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.fields_child_placement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.fields_child_placement

/-- info: 'TrustIr.AggregateMemory.decode_source_field_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decode_source_field_slot

/-- info: 'TrustIr.AggregateMemory.prepared_field_decoded_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_field_decoded_slot

/-- info: 'TrustIr.AggregateMemory.field_slot_codec_bytes_of_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.field_slot_codec_bytes_of_origin

/-- info: 'TrustIr.AggregateMemory.prepared_field_slot_codec_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_field_slot_codec_bytes

/-- info: 'TrustIr.AggregateMemory.FieldDecoderControls.nested_padded_child_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldDecoderControls.nested_padded_child_roundtrip

/-- info: 'TrustIr.AggregateMemory.FieldDecoderControls.padding_survives_later_field' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldDecoderControls.padding_survives_later_field

/-- info: 'TrustIr.AggregateMemory.FieldDecoderControls.field_positions_are_logical' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldDecoderControls.field_positions_are_logical

/-- info: 'TrustIr.AggregateMemory.FieldDecoderControls.zero_size_fields_keep_positions' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldDecoderControls.zero_size_fields_keep_positions

/-- info: 'TrustIr.AggregateMemory.FieldDecoderControls.clipped_empty_child_does_not_prove_parent_bounds' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldDecoderControls.clipped_empty_child_does_not_prove_parent_bounds

/-- info: 'TrustIr.AggregateMemory.FieldDecoderControls.forged_empty_offset_has_no_lane' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldDecoderControls.forged_empty_offset_has_no_lane

/-- info: 'TrustIr.AggregateMemory.FieldDecoderControls.forged_empty_offset_has_no_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldDecoderControls.forged_empty_offset_has_no_origin

/-- info: 'TrustIr.AggregateMemory.FieldDecoderControls.overlapping_suffix_changes_earlier_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldDecoderControls.overlapping_suffix_changes_earlier_value

/-- info: 'TrustIr.AggregateMemory.FieldDecoderControls.overlapping_fields_have_no_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldDecoderControls.overlapping_fields_have_no_origin

/-- info: 'TrustIr.AggregateMemory.FieldDecoderControls.nested_char_keeps_strict_raw_rule' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldDecoderControls.nested_char_keeps_strict_raw_rule

/-- info: 'TrustIr.AggregateMemory.FieldDecoderControls.missing_covered_byte_refuses' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldDecoderControls.missing_covered_byte_refuses

/-- info: 'TrustIr.AggregateMemory.FieldDecoderControls.parent_extent_mismatch_refuses' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldDecoderControls.parent_extent_mismatch_refuses

/-- info: 'TrustIr.AggregateMemory.FieldDecoderControls.array_child_is_observed_pointwise' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldDecoderControls.array_child_is_observed_pointwise

/-- info: 'TrustIr.AggregateMemory.FieldDecoderControls.prepared_child_geometry_includes_padding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldDecoderControls.prepared_child_geometry_includes_padding

/-- info: 'TrustIr.AggregateMemory.FieldDecoderControls.prepared_child_callback_retains_padding' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldDecoderControls.prepared_child_callback_retains_padding

/-- info: 'TrustIr.AggregateMemory.VariantDecoded.fields' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantDecoded.fields

/-- info: 'TrustIr.AggregateMemory.EnumDecodingSelects.functional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecodingSelects.functional

/-- info: 'TrustIr.AggregateMemory.decode_enumeration_steps' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decode_enumeration_steps

/-- info: 'TrustIr.AggregateMemory.ChildDecoded.enumeration_steps' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ChildDecoded.enumeration_steps

/-- info: 'TrustIr.AggregateMemory.decode_enum_selected_fields' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decode_enum_selected_fields

/-- info: 'TrustIr.AggregateMemory.decode_enum_payload_slot' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decode_enum_payload_slot

/-- info: 'TrustIr.AggregateMemory.enum_payload_slot_codec_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.enum_payload_slot_codec_bytes

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.enum_payload_child_placement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.enum_payload_child_placement

/-- info: 'TrustIr.AggregateMemory.decode_source_enum_payload_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decode_source_enum_payload_slot

/-- info: 'TrustIr.AggregateMemory.prepared_enum_decoded_payload_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_enum_decoded_payload_slot

/-- info: 'TrustIr.AggregateMemory.enum_payload_slot_codec_bytes_of_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.enum_payload_slot_codec_bytes_of_origin

/-- info: 'TrustIr.AggregateMemory.prepared_enum_payload_slot_codec_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_enum_payload_slot_codec_bytes

/-- info: 'TrustIr.AggregateMemory.prepared_enum_capture_payload_codec_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_enum_capture_payload_codec_bytes

/-- info: 'TrustIr.AggregateMemory.EnumDecoderControls.direct_payload_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecoderControls.direct_payload_roundtrip

/-- info: 'TrustIr.AggregateMemory.EnumDecoderControls.tag_and_payload_positions_are_distinct' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecoderControls.tag_and_payload_positions_are_distinct

/-- info: 'TrustIr.AggregateMemory.EnumDecoderControls.live_empty_payload_keeps_logical_discriminant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecoderControls.live_empty_payload_keeps_logical_discriminant

/-- info: 'TrustIr.AggregateMemory.EnumDecoderControls.untagged_zero_size_payload_is_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecoderControls.untagged_zero_size_payload_is_present

/-- info: 'TrustIr.AggregateMemory.EnumDecoderControls.single_inhabited_uses_source_position' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecoderControls.single_inhabited_uses_source_position

/-- info: 'TrustIr.AggregateMemory.EnumDecoderControls.default_niche_reads_real_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecoderControls.default_niche_reads_real_payload

/-- info: 'TrustIr.AggregateMemory.EnumDecoderControls.tagged_niche_maps_to_logical_discriminant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecoderControls.tagged_niche_maps_to_logical_discriminant

/-- info: 'TrustIr.AggregateMemory.EnumDecoderControls.default_niche_carrier_is_not_initialized_by_successful_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecoderControls.default_niche_carrier_is_not_initialized_by_successful_store

/-- info: 'TrustIr.AggregateMemory.EnumDecoderControls.absent_payload_row_refuses' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecoderControls.absent_payload_row_refuses

/-- info: 'TrustIr.AggregateMemory.EnumDecoderControls.uninhabited_flag_refuses_present_row' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecoderControls.uninhabited_flag_refuses_present_row

/-- info: 'TrustIr.AggregateMemory.EnumDecoderControls.signed_tag_uses_logical_table_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecoderControls.signed_tag_uses_logical_table_value

/-- info: 'TrustIr.AggregateMemory.EnumDecoderControls.missing_covered_payload_byte_refuses' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecoderControls.missing_covered_payload_byte_refuses

/-- info: 'TrustIr.AggregateMemory.EnumDecoderControls.parent_extent_mismatch_refuses' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecoderControls.parent_extent_mismatch_refuses

/-- info: 'TrustIr.AggregateMemory.EnumDecoderControls.payload_census_mismatch_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecoderControls.payload_census_mismatch_refuses

/-- info: 'TrustIr.AggregateMemory.EnumDecoderControls.prepared_payload_geometry_includes_padding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecoderControls.prepared_payload_geometry_includes_padding

/-- info: 'TrustIr.AggregateMemory.EnumDecoderControls.selected_payload_callback_keeps_padding' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecoderControls.selected_payload_callback_keeps_padding

/-- info: 'TrustIr.ByteImage.toList_eq_of_observations' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.toList_eq_of_observations

/-- info: 'TrustIr.ByteImage.slice_get_eq_of_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.slice_get_eq_of_observations

/-- info: 'TrustIr.ByteImage.slice_toList_eq_of_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.slice_toList_eq_of_observations

/-- info: 'TrustIr.AggregateMemory.encode_uniform_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_uniform_array

/-- info: 'TrustIr.AggregateMemory.ChildDecoded.leaf_bytes_iff' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ChildDecoded.leaf_bytes_iff

/-- info: 'TrustIr.AggregateMemory.selectVariant_eq_of_observations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.selectVariant_eq_of_observations

/-- info: 'TrustIr.AggregateMemory.EnumDecodingSelects.iff_of_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecodingSelects.iff_of_observations

/-- info: 'TrustIr.AggregateMemory.decode_leaf_eq_of_observations' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decode_leaf_eq_of_observations

/-- info: 'TrustIr.AggregateMemory.ChildDecoded.leaf_iff_of_observations' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ChildDecoded.leaf_iff_of_observations

/-- info: 'TrustIr.integer_child_leaf_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.integer_child_leaf_bytes

/-- info: 'TrustIr.integer_child_readback_of_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.integer_child_readback_of_encoded

/-- info: 'TrustIr.AggregateMemory.FieldsEncoded.child_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsEncoded.child_lane

/-- info: 'TrustIr.AggregateMemory.ByteLane.integer_child_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteLane.integer_child_readback

/-- info: 'TrustIr.AggregateMemory.field_integer_child_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.field_integer_child_readback

/-- info: 'TrustIr.AggregateMemory.prepared_field_integer_child_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_field_integer_child_readback

/-- info: 'TrustIr.AggregateMemory.array_integer_child_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.array_integer_child_readback

/-- info: 'TrustIr.AggregateMemory.enum_integer_child_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.enum_integer_child_readback

/-- info: 'TrustIr.AggregateMemory.prepared_enum_integer_child_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_enum_integer_child_readback

/-- info: 'TrustIr.AggregateMemory.IntegerReadbackControls.actual_parent_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.IntegerReadbackControls.actual_parent_store

/-- info: 'TrustIr.AggregateMemory.IntegerReadbackControls.stored_field_readback_without_parent_load' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.IntegerReadbackControls.stored_field_readback_without_parent_load

/-- info: 'TrustIr.AggregateMemory.IntegerReadbackControls.negative_target32_child' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.IntegerReadbackControls.negative_target32_child

/-- info: 'TrustIr.AggregateMemory.IntegerReadbackControls.nested_surrogate_is_raw' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.IntegerReadbackControls.nested_surrogate_is_raw

/-- info: 'TrustIr.AggregateMemory.IntegerReadbackControls.top_surrogate_still_refuses' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.IntegerReadbackControls.top_surrogate_still_refuses

/-- info: 'TrustIr.AggregateMemory.IntegerReadbackControls.scalar_storage_shape_does_not_change_result' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.IntegerReadbackControls.scalar_storage_shape_does_not_change_result

/-- info: 'TrustIr.AggregateMemory.IntegerReadbackControls.missing_scalar_byte_still_refuses' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.IntegerReadbackControls.missing_scalar_byte_still_refuses

/-- info: 'TrustIr.AggregateMemory.IntegerReadbackControls.extent_is_independent_of_total_byte_reads' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.IntegerReadbackControls.extent_is_independent_of_total_byte_reads

/-- info: 'TrustIr.AggregateMemory.IntegerReadbackControls.clipped_empty_windows_keep_observations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.IntegerReadbackControls.clipped_empty_windows_keep_observations

/-- info: 'TrustIr.AggregateMemory.IntegerReadbackControls.million_uniform_slot_readback' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.IntegerReadbackControls.million_uniform_slot_readback

/-- info: 'TrustIr.AggregateMemory.FieldsDecoded.cons' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsDecoded.cons

/-- info: 'TrustIr.AggregateMemory.FieldsDecoded.of_get' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsDecoded.of_get

/-- info: 'TrustIr.AggregateMemory.decode_fields_of_children' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decode_fields_of_children

/-- info: 'TrustIr.AggregateMemory.ChildDecoded.fields_of_children' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ChildDecoded.fields_of_children

/-- info: 'TrustIr.AggregateMemory.VariantDecoded.of_fields' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VariantDecoded.of_fields

/-- info: 'TrustIr.AggregateMemory.decode_enumeration_of_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decode_enumeration_of_payload

/-- info: 'TrustIr.AggregateMemory.ChildDecoded.enumeration_of_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ChildDecoded.enumeration_of_payload

/-- info: 'TrustIr.AggregateMemory.EnumDecodingSelects.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecodingSelects.bound

/-- info: 'TrustIr.AggregateMemory.EnumDecodingSelects.discriminant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EnumDecodingSelects.discriminant

/-- info: 'TrustIr.AggregateMemory.IntegerFieldReadback.length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.IntegerFieldReadback.length

/-- info: 'TrustIr.AggregateMemory.IntegerFieldReadback.at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.IntegerFieldReadback.at

/-- info: 'TrustIr.AggregateMemory.IntegerFieldReadback.fields_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.IntegerFieldReadback.fields_decoded

/-- info: 'TrustIr.AggregateMemory.integer_fields_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.integer_fields_decode

/-- info: 'TrustIr.AggregateMemory.prepared_integer_fields_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_integer_fields_decode

/-- info: 'TrustIr.AggregateMemory.IntegerFieldReadback.enum_payload_decoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.IntegerFieldReadback.enum_payload_decoded

/-- info: 'TrustIr.AggregateMemory.prepared_enum_capture_integer_decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_enum_capture_integer_decode

/-- info: 'TrustIr.AggregateMemory.integer_fields_child_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.integer_fields_child_decode

/-- info: 'TrustIr.AggregateMemory.ParentDecoderControls.actual_parent_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ParentDecoderControls.actual_parent_store

/-- info: 'TrustIr.AggregateMemory.ParentDecoderControls.whole_prepared_parent_load' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ParentDecoderControls.whole_prepared_parent_load

/-- info: 'TrustIr.AggregateMemory.ParentDecoderControls.parent_padding_stays_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ParentDecoderControls.parent_padding_stays_absent

/-- info: 'TrustIr.AggregateMemory.ParentDecoderControls.strict_nested_parent_load' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ParentDecoderControls.strict_nested_parent_load

/-- info: 'TrustIr.AggregateMemory.ParentDecoderControls.logical_outputs_are_normalized' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ParentDecoderControls.logical_outputs_are_normalized

/-- info: 'TrustIr.AggregateMemory.ParentDecoderControls.empty_product_parent_load' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ParentDecoderControls.empty_product_parent_load

/-- info: 'TrustIr.AggregateMemory.ParentDecoderControls.integer_relation_has_no_missing_outputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ParentDecoderControls.integer_relation_has_no_missing_outputs

/-- info: 'TrustIr.AggregateMemory.ParentDecoderControls.bool_is_not_silently_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ParentDecoderControls.bool_is_not_silently_covered

/-- info: 'TrustIr.AggregateMemory.ParentDecoderControls.successful_child_does_not_erase_parent_extent_check' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ParentDecoderControls.successful_child_does_not_erase_parent_extent_check

/-- info: 'TrustIr.AggregateMemory.ParentDecoderControls.selection_cannot_invent_discriminant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ParentDecoderControls.selection_cannot_invent_discriminant

/-- info: 'TrustIr.AggregateMemory.ParentDecoderControls.actual_enum_payload_run' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ParentDecoderControls.actual_enum_payload_run

/-- info: 'TrustIr.AggregateMemory.ParentDecoderControls.whole_enum_load_from_payload_success' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ParentDecoderControls.whole_enum_load_from_payload_success

/-- info: 'TrustIr.AggregateMemory.ParentDecoderControls.strict_nested_enum_load' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ParentDecoderControls.strict_nested_enum_load

/-- info: 'TrustIr.AggregateMemory.ParentDecoderControls.checked_capture_whole_enum_load' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ParentDecoderControls.checked_capture_whole_enum_load

/-- info: 'TrustIr.CompactArray.Leaf.get_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.CompactArray.Leaf.get_exists

/-- info: 'TrustIr.CompactArray.Tree.get_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.CompactArray.Tree.get_exists

/-- info: 'TrustIr.CompactArray.Packed.get_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.CompactArray.Packed.get_exists

/-- info: 'TrustIr.ByteImage.BlockResult.map_error' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ByteImage.BlockResult.map_error

/-- info: 'TrustIr.ByteImage.FailedSlots.congr' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ByteImage.FailedSlots.congr

/-- info: 'TrustIr.ByteImage.FailedSlots.of_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.FailedSlots.of_window

/-- info: 'TrustIr.ByteImage.mapBlocksSpec_failure_of_periods' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.mapBlocksSpec_failure_of_periods

/-- info: 'TrustIr.ByteImage.mapBlocksSpec_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.mapBlocksSpec_failure

/-- info: 'TrustIr.ByteImage.mapBlocks_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.mapBlocks_failure

/-- info: 'TrustIr.ByteImage.mapBlocks_exists_of_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.mapBlocks_exists_of_windows

/-- info: 'TrustIr.ByteImage.MapperFailureControls.visible_callback_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.MapperFailureControls.visible_callback_failure

/-- info: 'TrustIr.ByteImage.MapperFailureControls.visible_failure_has_actual_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.MapperFailureControls.visible_failure_has_actual_slot

/-- info: 'TrustIr.ByteImage.MapperFailureControls.hidden_template_error_is_not_forced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.MapperFailureControls.hidden_template_error_is_not_forced

/-- info: 'TrustIr.ByteImage.MapperFailureControls.zero_count_does_not_call_failing_callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.MapperFailureControls.zero_count_does_not_call_failing_callback

/-- info: 'TrustIr.ByteImage.MapperFailureControls.zero_width_callback_failure_has_visible_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.MapperFailureControls.zero_width_callback_failure_has_visible_slot

/-- info: 'TrustIr.ByteImage.MapperFailureControls.wrong_extent_has_no_complete_failure_window' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.MapperFailureControls.wrong_extent_has_no_complete_failure_window

/-- info: 'TrustIr.AggregateMemory.ChildDecoded.functional' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ChildDecoded.functional

/-- info: 'TrustIr.AggregateMemory.decode_array_exists_of_mapper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decode_array_exists_of_mapper

/-- info: 'TrustIr.AggregateMemory.ChildDecoded.array_exists_of_mapper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ChildDecoded.array_exists_of_mapper

/-- info: 'TrustIr.AggregateMemory.ChildDecoded.array_iff_decode' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ChildDecoded.array_iff_decode

/-- info: 'TrustIr.AggregateMemory.encode_array_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_array_geometry

/-- info: 'TrustIr.AggregateMemory.decode_array_exists_of_children' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.decode_array_exists_of_children

/-- info: 'TrustIr.AggregateMemory.ChildDecoded.array_exists_of_children' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ChildDecoded.array_exists_of_children

/-- info: 'TrustIr.AggregateMemory.ByteLane.integer_window_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteLane.integer_window_readback

/-- info: 'TrustIr.AggregateMemory.integer_array_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.integer_array_decode

/-- info: 'TrustIr.AggregateMemory.integer_array_child_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.integer_array_child_decode

/-- info: 'TrustIr.AggregateMemory.ArrayParentControls.million_uniform_parent_decode' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayParentControls.million_uniform_parent_decode

/-- info: 'TrustIr.AggregateMemory.ArrayParentControls.dense_parent_decode' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayParentControls.dense_parent_decode

/-- info: 'TrustIr.AggregateMemory.ArrayParentControls.split_parent_decode' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayParentControls.split_parent_decode

/-- info: 'TrustIr.AggregateMemory.ArrayParentControls.shifted_periodic_parent_decode' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayParentControls.shifted_periodic_parent_decode

/-- info: 'TrustIr.AggregateMemory.ArrayParentControls.empty_array_does_not_force_hidden_poison' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayParentControls.empty_array_does_not_force_hidden_poison

/-- info: 'TrustIr.AggregateMemory.ArrayParentControls.zero_stride_parent_keeps_logical_count' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayParentControls.zero_stride_parent_keeps_logical_count

/-- info: 'TrustIr.AggregateMemory.ArrayParentControls.nested_zero_stride_parent_keeps_mode' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayParentControls.nested_zero_stride_parent_keeps_mode

/-- info: 'TrustIr.AggregateMemory.ArrayParentControls.clipped_periodic_array_does_not_force_hidden_poison' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ArrayParentControls.clipped_periodic_array_does_not_force_hidden_poison

/-- info: 'TrustIr.AggregateMemory.ChildDecoded.leaf_iff_decode' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ChildDecoded.leaf_iff_decode

/-- info: 'TrustIr.AggregateMemory.ChildDecoded.ordinary_iff_decode' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ChildDecoded.ordinary_iff_decode

/-- info: 'TrustIr.AggregateMemory.ScalarReadbackInput.readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarReadbackInput.readback

/-- info: 'TrustIr.AggregateMemory.ByteLane.of_parent_observations' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteLane.of_parent_observations

/-- info: 'TrustIr.AggregateMemory.ByteLane.window_bytes' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteLane.window_bytes

/-- info: 'TrustIr.AggregateMemory.ByteLane.slice_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ByteLane.slice_bytes

/-- info: 'TrustIr.AggregateMemory.ValueReadback.aggregate_nil' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ValueReadback.aggregate_nil

/-- info: 'TrustIr.AggregateMemory.ValueReadback.aggregate_cons' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ValueReadback.aggregate_cons

/-- info: 'TrustIr.AggregateMemory.ReadbackInput.readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ReadbackInput.readback

/-- info: 'TrustIr.AggregateMemory.ScalarReadbackInput.character_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarReadbackInput.character_view

/-- info: 'TrustIr.AggregateMemory.ScalarReadbackInput.top_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarReadbackInput.top_readback

/-- info: 'TrustIr.AggregateMemory.ReadbackInput.top_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ReadbackInput.top_readback

/-- info: 'TrustIr.AggregateMemory.prepared_recursive_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_recursive_readback

/-- info: 'TrustIr.AggregateMemory.prepared_recursive_child_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_recursive_child_readback

/-- info: 'TrustIr.AggregateMemory.FieldReadbackInputs.length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldReadbackInputs.length

/-- info: 'TrustIr.AggregateMemory.FieldReadbackInputs.at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldReadbackInputs.at

/-- info: 'TrustIr.AggregateMemory.ReadbackInput.fields_of_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ReadbackInput.fields_of_pairs

/-- info: 'TrustIr.AggregateMemory.ReadbackInput.array_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ReadbackInput.array_uniform

/-- info: 'TrustIr.AggregateMemory.source_image_observations' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.source_image_observations

/-- info: 'TrustIr.AggregateMemory.ReadbackInput.enumeration_of_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ReadbackInput.enumeration_of_prefix

/-- info: 'TrustIr.AggregateMemory.RecursiveReadbackControls.prepared_mixed_recursive_readback' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.RecursiveReadbackControls.prepared_mixed_recursive_readback

/-- info: 'TrustIr.AggregateMemory.RecursiveReadbackControls.mixed_nested_recursive_readback' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.RecursiveReadbackControls.mixed_nested_recursive_readback

/-- info: 'TrustIr.AggregateMemory.RecursiveReadbackControls.distinct_byte_representation_readback' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.RecursiveReadbackControls.distinct_byte_representation_readback

/-- info: 'TrustIr.AggregateMemory.RecursiveReadbackControls.nested_pointer_uses_receiving_memory' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.RecursiveReadbackControls.nested_pointer_uses_receiving_memory

/-- info: 'TrustIr.AggregateMemory.RecursiveReadbackControls.fat_metadata_uses_declared_kind' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.RecursiveReadbackControls.fat_metadata_uses_declared_kind

/-- info: 'TrustIr.AggregateMemory.RecursiveReadbackControls.nested_zero_pointer_canonicalizes' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.RecursiveReadbackControls.nested_zero_pointer_canonicalizes

/-- info: 'TrustIr.AggregateMemory.RecursiveReadbackControls.nested_surrogate_stays_raw' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.RecursiveReadbackControls.nested_surrogate_stays_raw

/-- info: 'TrustIr.AggregateMemory.RecursiveReadbackControls.outer_padding_remains_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.RecursiveReadbackControls.outer_padding_remains_absent

/-- info: 'TrustIr.AggregateMemory.RecursiveReadbackControls.arrays_of_mixed_arrays_readback' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.RecursiveReadbackControls.arrays_of_mixed_arrays_readback

/-- info: 'TrustIr.AggregateMemory.RecursiveReadbackControls.recursive_enum_payload_readback' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.RecursiveReadbackControls.recursive_enum_payload_readback

/-- info: 'TrustIr.AggregateMemory.RecursiveReadbackControls.valid_top_character_readback' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.RecursiveReadbackControls.valid_top_character_readback

/-- info: 'TrustIr.AggregateMemory.RecursiveReadbackControls.invalid_top_character_has_no_ready_certificate' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.RecursiveReadbackControls.invalid_top_character_has_no_ready_certificate

/-- info: 'TrustIr.AggregateMemory.RecursiveReadbackControls.invalid_top_character_still_refuses' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.RecursiveReadbackControls.invalid_top_character_still_refuses

/-- info: 'TrustIr.AggregateMemory.RecursiveReadbackControls.float_is_not_implicitly_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.RecursiveReadbackControls.float_is_not_implicitly_admitted

/-- info: 'TrustIr.AggregateMemory.RecursiveReadbackControls.unwritten_is_not_implicitly_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.RecursiveReadbackControls.unwritten_is_not_implicitly_admitted

/-- info: 'TrustIr.AggregateMemory.RecursiveReadbackControls.target32_overflow_has_no_scalar_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.RecursiveReadbackControls.target32_overflow_has_no_scalar_certificate

/-- info: 'TrustIr.AggregateMemory.RecursiveReadbackControls.uninitialized_carrier_has_no_selection_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.RecursiveReadbackControls.uninitialized_carrier_has_no_selection_certificate

/-- info: 'TrustIr.AggregateMemory.RecursiveReadbackControls.overlapping_plan_has_no_source_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.RecursiveReadbackControls.overlapping_plan_has_no_source_origin

-- Function-word aggregate readback and contextual refusal controls.

/-- info: 'TrustIr.AggregateMemory.encode_function_leaf_of_memory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_function_leaf_of_memory

/-- info: 'TrustIr.AggregateMemory.function_aggregate_leaf_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.function_aggregate_leaf_roundtrip

/-- info: 'TrustIr.AggregateMemory.null_function_aggregate_leaf_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.null_function_aggregate_leaf_roundtrip

/-- info: 'TrustIr.AggregateMemory.FunctionReadbackInput.codec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FunctionReadbackInput.codec

/-- info: 'TrustIr.AggregateMemory.ReadbackInput.readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ReadbackInput.readback

/-- info: 'TrustIr.AggregateMemory.ReadbackInput.top_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ReadbackInput.top_readback

/-- info: 'TrustIr.AggregateMemory.prepared_recursive_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_recursive_readback

/-- info: 'TrustIr.AggregateMemory.prepared_recursive_child_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_recursive_child_readback

/-- info: 'TrustIr.AggregateMemory.FunctionReadbackControls.prepared_record_and_function_array' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FunctionReadbackControls.prepared_record_and_function_array

/-- info: 'TrustIr.AggregateMemory.FunctionReadbackControls.target32_function_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FunctionReadbackControls.target32_function_readback

/-- info: 'TrustIr.AggregateMemory.FunctionReadbackControls.duplicate_table_uses_first_position' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FunctionReadbackControls.duplicate_table_uses_first_position

/-- info: 'TrustIr.AggregateMemory.FunctionReadbackControls.changed_table_changes_target' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FunctionReadbackControls.changed_table_changes_target

/-- info: 'TrustIr.AggregateMemory.FunctionReadbackControls.missing_table_refuses_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FunctionReadbackControls.missing_table_refuses_store

/-- info: 'TrustIr.AggregateMemory.FunctionReadbackControls.missing_target_refuses_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FunctionReadbackControls.missing_target_refuses_store

/-- info: 'TrustIr.AggregateMemory.FunctionReadbackControls.mismatched_signature_refuses_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FunctionReadbackControls.mismatched_signature_refuses_store

/-- info: 'TrustIr.AggregateMemory.FunctionReadbackControls.unknown_word_refuses_load' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FunctionReadbackControls.unknown_word_refuses_load

/-- info: 'TrustIr.AggregateMemory.FunctionReadbackControls.null_without_table_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FunctionReadbackControls.null_without_table_readback

/-- info: 'TrustIr.AggregateMemory.FunctionReadbackControls.missing_table_has_no_function_certificate' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FunctionReadbackControls.missing_table_has_no_function_certificate

-- Admission recovered from actual successful ordinary stores.

/-- info: 'TrustIr.AggregateMemory.encode_leaf_memory_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_leaf_memory_success

/-- info: 'TrustIr.AggregateMemory.functionAddressOf_success' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.functionAddressOf_success

/-- info: 'TrustIr.AggregateMemory.FunctionReadbackInput.of_memory_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FunctionReadbackInput.of_memory_success

/-- info: 'TrustIr.AggregateMemory.FunctionReadbackInput.of_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FunctionReadbackInput.of_encoded

/-- info: 'TrustIr.AggregateMemory.ReadbackInput.function_of_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ReadbackInput.function_of_encoded

/-- info: 'TrustIr.AggregateMemory.encoded_function_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encoded_function_readback

/-- info: 'TrustIr.AggregateMemory.FieldsEncoded.readback_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsEncoded.readback_inputs

/-- info: 'TrustIr.AggregateMemory.ReadbackInput.fields_of_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ReadbackInput.fields_of_encoded

/-- info: 'TrustIr.AggregateMemory.ReadbackInput.array_of_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ReadbackInput.array_of_encoded

/-- info: 'TrustIr.AggregateMemory.FunctionReadbackPlan.admit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FunctionReadbackPlan.admit

/-- info: 'TrustIr.AggregateMemory.prepared_function_plan_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_function_plan_readback

/-- info: 'TrustIr.AggregateMemory.EncodedAdmissionControls.parent_store_supplies_recursive_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EncodedAdmissionControls.parent_store_supplies_recursive_admission

/-- info: 'TrustIr.AggregateMemory.EncodedAdmissionControls.prepared_parent_readback_without_value_certificates' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EncodedAdmissionControls.prepared_parent_readback_without_value_certificates

/-- info: 'TrustIr.AggregateMemory.EncodedAdmissionControls.target32_store_supplies_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EncodedAdmissionControls.target32_store_supplies_admission

/-- info: 'TrustIr.AggregateMemory.EncodedAdmissionControls.distinct_image_exact_function_readback' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EncodedAdmissionControls.distinct_image_exact_function_readback

/-- info: 'TrustIr.AggregateMemory.EncodedAdmissionControls.table_free_null_store_supplies_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EncodedAdmissionControls.table_free_null_store_supplies_admission

/-- info: 'TrustIr.AggregateMemory.EncodedAdmissionControls.missing_table_cannot_supply_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EncodedAdmissionControls.missing_table_cannot_supply_store

/-- info: 'TrustIr.AggregateMemory.EncodedAdmissionControls.mismatched_signature_cannot_supply_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EncodedAdmissionControls.mismatched_signature_cannot_supply_store

/-- info: 'TrustIr.AggregateMemory.EncodedAdmissionControls.wrong_extent_cannot_supply_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EncodedAdmissionControls.wrong_extent_cannot_supply_store

/-- info: 'TrustIr.AggregateMemory.EncodedAdmissionControls.empty_array_ignores_unused_unwritten_template' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.EncodedAdmissionControls.empty_array_ignores_unused_unwritten_template

-- Scalar admission from actual lane checks and successful stores.

/-- info: 'TrustIr.AggregateMemory.encode_leaf_fat_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_leaf_fat_valid

/-- info: 'TrustIr.AggregateMemory.checked_integer_lane_shape' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.checked_integer_lane_shape

/-- info: 'TrustIr.AggregateMemory.checked_pointer_lane_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.checked_pointer_lane_shape

/-- info: 'TrustIr.AggregateMemory.ScalarReadbackInput.integer_of_checked_encoded' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarReadbackInput.integer_of_checked_encoded

/-- info: 'TrustIr.AggregateMemory.ScalarReadbackInput.pointer_of_checked_encoded' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarReadbackInput.pointer_of_checked_encoded

/-- info: 'TrustIr.AggregateMemory.ScalarReadbackInput.boolean_of_checked' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarReadbackInput.boolean_of_checked

/-- info: 'TrustIr.AggregateMemory.ScalarReadbackInput.unit_of_checked' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarReadbackInput.unit_of_checked

/-- info: 'TrustIr.AggregateMemory.metadata_length64_shape' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.metadata_length64_shape

/-- info: 'TrustIr.AggregateMemory.metadata_length32_shape' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.metadata_length32_shape

/-- info: 'TrustIr.AggregateMemory.metadata_pointer64_shape' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.metadata_pointer64_shape

/-- info: 'TrustIr.AggregateMemory.metadata_pointer32_shape' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.metadata_pointer32_shape

/-- info: 'TrustIr.AggregateMemory.checked_fat_metadata_shape' depends on axioms: [Classical.choice, propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.checked_fat_metadata_shape

/-- info: 'TrustIr.AggregateMemory.fat_store_guard_shape' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.fat_store_guard_shape

/-- info: 'TrustIr.AggregateMemory.ScalarReadbackInput.fat_of_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarReadbackInput.fat_of_encoded

/-- info: 'TrustIr.AggregateMemory.ScalarReadbackPlan.input_certificate' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarReadbackPlan.input_certificate

/-- info: 'TrustIr.AggregateMemory.ScalarReadbackPlan.admit' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarReadbackPlan.admit

/-- info: 'TrustIr.AggregateMemory.ScalarReadbackPlan.readback' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarReadbackPlan.readback

/-- info: 'TrustIr.AggregateMemory.top_char_ready_of_checked_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.top_char_ready_of_checked_closure

/-- info: 'TrustIr.AggregateMemory.ScalarReadbackPlan.readback_of_checked_closure' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarReadbackPlan.readback_of_checked_closure

/-- info: 'TrustIr.AggregateMemory.ScalarAdmissionControls.integer_store_and_lane_check_supply_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarAdmissionControls.integer_store_and_lane_check_supply_admission

/-- info: 'TrustIr.AggregateMemory.ScalarAdmissionControls.target32_signed_transport_supplies_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarAdmissionControls.target32_signed_transport_supplies_admission

/-- info: 'TrustIr.AggregateMemory.ScalarAdmissionControls.distinct_byte_image_integer_readback' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarAdmissionControls.distinct_byte_image_integer_readback

/-- info: 'TrustIr.AggregateMemory.ScalarAdmissionControls.pointer_store_supplies_width_and_extent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarAdmissionControls.pointer_store_supplies_width_and_extent

/-- info: 'TrustIr.AggregateMemory.ScalarAdmissionControls.zero_pointer_canonical_readback' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarAdmissionControls.zero_pointer_canonical_readback

/-- info: 'TrustIr.AggregateMemory.ScalarAdmissionControls.boolean_checker_supplies_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarAdmissionControls.boolean_checker_supplies_admission

/-- info: 'TrustIr.AggregateMemory.ScalarAdmissionControls.unit_checker_supplies_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarAdmissionControls.unit_checker_supplies_admission

/-- info: 'TrustIr.AggregateMemory.ScalarAdmissionControls.target32_length_store_supplies_metadata_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarAdmissionControls.target32_length_store_supplies_metadata_admission

/-- info: 'TrustIr.AggregateMemory.ScalarAdmissionControls.vtable_store_supplies_both_address_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarAdmissionControls.vtable_store_supplies_both_address_bounds

/-- info: 'TrustIr.AggregateMemory.ScalarAdmissionControls.null_vtable_store_supplies_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarAdmissionControls.null_vtable_store_supplies_admission

/-- info: 'TrustIr.AggregateMemory.ScalarAdmissionControls.pointer_byte_storage_does_not_authenticate_lane' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarAdmissionControls.pointer_byte_storage_does_not_authenticate_lane

/-- info: 'TrustIr.AggregateMemory.ScalarAdmissionControls.boolean_byte_storage_does_not_authenticate_lane' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarAdmissionControls.boolean_byte_storage_does_not_authenticate_lane

/-- info: 'TrustIr.AggregateMemory.ScalarAdmissionControls.target32_pointer_lane_check_does_not_waive_overflow' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarAdmissionControls.target32_pointer_lane_check_does_not_waive_overflow

/-- info: 'TrustIr.AggregateMemory.ScalarAdmissionControls.wrong_fat_metadata_still_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarAdmissionControls.wrong_fat_metadata_still_refuses

/-- info: 'TrustIr.AggregateMemory.ScalarAdmissionControls.nested_surrogate_has_checked_store_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarAdmissionControls.nested_surrogate_has_checked_store_admission

/-- info: 'TrustIr.AggregateMemory.ScalarAdmissionControls.recursive_checker_supplies_valid_top_character' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarAdmissionControls.recursive_checker_supplies_valid_top_character

/-- info: 'TrustIr.AggregateMemory.ScalarAdmissionControls.recursive_checker_refuses_surrogate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarAdmissionControls.recursive_checker_refuses_surrogate

/-- info: 'TrustIr.AggregateMemory.ScalarAdmissionControls.top_surrogate_load_still_refuses' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarAdmissionControls.top_surrogate_load_still_refuses

/-- info: 'TrustIr.AggregateMemory.ScalarAdmissionControls.float_has_no_implicit_scalar_plan' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarAdmissionControls.float_has_no_implicit_scalar_plan

-- Real recursive source checking derives visible admission through source-bound tuples and arrays.

/-- info: 'TrustIr.AggregateMemory.closure_checked_integer_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.closure_checked_integer_lane

/-- info: 'TrustIr.AggregateMemory.closure_checked_pointer_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.closure_checked_pointer_lane

/-- info: 'TrustIr.AggregateMemory.closure_checked_boolean_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.closure_checked_boolean_lane

/-- info: 'TrustIr.AggregateMemory.closure_checked_unit_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.closure_checked_unit_lane

/-- info: 'TrustIr.AggregateMemory.ScalarReadbackPlan.input_of_source_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarReadbackPlan.input_of_source_checked

/-- info: 'TrustIr.AggregateMemory.ScalarReadbackPlan.admit_of_source_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarReadbackPlan.admit_of_source_checked

/-- info: 'TrustIr.AggregateMemory.encode_ordinary_not_uninit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_ordinary_not_uninit

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.tuple_types_and_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.tuple_types_and_children

/-- info: 'TrustIr.AggregateMemory.list_zip_member_of_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.list_zip_member_of_get

/-- info: 'TrustIr.AggregateMemory.SourceReadbackShape.admit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackShape.admit

/-- info: 'TrustIr.AggregateMemory.source_checked_recursive_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.source_checked_recursive_readback

/-- info: 'TrustIr.AggregateMemory.prepared_checked_value_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_checked_value_readback

/-- info: 'TrustIr.AggregateMemory.SourceCheckedAdmissionControls.actual_recursive_checker_accepts_mixed_parent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceCheckedAdmissionControls.actual_recursive_checker_accepts_mixed_parent

/-- info: 'TrustIr.AggregateMemory.SourceCheckedAdmissionControls.one_source_check_supplies_recursive_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceCheckedAdmissionControls.one_source_check_supplies_recursive_admission

/-- info: 'TrustIr.AggregateMemory.SourceCheckedAdmissionControls.prepared_mixed_source_readback' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceCheckedAdmissionControls.prepared_mixed_source_readback

/-- info: 'TrustIr.AggregateMemory.SourceCheckedAdmissionControls.reconstructed_source_image_readback' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceCheckedAdmissionControls.reconstructed_source_image_readback

/-- info: 'TrustIr.AggregateMemory.SourceCheckedAdmissionControls.recursive_checker_replaces_separate_scalar_lane_argument' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceCheckedAdmissionControls.recursive_checker_replaces_separate_scalar_lane_argument

/-- info: 'TrustIr.AggregateMemory.SourceCheckedAdmissionControls.empty_array_ignores_unsupported_unused_template_and_row' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceCheckedAdmissionControls.empty_array_ignores_unsupported_unused_template_and_row

/-- info: 'TrustIr.AggregateMemory.SourceCheckedAdmissionControls.tuple_transport_exception_does_not_supply_ordinary_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceCheckedAdmissionControls.tuple_transport_exception_does_not_supply_ordinary_store

/-- info: 'TrustIr.AggregateMemory.SourceCheckedAdmissionControls.partial_carriers_still_refuse_source_check_and_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceCheckedAdmissionControls.partial_carriers_still_refuse_source_check_and_store

/-- info: 'TrustIr.AggregateMemory.SourceCheckedAdmissionControls.byte_store_and_checker_do_not_authenticate_field_types' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceCheckedAdmissionControls.byte_store_and_checker_do_not_authenticate_field_types

/-- info: 'TrustIr.AggregateMemory.SourceCheckedAdmissionControls.forged_field_types_have_no_source_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceCheckedAdmissionControls.forged_field_types_have_no_source_origin

/-- info: 'TrustIr.AggregateMemory.SourceCheckedAdmissionControls.visible_array_row_disagreement_cannot_supply_shape' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceCheckedAdmissionControls.visible_array_row_disagreement_cannot_supply_shape

/-- info: 'TrustIr.AggregateMemory.SourceCheckedAdmissionControls.actual_checks_and_storage_do_not_waive_visible_row_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceCheckedAdmissionControls.actual_checks_and_storage_do_not_waive_visible_row_agreement

/-- info: 'TrustIr.AggregateMemory.SourceCheckedAdmissionControls.target32_source_checker_supplies_scalar_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceCheckedAdmissionControls.target32_source_checker_supplies_scalar_admission

/-- info: 'TrustIr.AggregateMemory.SourceCheckedAdmissionControls.actual_target32_recursive_checker_accepts_mixed_parent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceCheckedAdmissionControls.actual_target32_recursive_checker_accepts_mixed_parent

/-- info: 'TrustIr.AggregateMemory.SourceCheckedAdmissionControls.prepared_target32_mixed_source_readback' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceCheckedAdmissionControls.prepared_target32_mixed_source_readback

/-- info: 'TrustIr.SourceLayout.zip_fst_exact' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.zip_fst_exact

/-- info: 'TrustIr.SourceLayout.canonicalFields_steps_types' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.canonicalFields_steps_types

/-- info: 'TrustIr.SourceLayout.Equation.Executes.canonicalFields_types' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.canonicalFields_types

/-- info: 'TrustIr.SourceLayout.declaredFields_steps_types' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.declaredFields_steps_types

/-- info: 'TrustIr.SourceLayout.Equation.Executes.declaredFields_types' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.Executes.declaredFields_types

/-- info: 'TrustIr.SourceLayout.StructSourceAt.above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StructSourceAt.above

/-- info: 'TrustIr.SourceLayout.StructSourceAt.other_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StructSourceAt.other_slot

/-- info: 'TrustIr.SourceLayout.Equation.IndexedRule.struct_types' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Equation.IndexedRule.struct_types

/-- info: 'TrustIr.SourceLayout.Index.struct_selected_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Index.struct_selected_source

/-- info: 'TrustIr.SourceLayout.Session.Reachable.struct_origin_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.struct_origin_invariant

/-- info: 'TrustIr.SourceLayout.Session.CompiledRoot.struct_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.CompiledRoot.struct_selected

/-- info: 'TrustIr.SourceLayout.Session.Reachable.struct_value_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.struct_value_origin

/-- info: 'TrustIr.SourceLayout.Session.Reachable.query_struct_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.Reachable.query_struct_origin

/-- info: 'TrustIr.AggregateMemory.Plan.Origin.struct_types_and_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Plan.Origin.struct_types_and_children

/-- info: 'TrustIr.AggregateMemory.SourceNominalReadbackShape.admit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceNominalReadbackShape.admit

/-- info: 'TrustIr.AggregateMemory.source_checked_nominal_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.source_checked_nominal_readback

/-- info: 'TrustIr.AggregateMemory.prepared_checked_nominal_value_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_checked_nominal_value_readback

/-- info: 'TrustIr.AggregateMemory.SourceStructAdmissionControls.shape_selects_first_duplicate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceStructAdmissionControls.shape_selects_first_duplicate

/-- info: 'TrustIr.AggregateMemory.SourceStructAdmissionControls.execution_selects_matching_duplicate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceStructAdmissionControls.execution_selects_matching_duplicate

/-- info: 'TrustIr.AggregateMemory.SourceStructAdmissionControls.execution_selects_sparse_id' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceStructAdmissionControls.execution_selects_sparse_id

/-- info: 'TrustIr.AggregateMemory.SourceStructAdmissionControls.nested_structs_admitted_from_real_checker_and_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceStructAdmissionControls.nested_structs_admitted_from_real_checker_and_store

/-- info: 'TrustIr.AggregateMemory.SourceStructAdmissionControls.duplicate_context_disagreement_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceStructAdmissionControls.duplicate_context_disagreement_refused

/-- info: 'TrustIr.AggregateMemory.SourceStructAdmissionControls.actual_entry_checks_nested_structs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceStructAdmissionControls.actual_entry_checks_nested_structs

/-- info: 'TrustIr.AggregateMemory.SourceStructAdmissionControls.prepared_nested_struct_readback' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceStructAdmissionControls.prepared_nested_struct_readback

/-- info: 'TrustIr.AggregateMemory.SourceStructAdmissionControls.complete_external_image_readback' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceStructAdmissionControls.complete_external_image_readback

/-- info: 'TrustIr.AggregateMemory.SourceStructAdmissionControls.wrong_duplicate_row_fails_real_checker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceStructAdmissionControls.wrong_duplicate_row_fails_real_checker

/-- info: 'TrustIr.SourceLayout.TypesCompilation.length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.TypesCompilation.length

/-- info: 'TrustIr.SourceLayout.StructCompilation.field_types' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.StructCompilation.field_types

/-- info: 'TrustIr.SourceLayout.RootCompilation.struct_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.struct_selected

/-- info: 'TrustIr.SourceLayout.prepare_struct_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.prepare_struct_origin

/-- info: 'TrustIr.SourceLayout.RootCompilation.preserves_struct_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.RootCompilation.preserves_struct_origin

/-- info: 'TrustIr.SourceLayout.Session.query_preserves_struct_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.SourceLayout.Session.query_preserves_struct_origin

-- Executable source-bound readback policy: soundness, completeness and controls.
/-- info: 'TrustIr.AggregateMemory.selectedStructAgrees_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.selectedStructAgrees_sound

/-- info: 'TrustIr.AggregateMemory.sourceReadbackPolicy_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.sourceReadbackPolicy_sound

/-- info: 'TrustIr.AggregateMemory.scalarReadbackPolicy_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.scalarReadbackPolicy_complete

/-- info: 'TrustIr.AggregateMemory.sourceReadbackShape_policy_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.sourceReadbackShape_policy_complete

/-- info: 'TrustIr.AggregateMemory.selectedStructAgrees_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.selectedStructAgrees_complete

/-- info: 'TrustIr.AggregateMemory.sourceNominalReadbackShape_policy_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.sourceNominalReadbackShape_policy_complete

/-- info: 'TrustIr.AggregateMemory.sourceReadbackPolicy_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.sourceReadbackPolicy_iff

/-- info: 'TrustIr.AggregateMemory.prepared_policy_checked_value_readback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_policy_checked_value_readback

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.scalar_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.scalar_accepted

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.canonical_bool_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.canonical_bool_accepted

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.oversized_bool_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.oversized_bool_refused

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.misaligned_unit_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.misaligned_unit_refused

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.float_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.float_refused

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.pointer_vector_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.pointer_vector_refused

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.pointer_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.pointer_accepted

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.char_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.char_accepted

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.function_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.function_accepted

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.fat_pointer_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.fat_pointer_accepted

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.enumeration_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.enumeration_refused

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.record_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.record_refused

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.duplicate_selects_execution_row' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.duplicate_selects_execution_row

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.first_duplicate_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.first_duplicate_refused

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.full_row_metadata_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.full_row_metadata_bound

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.absent_nominal_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.absent_nominal_refused

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.absent_evaluator_row_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.absent_evaluator_row_refused

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.wrong_array_type_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.wrong_array_type_refused

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.absent_array_type_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.absent_array_type_refused

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.array_count_mismatch_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.array_count_mismatch_refused

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.unused_empty_template_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.unused_empty_template_accepted

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.unsupported_nested_child_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.unsupported_nested_child_refused

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.nested_nominal_policy_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.nested_nominal_policy_accepted

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.prepared_readback_without_manual_shape' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.prepared_readback_without_manual_shape

/-- info: 'TrustIr.AggregateMemory.SourceReadbackPolicyControls.real_origin_policy_equivalence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.SourceReadbackPolicyControls.real_origin_policy_equivalence

/-- info: 'TrustIr.AggregateMemory.instDecidableEqFieldDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.instDecidableEqFieldDef

/-- info: 'TrustIr.AggregateMemory.instDecidableEqStructRepr' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.instDecidableEqStructRepr

/-- info: 'TrustIr.AggregateMemory.instDecidableEqStructDef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.instDecidableEqStructDef

-- Exact float byte codec and ordinary-leaf failure correspondence.
/-- info: 'TrustIr.natToBytesLE_eq_integer_go' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.natToBytesLE_eq_integer_go

/-- info: 'TrustIr.natToBytesLE_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.natToBytesLE_length

/-- info: 'TrustIr.natOfBytesLE_eq_integer_go' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.natOfBytesLE_eq_integer_go

/-- info: 'TrustIr.natOfBytesLE_natToBytesLE' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.natOfBytesLE_natToBytesLE

/-- info: 'TrustIr.encodeFloatAt_nan_refuses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.encodeFloatAt_nan_refuses

/-- info: 'TrustIr.FloatStorageFormat.encode_success_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FloatStorageFormat.encode_success_iff

/-- info: 'TrustIr.FloatStorageFormat.encode_extent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FloatStorageFormat.encode_extent

/-- info: 'TrustIr.FloatStorageFormat.decode_success_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FloatStorageFormat.decode_success_iff

/-- info: 'TrustIr.FloatStorageFormat.encoded_byte_readback' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FloatStorageFormat.encoded_byte_readback

/-- info: 'TrustIr.AggregateMemory.encode_float_leaf_result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_float_leaf_result

/-- info: 'TrustIr.AggregateMemory.encode_float_leaf_nan_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_float_leaf_nan_refuses

/-- info: 'TrustIr.AggregateMemory.encode_float_leaf_wrong_extent' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_float_leaf_wrong_extent

/-- info: 'TrustIr.AggregateMemory.encode_float_leaf_success' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_float_leaf_success

/-- info: 'TrustIr.AggregateMemory.encode_float_leaf_error_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_float_leaf_error_iff

/-- info: 'TrustIr.AggregateMemory.float_leaf_stored_byte_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.float_leaf_stored_byte_view

/-- info: 'TrustIr.FloatStorageControls.little_endian_binary16' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.little_endian_binary16

/-- info: 'TrustIr.FloatStorageControls.little_endian_binary32' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.little_endian_binary32

/-- info: 'TrustIr.FloatStorageControls.little_endian_binary64' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.little_endian_binary64

/-- info: 'TrustIr.FloatStorageControls.low_bytes_only' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.low_bytes_only

/-- info: 'TrustIr.FloatStorageControls.full_binary16_residue' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.full_binary16_residue

/-- info: 'TrustIr.FloatStorageControls.empty_byte_residue' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.empty_byte_residue

/-- info: 'TrustIr.FloatStorageControls.binary16_decode_truncated_refuses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.binary16_decode_truncated_refuses

/-- info: 'TrustIr.FloatStorageControls.binary32_decode_oversized_refuses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.binary32_decode_oversized_refuses

/-- info: 'TrustIr.FloatStorageControls.binary64_decode_truncated_refuses' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.binary64_decode_truncated_refuses

/-- info: 'TrustIr.FloatStorageControls.binary16_decode_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.binary16_decode_bytes

/-- info: 'TrustIr.FloatStorageControls.binary32_decode_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.binary32_decode_bytes

/-- info: 'TrustIr.FloatStorageControls.binary64_decode_bytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.binary64_decode_bytes

/-- info: 'TrustIr.FloatStorageControls.nan_precedes_untyped_width' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.nan_precedes_untyped_width

/-- info: 'TrustIr.FloatStorageControls.nan_precedes_layout_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.nan_precedes_layout_failure

/-- info: 'TrustIr.FloatStorageControls.ordinary_f64_layout_refuses' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.ordinary_f64_layout_refuses

/-- info: 'TrustIr.FloatStorageControls.ordinary_f16_image' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.ordinary_f16_image

/-- info: 'TrustIr.FloatStorageControls.ordinary_f32_image' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.ordinary_f32_image

/-- info: 'TrustIr.FloatStorageControls.ordinary_f64_image' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.ordinary_f64_image

/-- info: 'TrustIr.FloatStorageControls.successful_f32_store_supplies_byte_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.successful_f32_store_supplies_byte_view

/-- info: 'TrustIr.FloatStorageControls.ordinary_f16_error_correspondence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.ordinary_f16_error_correspondence

/-- info: 'TrustIr.FloatStorageControls.numeric_readback_policy_not_promoted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.FloatStorageControls.numeric_readback_policy_not_promoted

/-- info: 'TrustIr.AggregateMemory.encode_float_leaf_of_type' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_float_leaf_of_type

-- Packed integer/Bool vector codecs and automatic recursive admission.
/-- info: 'TrustIr.VectorReadbackLane.byte_size' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.VectorReadbackLane.byte_size

/-- info: 'TrustIr.vectorReadbackLane_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.vectorReadbackLane_iff

/-- info: 'TrustIr.vector_integer_lane_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.vector_integer_lane_bytes

/-- info: 'TrustIr.vector_integer_lane_decodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.vector_integer_lane_decodes

/-- info: 'TrustIr.vector_lane_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.vector_lane_roundtrip

/-- info: 'TrustIr.encodeVectorLane_extent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.encodeVectorLane_extent

/-- info: 'TrustIr.vector_lanes_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.vector_lanes_roundtrip

/-- info: 'TrustIr.vector_lane_ready_of_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.vector_lane_ready_of_checked

/-- info: 'TrustIr.vector_source_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.vector_source_checked

/-- info: 'TrustIr.encodeScalarVectorAt_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.encodeScalarVectorAt_steps

/-- info: 'TrustIr.vector_lane_ready_of_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.vector_lane_ready_of_encoded

/-- info: 'TrustIr.vector_lanes_ready_of_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.vector_lanes_ready_of_encoded

/-- info: 'TrustIr.vector_codec_readback_of_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.vector_codec_readback_of_encoded

/-- info: 'TrustIr.checked_vector_codec_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.checked_vector_codec_readback

/-- info: 'TrustIr.checked_immediate_vector_shape' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.checked_immediate_vector_shape

/-- info: 'TrustIr.AggregateMemory.vector_leaf_admission_of_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.vector_leaf_admission_of_encoded

/-- info: 'TrustIr.AggregateMemory.vector_child_readback_of_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.vector_child_readback_of_encoded

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.all_fixed_lanes_classified' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.all_fixed_lanes_classified

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.boolean_mask_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.boolean_mask_image

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.vector_and_scalar_boolean_images_differ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.vector_and_scalar_boolean_images_differ

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.signed_lane_residue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.signed_lane_residue

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.signed_lane_readback' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.signed_lane_readback

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.u16_little_endian' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.u16_little_endian

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.u64_full_width' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.u64_full_width

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.unchecked_lane_wraps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.unchecked_lane_wraps

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.source_rejects_unbounded_lane' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.source_rejects_unbounded_lane

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.wrong_lane_width_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.wrong_lane_width_refused

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.boolean_integer_carrier_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.boolean_integer_carrier_refused

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.zero_count_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.zero_count_refused

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.wrong_lane_count_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.wrong_lane_count_refused

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.trailing_bytes_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.trailing_bytes_refused

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.truncated_bytes_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.truncated_bytes_refused

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.pointer_lane_refused' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.pointer_lane_refused

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.target_sized_lane_refused' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.target_sized_lane_refused

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.wide_lane_refused' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.wide_lane_refused

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.float_lane_refused' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.float_lane_refused

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.nested_lane_refused' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.nested_lane_refused

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.wrong_width_certificate_impossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.wrong_width_certificate_impossible

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.zero_count_certificate_impossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.zero_count_certificate_impossible

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.wrong_extent_certificate_impossible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.wrong_extent_certificate_impossible

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.checked_boolean_vector_reloads' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.checked_boolean_vector_reloads

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.nested_policy_computed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.nested_policy_computed

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.prepared_nested_vectors_readback' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.prepared_nested_vectors_readback

/-- info: 'TrustIr.AggregateMemory.VectorReadbackControls.complete_receiving_window_readback' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.VectorReadbackControls.complete_receiving_window_readback

/-- info: 'TrustIr.vectorReadbackLane' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.vectorReadbackLane

/-- info: 'TrustIr.VectorLaneReady' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.VectorLaneReady

/-- info: 'TrustIr.vectorLaneResult' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.vectorLaneResult

/-- info: 'TrustIr.AggregateMemory.ValueReadback.vector' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ValueReadback.vector

/-- info: 'TrustIr.AggregateMemory.ScalarReadbackInput.vector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarReadbackInput.vector

/-- info: 'TrustIr.AggregateMemory.ScalarReadbackPlan.vector' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ScalarReadbackPlan.vector

/-- info: 'TrustIr.AggregateMemory.vector_lane_value_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.vector_lane_value_readback

-- Ordinary-image metadata, including the actual unwritten-store boundary.

/-- info: 'TrustIr.AggregateMemory.FieldsEncoded.unwritten_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsEncoded.unwritten_preserved

/-- info: 'TrustIr.AggregateMemory.encode_leaf_unwritten_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_leaf_unwritten_empty

/-- info: 'TrustIr.AggregateMemory.encode_array_unwritten_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_array_unwritten_empty

/-- info: 'TrustIr.AggregateMemory.encode_ordinary_unwritten_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_ordinary_unwritten_empty

/-- info: 'TrustIr.AggregateMemory.encode_uninit_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_uninit_exact

/-- info: 'TrustIr.AggregateMemory.encode_ordinary_recordUnwritten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_ordinary_recordUnwritten

/-- info: 'TrustIr.AggregateMemory.OrdinaryImageMetadataControls.padding_is_not_an_unwritten_lane' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.OrdinaryImageMetadataControls.padding_is_not_an_unwritten_lane

/-- info: 'TrustIr.AggregateMemory.OrdinaryImageMetadataControls.nested_ordinary_metadata_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.OrdinaryImageMetadataControls.nested_ordinary_metadata_empty

/-- info: 'TrustIr.AggregateMemory.OrdinaryImageMetadataControls.unwritten_permission_is_observable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.OrdinaryImageMetadataControls.unwritten_permission_is_observable

/-- info: 'TrustIr.AggregateMemory.OrdinaryImageMetadataControls.ordinary_whole_unwritten_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.OrdinaryImageMetadataControls.ordinary_whole_unwritten_refuses

/-- info: 'TrustIr.AggregateMemory.OrdinaryImageMetadataControls.ordinary_nested_unwritten_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.OrdinaryImageMetadataControls.ordinary_nested_unwritten_refuses

/-- info: 'TrustIr.AggregateMemory.OrdinaryImageMetadataControls.allowed_nested_unwritten_retains_offset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.OrdinaryImageMetadataControls.allowed_nested_unwritten_retains_offset

/-- info: 'TrustIr.AggregateMemory.OrdinaryImageMetadataControls.empty_array_unused_template_has_no_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.OrdinaryImageMetadataControls.empty_array_unused_template_has_no_records

/-- info: 'TrustIr.AggregateMemory.OrdinaryImageMetadataControls.visible_array_unwritten_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.OrdinaryImageMetadataControls.visible_array_unwritten_refuses

/-- info: 'TrustIr.AggregateMemory.OrdinaryImageMetadataControls.enum_payload_metadata_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.OrdinaryImageMetadataControls.enum_payload_metadata_empty

/-- info: 'TrustIr.AggregateMemory.OrdinaryImageMetadataControls.enum_payload_does_not_inherit_permission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.OrdinaryImageMetadataControls.enum_payload_does_not_inherit_permission

/-- info: 'TrustIr.AggregateMemory.OrdinaryImageMetadataControls.zero_sized_whole_record_is_retained_by_encoder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.OrdinaryImageMetadataControls.zero_sized_whole_record_is_retained_by_encoder

/-- info: 'TrustIr.AggregateMemory.OrdinaryImageMetadataControls.zero_sized_record_is_omitted_by_memory' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.OrdinaryImageMetadataControls.zero_sized_record_is_omitted_by_memory

/-- info: 'TrustIr.AggregateMemory.OrdinaryImageMetadataControls.ordinary_recording_preserves_existing_memory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.OrdinaryImageMetadataControls.ordinary_recording_preserves_existing_memory

/-- info: 'TrustIr.AggregateMemory.OrdinaryImageMetadataControls.copying_padding_does_not_record_unwritten' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.OrdinaryImageMetadataControls.copying_padding_does_not_record_unwritten

-- Unwritten image and actual destination registration bounds.

/-- info: 'TrustIr.AggregateMemory.Image.UnwrittenBounded' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Image.UnwrittenBounded

/-- info: 'TrustIr.AggregateMemory.Image.unwritten_bounded_of_empty' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Image.unwritten_bounded_of_empty

/-- info: 'TrustIr.AggregateMemory.FieldsEncoded.unwritten_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.FieldsEncoded.unwritten_bounded

/-- info: 'TrustIr.AggregateMemory.encode_unwritten_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_unwritten_bounded

/-- info: 'TrustIr.AggregateMemory.encode_unwritten_plan_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_unwritten_plan_bounds

/-- info: 'TrustIr.AggregateMemory.Image.recordUnwritten_bounds' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.Image.recordUnwritten_bounds

/-- info: 'TrustIr.AggregateMemory.encode_registered_unwritten_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_registered_unwritten_bounds

/-- info: 'TrustIr.AggregateMemory.UnwrittenImageBoundsControls.nested_offsets_are_added' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.UnwrittenImageBoundsControls.nested_offsets_are_added

/-- info: 'TrustIr.AggregateMemory.UnwrittenImageBoundsControls.actual_nested_encoding_is_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.UnwrittenImageBoundsControls.actual_nested_encoding_is_bounded

/-- info: 'TrustIr.AggregateMemory.UnwrittenImageBoundsControls.declared_extent_supplies_the_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.UnwrittenImageBoundsControls.declared_extent_supplies_the_bound

/-- info: 'TrustIr.AggregateMemory.UnwrittenImageBoundsControls.registration_moves_into_destination_window' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.UnwrittenImageBoundsControls.registration_moves_into_destination_window

/-- info: 'TrustIr.AggregateMemory.UnwrittenImageBoundsControls.registration_retains_allocation_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.UnwrittenImageBoundsControls.registration_retains_allocation_identity

/-- info: 'TrustIr.AggregateMemory.UnwrittenImageBoundsControls.actual_encoding_supplies_registration_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.UnwrittenImageBoundsControls.actual_encoding_supplies_registration_bounds

/-- info: 'TrustIr.AggregateMemory.UnwrittenImageBoundsControls.fabricated_outside_record_is_not_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.UnwrittenImageBoundsControls.fabricated_outside_record_is_not_bounded

/-- info: 'TrustIr.AggregateMemory.UnwrittenImageBoundsControls.child_outside_parent_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.UnwrittenImageBoundsControls.child_outside_parent_refuses

/-- info: 'TrustIr.AggregateMemory.UnwrittenImageBoundsControls.zero_sized_child_outside_parent_also_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.UnwrittenImageBoundsControls.zero_sized_child_outside_parent_also_refuses

/-- info: 'TrustIr.AggregateMemory.UnwrittenImageBoundsControls.whole_array_unwritten_has_bounded_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.UnwrittenImageBoundsControls.whole_array_unwritten_has_bounded_record

/-- info: 'TrustIr.AggregateMemory.UnwrittenImageBoundsControls.zero_sized_record_at_endpoint_is_bounded' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.UnwrittenImageBoundsControls.zero_sized_record_at_endpoint_is_bounded

/-- info: 'TrustIr.AggregateMemory.UnwrittenImageBoundsControls.zero_sized_registration_adds_no_record' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.UnwrittenImageBoundsControls.zero_sized_registration_adds_no_record

/-- info: 'TrustIr.AggregateMemory.UnwrittenImageBoundsControls.unrelated_old_records_are_preserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.UnwrittenImageBoundsControls.unrelated_old_records_are_preserved

/-- info: 'TrustIr.AggregateMemory.UnwrittenImageBoundsControls.bounded_record_does_not_imply_absent_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.UnwrittenImageBoundsControls.bounded_record_does_not_imply_absent_bytes

-- Exact unwritten coverage through clipping and authoritative byte writes.

/-- info: 'TrustIr.Memory.forgetUnwritten_coverage' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.Memory.forgetUnwritten_coverage

/-- info: 'TrustIr.Memory.writeImage_unwritten_coverage' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.Memory.writeImage_unwritten_coverage

/-- info: 'TrustIr.Memory.writeImage_unwritten_inside' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.Memory.writeImage_unwritten_inside

/-- info: 'TrustIr.Memory.writeImage_unwritten_outside' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.Memory.writeImage_unwritten_outside

/-- info: 'TrustIr.Memory.writeImage_no_new_unwritten' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.Memory.writeImage_no_new_unwritten

/-- info: 'TrustIr.Memory.writeBytesMaybeUninit_unwritten_coverage' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.Memory.writeBytesMaybeUninit_unwritten_coverage

/-- info: 'TrustIr.Memory.writeBytes_unwritten_coverage' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.Memory.writeBytes_unwritten_coverage

/-- info: 'TrustIr.AggregateMemory.encode_ordinary_publication_coverage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.encode_ordinary_publication_coverage

/-- info: 'TrustIr.UnwrittenOverwriteControls.absent_copy_clears_old_lane' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.UnwrittenOverwriteControls.absent_copy_clears_old_lane

/-- info: 'TrustIr.UnwrittenOverwriteControls.middle_write_preserves_both_sides' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.UnwrittenOverwriteControls.middle_write_preserves_both_sides

/-- info: 'TrustIr.UnwrittenOverwriteControls.half_open_endpoints_are_exact' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.UnwrittenOverwriteControls.half_open_endpoints_are_exact

/-- info: 'TrustIr.UnwrittenOverwriteControls.complete_overwrite_clears_every_covered_address' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.UnwrittenOverwriteControls.complete_overwrite_clears_every_covered_address

/-- info: 'TrustIr.UnwrittenOverwriteControls.zero_length_write_preserves_lane' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.UnwrittenOverwriteControls.zero_length_write_preserves_lane

/-- info: 'TrustIr.UnwrittenOverwriteControls.adjacent_write_does_not_clip' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.UnwrittenOverwriteControls.adjacent_write_does_not_clip

/-- info: 'TrustIr.UnwrittenOverwriteControls.write_cannot_create_an_unwritten_claim' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.UnwrittenOverwriteControls.write_cannot_create_an_unwritten_claim

/-- info: 'TrustIr.UnwrittenOverwriteControls.distinct_allocation_does_not_gain_coverage' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.UnwrittenOverwriteControls.distinct_allocation_does_not_gain_coverage

/-- info: 'TrustIr.UnwrittenOverwriteControls.duplicate_overlapping_records_are_all_clipped' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.UnwrittenOverwriteControls.duplicate_overlapping_records_are_all_clipped

/-- info: 'TrustIr.UnwrittenOverwriteControls.list_transport_has_same_clipping' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.UnwrittenOverwriteControls.list_transport_has_same_clipping

/-- info: 'TrustIr.UnwrittenOverwriteControls.initialized_list_write_has_same_clipping' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.UnwrittenOverwriteControls.initialized_list_write_has_same_clipping

/-- info: 'TrustIr.UnwrittenOverwriteControls.malformed_old_record_cannot_create_coverage' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.UnwrittenOverwriteControls.malformed_old_record_cannot_create_coverage

/-- info: 'TrustIr.UnwrittenOverwriteControls.actual_ordinary_publication_clears_old_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.UnwrittenOverwriteControls.actual_ordinary_publication_clears_old_record

/-- info: 'TrustIr.UnwrittenOverwriteControls.source_publication_law_uses_actual_extent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.UnwrittenOverwriteControls.source_publication_law_uses_actual_extent

-- Actual aggregate Store execution, transport branches, live extents and metadata.

/-- info: 'TrustIr.AggregateMemory.StoreImageAccepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreImageAccepted

/-- info: 'TrustIr.AggregateMemory.storeValue_success_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.storeValue_success_steps

/-- info: 'TrustIr.AggregateMemory.StoreImageAccepted.unwritten_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreImageAccepted.unwritten_bounded

/-- info: 'TrustIr.AggregateMemory.StoreImageAccepted.unwritten_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreImageAccepted.unwritten_empty

/-- info: 'TrustIr.AggregateMemory.storeValue_success_live_allocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.storeValue_success_live_allocation

/-- info: 'TrustIr.AggregateMemory.storeValue_success_unwritten_coverage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.storeValue_success_unwritten_coverage

/-- info: 'TrustIr.AggregateMemory.storeValue_success_registered_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.storeValue_success_registered_bounds

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.actual_scalar_store_executes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.actual_scalar_store_executes

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.actual_scalar_store_writes_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.actual_scalar_store_writes_byte

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.actual_scalar_store_clears_exact_window' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.actual_scalar_store_clears_exact_window

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.scalar_store_retains_private_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.scalar_store_retains_private_state

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.partial_transport_is_not_ordinary_encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.partial_transport_is_not_ordinary_encoding

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.typed_poison_transport_has_no_new_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.typed_poison_transport_has_no_new_records

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.wrong_poison_type_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.wrong_poison_type_refuses

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.strict_poison_refuses_before_target_and_pointer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.strict_poison_refuses_before_target_and_pointer

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.source_target_mismatch_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.source_target_mismatch_refuses

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.alignment_refusal_precedes_pointer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.alignment_refusal_precedes_pointer

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.null_pointer_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.null_pointer_refuses

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.dead_allocation_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.dead_allocation_refuses

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.access_refusal_precedes_bad_carrier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.access_refusal_precedes_bad_carrier

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.target32_refusal_precedes_allocation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.target32_refusal_precedes_allocation

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.partial_image_extent_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.partial_image_extent_refuses

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.actual_unwritten_tuple_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.actual_unwritten_tuple_publication

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.strict_nested_unwritten_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.strict_nested_unwritten_refuses

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.whole_unwritten_store_registers_a_new_lane' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.whole_unwritten_store_registers_a_new_lane

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.actual_scalar_store_then_load' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.actual_scalar_store_then_load

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.actual_unwritten_tuple_store_then_load' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.actual_unwritten_tuple_store_then_load

/-- info: 'TrustIr.AggregateMemory.StoreExecutionControls.absent_transport_does_not_authorize_strict_load' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreExecutionControls.absent_transport_does_not_authorize_strict_load

-- Original SSA Store operands, actual context dispatch and descriptor execution.

/-- info: 'TrustIr.selectedStoreAction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.selectedStoreAction

/-- info: 'TrustIr.selectedStoreAction_default_align' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.selectedStoreAction_default_align

/-- info: 'TrustIr.stepStore_lookup_action' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepStore_lookup_action

/-- info: 'TrustIr.stepStore_success_operands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepStore_success_operands

/-- info: 'TrustIr.aggregateStore_success_operands' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.aggregateStore_success_operands

/-- info: 'TrustIr.stepStore_descriptor_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepStore_descriptor_execution

/-- info: 'TrustIr.stepStore_canonical_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepStore_canonical_execution

/-- info: 'TrustIr.memoryServiceFor_descriptor_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms TrustIr.memoryServiceFor_descriptor_iff

/-- info: 'TrustIr.stepStore_descriptor_success_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepStore_descriptor_success_steps

/-- info: 'TrustIr.stepStore_descriptor_unwritten_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepStore_descriptor_unwritten_coverage

/-- info: 'TrustIr.stepStore_descriptor_registered_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepStore_descriptor_registered_bounds

/-- info: 'TrustIr.StoreInstructionControls.descriptor_selector_uses_actual_service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreInstructionControls.descriptor_selector_uses_actual_service

/-- info: 'TrustIr.StoreInstructionControls.canonical_selector_keeps_scalar_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreInstructionControls.canonical_selector_keeps_scalar_path

/-- info: 'TrustIr.StoreInstructionControls.actual_store_node_executes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreInstructionControls.actual_store_node_executes

/-- info: 'TrustIr.StoreInstructionControls.store_node_does_not_publish_ssa_temporaries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreInstructionControls.store_node_does_not_publish_ssa_temporaries

/-- info: 'TrustIr.StoreInstructionControls.store_node_publishes_selected_unwritten_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreInstructionControls.store_node_publishes_selected_unwritten_image

/-- info: 'TrustIr.StoreInstructionControls.missing_pointer_lookup_precedes_other_refusals' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreInstructionControls.missing_pointer_lookup_precedes_other_refusals

/-- info: 'TrustIr.StoreInstructionControls.missing_value_lookup_is_not_a_missing_pointer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreInstructionControls.missing_value_lookup_is_not_a_missing_pointer

/-- info: 'TrustIr.StoreInstructionControls.canonical_store_ignores_wrong_target_descriptor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreInstructionControls.canonical_store_ignores_wrong_target_descriptor

/-- info: 'TrustIr.StoreInstructionControls.descriptor_store_keeps_target_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreInstructionControls.descriptor_store_keeps_target_refusal

/-- info: 'TrustIr.StoreInstructionControls.missing_descriptor_has_no_fabricated_layout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreInstructionControls.missing_descriptor_has_no_fabricated_layout

/-- info: 'TrustIr.StoreInstructionControls.instruction_alignment_is_forwarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreInstructionControls.instruction_alignment_is_forwarded

/-- info: 'TrustIr.StoreInstructionControls.descriptor_strict_poison_precedes_pointer_check' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreInstructionControls.descriptor_strict_poison_precedes_pointer_check

/-- info: 'TrustIr.StoreInstructionControls.canonical_pointer_check_precedes_strict_poison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreInstructionControls.canonical_pointer_check_precedes_strict_poison

/-- info: 'TrustIr.StoreInstructionControls.identical_operand_ids_are_read_from_original_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreInstructionControls.identical_operand_ids_are_read_from_original_state

/-- info: 'TrustIr.StoreInstructionControls.descriptor_store_then_load_publishes_only_the_load' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreInstructionControls.descriptor_store_then_load_publishes_only_the_load

/-- info: 'TrustIr.StoreInstructionControls.canonical_store_then_load_publishes_only_the_load' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreInstructionControls.canonical_store_then_load_publishes_only_the_load

/-- info: 'TrustIr.scalarLoadValue_readOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.scalarLoadValue_readOnly

/-- info: 'TrustIr.aggregateLoadValue_readOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.aggregateLoadValue_readOnly

/-- info: 'TrustIr.selectedLoadAction_readOnly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.selectedLoadAction_readOnly

/-- info: 'TrustIr.selectedLoadAction_default_align' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.selectedLoadAction_default_align

/-- info: 'TrustIr.stepLoad_lookup_action' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepLoad_lookup_action

/-- info: 'TrustIr.stepLoad_success_publication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepLoad_success_publication

/-- info: 'TrustIr.stepLoad_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepLoad_success_iff

/-- info: 'TrustIr.stepLoad_memory_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepLoad_memory_unchanged

/-- info: 'TrustIr.stepLoad_published_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepLoad_published_value

/-- info: 'TrustIr.stepLoad_descriptor_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepLoad_descriptor_execution

/-- info: 'TrustIr.stepLoad_canonical_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepLoad_canonical_execution

/-- info: 'TrustIr.LoadInstructionControls.descriptor_load_publishes_actual_value_once' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LoadInstructionControls.descriptor_load_publishes_actual_value_once

/-- info: 'TrustIr.LoadInstructionControls.scalar_load_keeps_canonical_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LoadInstructionControls.scalar_load_keeps_canonical_path

/-- info: 'TrustIr.LoadInstructionControls.scalar_partial_load_publishes_poison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LoadInstructionControls.scalar_partial_load_publishes_poison

/-- info: 'TrustIr.LoadInstructionControls.scalar_strict_load_refuses_uninitialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LoadInstructionControls.scalar_strict_load_refuses_uninitialized

/-- info: 'TrustIr.LoadInstructionControls.descriptor_unexplained_hole_is_not_padding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LoadInstructionControls.descriptor_unexplained_hole_is_not_padding

/-- info: 'TrustIr.LoadInstructionControls.descriptor_unwritten_load_uses_original_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LoadInstructionControls.descriptor_unwritten_load_uses_original_metadata

/-- info: 'TrustIr.LoadInstructionControls.strict_descriptor_preserves_explicit_unwritten_policy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LoadInstructionControls.strict_descriptor_preserves_explicit_unwritten_policy

/-- info: 'TrustIr.LoadInstructionControls.unwritten_read_does_not_consume_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LoadInstructionControls.unwritten_read_does_not_consume_metadata

/-- info: 'TrustIr.LoadInstructionControls.missing_operand_precedes_target_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LoadInstructionControls.missing_operand_precedes_target_refusal

/-- info: 'TrustIr.LoadInstructionControls.descriptor_target_precedes_null_pointer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LoadInstructionControls.descriptor_target_precedes_null_pointer

/-- info: 'TrustIr.LoadInstructionControls.scalar_null_pointer_precedes_bad_alignment' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LoadInstructionControls.scalar_null_pointer_precedes_bad_alignment

/-- info: 'TrustIr.LoadInstructionControls.descriptor_alignment_is_forwarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LoadInstructionControls.descriptor_alignment_is_forwarded

/-- info: 'TrustIr.LoadInstructionControls.missing_service_does_not_fabricate_layout' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LoadInstructionControls.missing_service_does_not_fabricate_layout

/-- info: 'TrustIr.LoadInstructionControls.colliding_next_id_still_looks_up_before_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.LoadInstructionControls.colliding_next_id_still_looks_up_before_publication

/-- info: 'TrustIr.AggregateMemory.loadValue_image_action' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.loadValue_image_action

/-- info: 'TrustIr.AggregateMemory.loadValue_success_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.loadValue_success_steps

/-- info: 'TrustIr.AggregateMemory.loadImageResult_success_cases' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.loadImageResult_success_cases

/-- info: 'TrustIr.AggregateMemory.loadValue_success_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.loadValue_success_image

/-- info: 'TrustIr.AggregateMemory.loadImageAccepted_result' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.loadImageAccepted_result

/-- info: 'TrustIr.AggregateMemory.loadImageResult_success_iff' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.loadImageResult_success_iff

/-- info: 'TrustIr.stepLoad_descriptor_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepLoad_descriptor_image

/-- info: 'TrustIr.AggregateLoadExecutionControls.plan_is_actual_source_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateLoadExecutionControls.plan_is_actual_source_query

/-- info: 'TrustIr.AggregateLoadExecutionControls.complete_image_selects_ordinary_decode' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateLoadExecutionControls.complete_image_selects_ordinary_decode

/-- info: 'TrustIr.AggregateLoadExecutionControls.missing_padding_is_not_partial_poison' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateLoadExecutionControls.missing_padding_is_not_partial_poison

/-- info: 'TrustIr.AggregateLoadExecutionControls.padding_path_checks_only_covered_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateLoadExecutionControls.padding_path_checks_only_covered_bytes

/-- info: 'TrustIr.AggregateLoadExecutionControls.explained_fields_decode_original_unwritten_value' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateLoadExecutionControls.explained_fields_decode_original_unwritten_value

/-- info: 'TrustIr.AggregateLoadExecutionControls.temporary_zeros_do_not_replace_original_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateLoadExecutionControls.temporary_zeros_do_not_replace_original_image

/-- info: 'TrustIr.AggregateLoadExecutionControls.temporary_zeros_are_not_a_loaded_zero_value' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateLoadExecutionControls.temporary_zeros_are_not_a_loaded_zero_value

/-- info: 'TrustIr.AggregateLoadExecutionControls.wrong_allocation_cannot_explain_a_hole' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateLoadExecutionControls.wrong_allocation_cannot_explain_a_hole

/-- info: 'TrustIr.AggregateLoadExecutionControls.padding_record_cannot_explain_a_field' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateLoadExecutionControls.padding_record_cannot_explain_a_field

/-- info: 'TrustIr.AggregateLoadExecutionControls.adjacent_record_does_not_cover_the_load' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateLoadExecutionControls.adjacent_record_does_not_cover_the_load

/-- info: 'TrustIr.AggregateLoadExecutionControls.partial_scalar_transport_is_a_distinct_branch' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateLoadExecutionControls.partial_scalar_transport_is_a_distinct_branch

/-- info: 'TrustIr.AggregateLoadExecutionControls.strict_scalar_does_not_take_partial_transport' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.AggregateLoadExecutionControls.strict_scalar_does_not_take_partial_transport

/-- info: 'TrustIr.AggregateLoadExecutionControls.original_node_reads_padded_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateLoadExecutionControls.original_node_reads_padded_image

/-- info: 'TrustIr.AggregateLoadExecutionControls.original_node_reads_unwritten_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateLoadExecutionControls.original_node_reads_unwritten_image

/-- info: 'TrustIr.scalarLoadValue_success_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.scalarLoadValue_success_steps

/-- info: 'TrustIr.scalarLoadValue_of_checks' depends on axioms: [Quot.sound, propext] -/
#guard_msgs in
#print axioms TrustIr.scalarLoadValue_of_checks

/-- info: 'TrustIr.scalarLoadValue_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.scalarLoadValue_success_iff

/-- info: 'TrustIr.stepLoad_scalar_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepLoad_scalar_image

/-- info: 'TrustIr.ScalarLoadExecutionControls.target32_reads_exactly_four_usize_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ScalarLoadExecutionControls.target32_reads_exactly_four_usize_bytes

/-- info: 'TrustIr.ScalarLoadExecutionControls.target64_reads_all_eight_usize_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ScalarLoadExecutionControls.target64_reads_all_eight_usize_bytes

/-- info: 'TrustIr.ScalarLoadExecutionControls.target32_ignores_unread_high_half' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ScalarLoadExecutionControls.target32_ignores_unread_high_half

/-- info: 'TrustIr.ScalarLoadExecutionControls.target64_transports_the_actual_partial_image' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ScalarLoadExecutionControls.target64_transports_the_actual_partial_image

/-- info: 'TrustIr.ScalarLoadExecutionControls.pointer_decode_recovers_original_memory_provenance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ScalarLoadExecutionControls.pointer_decode_recovers_original_memory_provenance

/-- info: 'TrustIr.ScalarLoadExecutionControls.function_decode_uses_source_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ScalarLoadExecutionControls.function_decode_uses_source_order

/-- info: 'TrustIr.ScalarLoadExecutionControls.changed_function_order_changes_actual_loaded_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ScalarLoadExecutionControls.changed_function_order_changes_actual_loaded_identity

/-- info: 'TrustIr.ScalarLoadExecutionControls.initialized_function_without_table_is_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ScalarLoadExecutionControls.initialized_function_without_table_is_refused

/-- info: 'TrustIr.ScalarLoadExecutionControls.null_function_does_not_require_a_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ScalarLoadExecutionControls.null_function_does_not_require_a_table

/-- info: 'TrustIr.ScalarLoadExecutionControls.initialized_invalid_char_is_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ScalarLoadExecutionControls.initialized_invalid_char_is_refused

/-- info: 'TrustIr.ScalarLoadExecutionControls.partial_char_keeps_the_partial_transport_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ScalarLoadExecutionControls.partial_char_keeps_the_partial_transport_path

/-- info: 'TrustIr.ScalarLoadExecutionControls.initialized_bytes_retain_the_actual_decoder_refusal' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ScalarLoadExecutionControls.initialized_bytes_retain_the_actual_decoder_refusal

/-- info: 'TrustIr.ScalarLoadExecutionControls.partial_transport_does_not_assume_decoder_success' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ScalarLoadExecutionControls.partial_transport_does_not_assume_decoder_success

/-- info: 'TrustIr.Memory.recordUnwritten_bytes' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.Memory.recordUnwritten_bytes

/-- info: 'TrustIr.Memory.readImage_after_write_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.Memory.readImage_after_write_record

/-- info: 'TrustIr.AggregateMemory.ReadbackInput.not_poison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.ReadbackInput.not_poison

/-- info: 'TrustIr.AggregateMemory.StoreImageAccepted.ordinary_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.StoreImageAccepted.ordinary_encode

/-- info: 'TrustIr.AggregateMemory.storeValue_success_image_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.storeValue_success_image_bytes

/-- info: 'TrustIr.AggregateMemory.prepared_store_snapshot_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.AggregateMemory.prepared_store_snapshot_readback

/-- info: 'TrustIr.stepStore_descriptor_image_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepStore_descriptor_image_bytes

/-- info: 'TrustIr.stepStore_prepared_snapshot_readback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.stepStore_prepared_snapshot_readback

/-- info: 'TrustIr.StoreImageReadbackControls.actual_store_has_admitted_snapshot' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.StoreImageReadbackControls.actual_store_has_admitted_snapshot

/-- info: 'TrustIr.StoreImageReadbackControls.snapshot_contains_normalized_integer_not_raw_carrier' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.StoreImageReadbackControls.snapshot_contains_normalized_integer_not_raw_carrier

/-- info: 'TrustIr.StoreImageReadbackControls.raw_carrier_identity_is_not_the_readback_relation' depends on axioms: [propext,
 Quot.sound,
 Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.StoreImageReadbackControls.raw_carrier_identity_is_not_the_readback_relation

/-- info: 'TrustIr.StoreImageReadbackControls.absent_padding_overwrites_stale_initialized_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreImageReadbackControls.absent_padding_overwrites_stale_initialized_bytes

/-- info: 'TrustIr.StoreImageReadbackControls.ordinary_store_does_not_retain_stale_unwritten_coverage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreImageReadbackControls.ordinary_store_does_not_retain_stale_unwritten_coverage

/-- info: 'TrustIr.StoreImageReadbackControls.outside_snapshot_is_absent_even_when_following_memory_is_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreImageReadbackControls.outside_snapshot_is_absent_even_when_following_memory_is_initialized

/-- info: 'TrustIr.StoreImageReadbackControls.original_store_then_load_reads_the_normalized_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreImageReadbackControls.original_store_then_load_reads_the_normalized_value

/-- info: 'TrustIr.StoreImageReadbackControls.partial_store_also_replaces_stale_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreImageReadbackControls.partial_store_also_replaces_stale_bytes

/-- info: 'TrustIr.StoreImageReadbackControls.partial_transport_has_no_typed_readback_admission' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreImageReadbackControls.partial_transport_has_no_typed_readback_admission

/-- info: 'TrustIr.StoreImageReadbackControls.empty_snapshot_has_no_outside_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.StoreImageReadbackControls.empty_snapshot_has_no_outside_byte

-- Logical block-check completeness and actual callback controls.

/-- info: 'TrustIr.ByteImage.CheckedBlocks.congr' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.ByteImage.CheckedBlocks.congr

/-- info: 'TrustIr.ByteImage.CheckedBlocks.subrange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.CheckedBlocks.subrange

/-- info: 'TrustIr.ByteImage.checkBlocksSpec_none_of_checked_of_periods' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.checkBlocksSpec_none_of_checked_of_periods

/-- info: 'TrustIr.ByteImage.checkBlocks_none_of_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.checkBlocks_none_of_checked

/-- info: 'TrustIr.ByteImage.checkBlocks_subrange_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.checkBlocks_subrange_none

/-- info: 'TrustIr.ByteImage.BlockCheckCompletenessControls.logical_custody_drives_actual_check' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.BlockCheckCompletenessControls.logical_custody_drives_actual_check

/-- info: 'TrustIr.ByteImage.BlockCheckCompletenessControls.bounded_subrange_keeps_callback_authority' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.BlockCheckCompletenessControls.bounded_subrange_keeps_callback_authority

/-- info: 'TrustIr.ByteImage.BlockCheckCompletenessControls.zero_count_does_not_call_a_refusing_callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.BlockCheckCompletenessControls.zero_count_does_not_call_a_refusing_callback

/-- info: 'TrustIr.ByteImage.BlockCheckCompletenessControls.positive_count_zero_width_retains_callback_refusal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.BlockCheckCompletenessControls.positive_count_zero_width_retains_callback_refusal

/-- info: 'TrustIr.ByteImage.BlockCheckCompletenessControls.coprime_periodic_phases_are_checked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.BlockCheckCompletenessControls.coprime_periodic_phases_are_checked

/-- info: 'TrustIr.ByteImage.BlockCheckCompletenessControls.late_hole_in_period_is_not_hidden_by_initialized_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.BlockCheckCompletenessControls.late_hole_in_period_is_not_hidden_by_initialized_prefix

/-- info: 'TrustIr.ByteImage.BlockCheckCompletenessControls.later_error_keeps_precedence_over_earlier_hole' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.BlockCheckCompletenessControls.later_error_keeps_precedence_over_earlier_hole

/-- info: 'TrustIr.ByteImage.BlockCheckCompletenessControls.invisible_retained_hole_is_not_a_visible_block' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.BlockCheckCompletenessControls.invisible_retained_hole_is_not_a_visible_block

/-- info: 'TrustIr.ByteImage.BlockCheckCompletenessControls.initialized_prefix_is_not_full_block_custody' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.ByteImage.BlockCheckCompletenessControls.initialized_prefix_is_not_full_block_custody
