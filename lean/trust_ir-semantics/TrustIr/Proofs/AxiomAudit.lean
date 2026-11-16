import TrustIr.Proofs.AxiomAuditCompat
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
-- `Quot.sound`. The commands below enforce exact transitive axiom sets for
-- both pinned compilers, independent of printer order. The canonical sets are
-- retained verbatim. Modern Float primitives and library proofs can move among
-- the same Lean-core trio; the project axiom cannot enter a declaration that
-- lacked it canonically. A NEW axiom (including `sorryAx`) fails the build. Imported by `TrustIr.lean`, so the gate runs on
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
#trustIrAxiomsPinned TrustIr.functionAddressIndex_spec == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.encodeFunctionWord == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.decodeFunctionWord == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.functionTargetAt_unregistered == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.constValueAtWithDefs_withFunctionOrder == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.functionOrder_mapFunctionCFGs == [] modern []

#trustIrAxiomsPinned TrustIr.functionCall_signature_mismatch == [] modern []

#trustIrAxiomsPinned TrustIr.const_function_retains_identity == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

open TrustIr.VectorDialect

-- Bool ICmp is checked by exhaustive kernel reduction, not a native oracle.
#trustIrAxiomsPinned TrustIr.semBoolICmp_truth_table == [] modern []

-- The AY soundness bridge: its SOLE first-party axiom is `ay_sound_unsat`.
#trustIrAxiomsPinned TrustIr.ay_sound_contrapositive == [propext, TrustIr.ay_sound_unsat] modern [propext, TrustIr.ay_sound_unsat]

-- Semantic decoding and its controls must not depend on the solver oracle.
#trustIrAxiomsPinned TrustIr.ay_equiv_implies_inst_equiv == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.unreachable_encoding_faithful == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.unreachable_error_decoder_refused == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

-- DCE correctness: no first-party axiom (Lean-core trio only).
#trustIrAxiomsPinned TrustIr.dce_pure_inst == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

-- The four formerly-axiomatized theorems are genuine proofs: Lean-core trio only,
-- NO `ay_sound_unsat`, NO `sorryAx`.
-- Typed-vector encoding now checks integer lane widths with the existing
-- `Ty.bitWidth`, whose axiom census includes `Classical.choice`. This reaches
-- `semStore` and dependent theorem types, including scalar examples below.
-- Their exact guards retain only the same permitted Lean-core trio.
#trustIrAxiomsPinned TrustIr.semStore_characterize == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.load_after_store_program == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- WS3.7 (F-047, memory half): the sealed handle slot round trip is an
-- instance of the byte-level load-after-store lemma at the handle width —
-- Lean-core trio only, no first-party axiom.
#trustIrAxiomsPinned TrustIr.load_store_roundtrip_handle == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

-- Borrow address resolution: existing invariant proofs and the actual
-- allocation/borrow/memory compositions use Lean-core axioms only.
#trustIrAxiomsPinned TrustIr.borrow_preserves_stack == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.borrow_mut_preserves_stack == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.end_borrow_preserves_stack == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.BorrowMemoryProps.alloca_store_borrow_load == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.BorrowMemoryProps.alloca_borrow_mut_store_load == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.BorrowMemoryProps.shared_reborrow_and_end_preserve_address == [] modern []

#trustIrAxiomsPinned TrustIr.BorrowMemoryProps.interior_borrow_keeps_offset == [propext, Classical.choice, Quot.sound] modern [propext]

-- A Rust reference carries no permission instruction (docs/SPEC_RATIFICATIONS.md):
-- the two permission-machine faults and the Copy step's frame property, stated
-- for every state and peeled with the sr_* helpers. Lean-core axioms at most;
-- no native_decide (Lean.ofReduceBool) and no ay_sound_unsat.
#trustIrAxiomsPinned TrustIr.BorrowMemoryProps.semBorrow_ub_of_uniqueBorrow == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.BorrowMemoryProps.semBorrowMut_ub_of_not_owned == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.BorrowMemoryProps.stepInst_copy_preserves_memory_and_permissions == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

-- B2 dealloc lifecycle (dead-marking + double-free UB): Lean-core trio only.
#trustIrAxiomsPinned TrustIr.semDealloc_marks_dead == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.semDealloc_twice_is_ub == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

-- Heap-lifetime UB ratification (docs/ub-numerics-policy.md §6): the
-- double-free / use-after-free / ARC-underflow theorems are plain `rfl`
-- computations over the executable semantics — Lean-core axioms at most
-- (semLoad unfolds through well-founded-recursion helpers, pulling in
-- propext/Quot.sound), and in particular NOT native_decide's
-- Lean.ofReduceBool and NOT ay_sound_unsat.
#trustIrAxiomsPinned TrustIr.semDealloc_twice_is_ub_example == [] modern []

#trustIrAxiomsByCompiler TrustIr.semLoad_after_dealloc_is_ub == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.semRelease_after_last_release_is_ub == [] modern []

-- A reference-counted cell is released by `Release`, never by `Dealloc`
-- (docs/SPEC_RATIFICATIONS.md): the general arcRef theorem peels semDealloc
-- with the sr_* helpers (Lean-core trio); the concrete CleanHeap / SwiftHeap
-- instances are axiom-free `rfl` computations; the positive Release twin runs
-- semLoad (its well-founded helpers pull in propext / Quot.sound). None uses
-- native_decide's Lean.ofReduceBool or ay_sound_unsat.
#trustIrAxiomsPinned TrustIr.semDealloc_arcRef_is_ub == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.semDealloc_cleanHeap_is_ub_example == [] modern []

#trustIrAxiomsPinned TrustIr.semDealloc_swiftHeap_is_ub_example == [] modern []

#trustIrAxiomsPinned TrustIr.semRelease_cleanHeap_after_store_load_ok_example == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

-- An ARC operation counts only a reference-counted cell
-- (docs/SPEC_RATIFICATIONS.md): `requireArcRef_non_arcRef_is_ub` is a case
-- split with no axiom; the three general theorems peel the op with the sr_*
-- helpers, whose `simp` rewriting uses propext; the four concrete instances
-- (stack, RustHeap, CMalloc, global reservation) and the address-model pin
-- `retain_one_past_rustHeap_counts_neighbour` are axiom-free `rfl`
-- computations. None uses native_decide's Lean.ofReduceBool or ay_sound_unsat.
#trustIrAxiomsPinned TrustIr.requireArcRef_non_arcRef_is_ub == [] modern []

#trustIrAxiomsPinned TrustIr.semRetain_non_arcRef_is_ub == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.semRelease_non_arcRef_is_ub == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.semIsUnique_non_arcRef_is_ub == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.semRetain_alloca_is_ub_example == [] modern []

#trustIrAxiomsPinned TrustIr.semRelease_rustHeap_is_ub_example == [] modern []

#trustIrAxiomsPinned TrustIr.semIsUnique_cMalloc_is_ub_example == [] modern []

#trustIrAxiomsPinned TrustIr.semRetain_globalAddr_is_ub_example == [] modern []

#trustIrAxiomsPinned TrustIr.retain_one_past_rustHeap_is_ub_and_spares_neighbour == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

-- An ARC operand names its cell's object base (SPEC "An ARC operation
-- counts only a reference-counted cell", clause 3, decided 2026-09-30).

#trustIrAxiomsPinned TrustIr.requireObjectBase_off_base_is_ub == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.semRetain_interior_is_ub == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.semRelease_interior_is_ub == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.semIsUnique_interior_is_ub == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.retain_interior_of_cleanHeap_is_ub == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.release_one_past_cleanHeap_is_ub == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.isUnique_past_slack_of_cleanHeap_is_ub == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.arc_at_object_base_ok_example == [] modern []

-- Freeing an allocation under a live borrow is undefined behaviour
-- (docs/SPEC_RATIFICATIONS.md): the general borrow-state theorem peels
-- semDealloc with the sr_* helpers (Lean-core trio); the five concrete
-- instances and the two decided provenance families
-- (`borrow_one_past_moves_no_permission_and_neighbour_frees`,
-- `double_endBorrow_one_past_keeps_neighbour_borrow`) are axiom-free `rfl`
-- computations. None uses native_decide's Lean.ofReduceBool or ay_sound_unsat.
#trustIrAxiomsPinned TrustIr.semDealloc_borrowed_is_ub == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.semDealloc_under_borrow_is_ub_example == [] modern []

#trustIrAxiomsPinned TrustIr.semDealloc_under_borrowMut_is_ub_example == [] modern []

#trustIrAxiomsPinned TrustIr.semDealloc_under_interior_borrow_is_ub_example == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.semDealloc_one_of_two_borrows_live_is_ub_example == [] modern []

#trustIrAxiomsPinned TrustIr.semDealloc_after_every_endBorrow_ok_example == [] modern []

#trustIrAxiomsPinned TrustIr.borrow_one_past_moves_no_permission_and_neighbour_frees == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.double_endBorrow_one_past_keeps_neighbour_borrow == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

-- P1 CleanHeap origin: the IR→memory-model mapping lock and the
-- origins-are-provenance parity backbone are definitional (`rfl`) — no axioms.
#trustIrAxiomsPinned TrustIr.cleanHeap_toAllocationOrigin == [] modern []

#trustIrAxiomsPinned TrustIr.alloc_isInBounds_ignores_origin == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.VectorDialect.runsAgreeFrom_pack_lanes == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.VectorDialect.runsAgreeFrom_mask_to_bits == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

-- B5 bridge + transfer: the evaluator's Call handling IS runCallReq
-- (terminator branch verbatim; body branch composed with bindResultDests),
-- and the ProofContext postcondition transfer holds over the real evaluator.
-- Lean-core trio only — NO `ay_sound_unsat`, NO `sorryAx`.
#trustIrAxiomsPinned TrustIr.stepNWithContext_callReq_eq_runCallReq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepNWithContext_bodyCall_eq_runCallReq_bind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.proof_context_assume_sound_evaluator == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- B5/EH Invoke bridge + transfer: the evaluator's InvokeReq branch IS
-- runInvokeCall composed with the invoke node's result binding, the
-- normal-edge argument evaluation, and the normal-edge continuation; the
-- ProofContext postcondition transfer holds for the Invoke path over the
-- real evaluator. Lean-core trio only — NO `ay_sound_unsat`, NO `sorryAx`.
#trustIrAxiomsPinned TrustIr.stepNWithContext_invokeReq_eq_runInvokeCall_bind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.proof_context_assume_sound_invoke == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.proof_context_assume_sound_invoke_evaluator == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- Inlining correctness (frame-discipline form): Lean-core trio only.
#trustIrAxiomsPinned TrustIr.inlining_preserving == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- Give-back loop-instruction round-trip laws (the listMap_roundTrip /
-- boolNotLoop_roundTrip counterparts at the operational layer): Lean-core
-- trio only.
#trustIrAxiomsPinned TrustIr.seqMapAddKList_roundTrip == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

-- (This proof's elaboration no longer touches Classical.choice / Quot.sound
-- — the dependency set SHRANK to a subset of the Lean-core trio, which is
-- always acceptable.)
#trustIrAxiomsPinned TrustIr.seqMapNotList_involutive == [propext] modern [propext]

-- B3 depth ledger "Fat-pointer values": the fat-pointer decompose/recombine
-- round trip, at the value level and over the Sem-monad semantics of the
-- PtrData / PtrMetadata / PtrFromParts trio. Lean-core axioms only.
#trustIrAxiomsPinned TrustIr.fatPtr_roundTrip_value == [] modern []

#trustIrAxiomsPinned TrustIr.semFatPtr_roundTrip == [Quot.sound, propext] modern [propext, Quot.sound]

-- fast-4 cross-lane refinements: genuine proofs, Lean-core trio only.
#trustIrAxiomsPinned TrustIr.VectorDialect.runsAgreeFrom_reduce == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.VectorDialect.runsAgreeFrom_shuffle == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.VectorDialect.vectorLowerFrom_sound == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

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
#trustIrAxiomsPinned TrustIr.implies_sound == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.join_upper_bound_left == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.join_upper_bound_right == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.denote_Top == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.top_certifies_only_trivia == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.index_never_implies_member == [propext, Classical.choice, Quot.sound] modern [propext]

-- WS8.15 behaviour refinement (`TransformCorrectness.lean`): the refinement
-- theorems, the constant-fold instance, the negative twin and the mutation
-- controls (the `.ok`-only notions hold where refinement is refuted) all rest
-- on the Lean-core trio only. `sorryAx` or `ay_sound_unsat` here is a
-- regression.
#trustIrAxiomsPinned TrustIr.id_refines == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.compose_refines == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.block_transform_lifts_to_cfg_refines == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.constant_fold_refines == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.assertElim_semantics_preserving == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.assertElim_not_refines == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.loop_not_refines == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.panicToLoop_semantics_preserving_weak == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.panicToLoop_not_refines == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ub_introduction_not_refines == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.semantics_preserving_not_imp_refines == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.inlining_error_transfer == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- WS8.15 adversarial review: divergence-to-return is accepted by the `.ok`-only
-- notion and refused by refinement, trap classes are distinguished, and the
-- UB-top ruling admits a UB-exploiting rewrite.
#trustIrAxiomsPinned TrustIr.divToRet_semantics_preserving == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.divToRet_not_refines == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.trapClass_not_refines == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.unreachableToReturn_refines == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

-- WS8.15 (remainder): behaviour refinement with calls executed
-- (`TransformRefinementCtx.lean`), at the Lean-core trio.
#trustIrAxiomsPinned TrustIr.behavesIn_nonempty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.id_refines_in == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.compose_refines_in == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepNWithContext_unreachableToReturn == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.unreachableToReturn_refines_in == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepNWithContext_mapUnreachableToReturn == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.evalFunctionInContext_mapUnreachableToReturn == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.unreachableToReturn_program_refines == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.inlining_outcome == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.inlining_behaves_iff == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.assertElim_not_refines_in == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.callRetarget_refines == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.callRetarget_not_refines_in == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.behaviour_refines_not_imp_refines_in == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.behavesFn_nonempty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.compose_program_refines == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.withMaxCallDepth_program_refines == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.callProgram_zero_budget_runs_out == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- WS8.15 review: divergence and recursion controls with calls executed.
#trustIrAxiomsPinned TrustIr.loop_not_refines_in == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.recursion_not_refines_in == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.panicToLoop_not_refines_in == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.withMaxCallDepth_not_fixedDepth_refines == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]


-- WS2.18: the fail-closed refusal of a link-time `symbolAddr` constant, and
-- the seed lemmas that thread its absence through the vector lowering.
#trustIrAxiomsPinned TrustIr.const_symbolAddr_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.VectorDialect.seed_noSym_of_lane == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.VectorDialect.listHasSymbolAddr_replicate_int == [propext, Classical.choice, Quot.sound] modern [propext]

-- WS2.24 two-result binding: the unpacked `Overflow` / `CmpXchg` component
-- theorems carry no first-party axiom.
#trustIrAxiomsPinned TrustIr.Sem.bindFreshPair_ok == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.semOverflow_binds_components == [propext, Quot.sound] modern [propext, Quot.sound]

-- Factoring the exchange through typed codecs changes dependency traversal
-- order; the exact census still contains only the same three Lean-core axioms.
#trustIrAxiomsPinned TrustIr.semCmpXchg_binds_components == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

-- Scalar Undef is poison (roadmap WS2.10): executing it succeeds, inspecting it is UB.
#trustIrAxiomsPinned TrustIr.undef_inspect_is_ub == [] modern []

#trustIrAxiomsPinned TrustIr.undef_binop_operand_is_ub == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.undef_condbr_is_ub == [propext] modern [propext]

-- Coroutine controls now use the faithful held-value intrinsic and actual
-- finite source graphs. The false private-register macro/evaluator claims
-- are replaced by value composition and a concrete counterexample. The full
-- source-aware generic graph theorem remains an explicitly open follow-up.
#trustIrAxiomsPinned TrustIr.semGEP_endsFresh == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.semCoroSuspend_bind_value_composition == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.semCoroSuspend_step_value_composition == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.coro_private_spine_counterexample == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.CoroGen.coro_two_state_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.CoroGen.coro_two_state_mutant_traps == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.CoroGen.coro_two_state_roundtrip_mutant_refuted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- WS2.25 review controls: the SILENT `next - 1` mutant (second resume
-- succeeds but re-yields), the load-bearing initial-state hypothesis, and
-- the generator whose suspend state is the literal five-instruction
-- expansion — identical round trip for the correct operand wiring, refuted
-- for the mis-wired store that reads the slot immediate.
#trustIrAxiomsPinned TrustIr.CoroGen.coro_two_state_mutant_loops_refuted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.CoroGen.coro_two_state_from_state_one_never_yields == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.CoroGen.coro_two_state_roundtrip_expanded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.CoroGen.coro_two_state_roundtrip_miswired_refuted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- SPEC "A pointer operand names the allocation it was derived from": the
-- general provenance theorems (every state) and the decided cells (`rfl`
-- computations in the reference placement). Lean-core trio at most; none
-- uses native_decide's Lean.ofReduceBool or ay_sound_unsat.
#trustIrAxiomsPinned TrustIr.semAccess_names_provenance == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.accessAddr_ok_of == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.expectPointer_ok_inv == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.checkedAccess_ok_inv == [Quot.sound, propext, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.checkedAccess_ok_of == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.semBorrow_frame == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.semBorrowMut_frame == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.semEndBorrow_frame == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.semBorrow_outside_requested_is_identity == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.semEndBorrow_outside_requested_is_noop == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.semRetain_frame == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.semRelease_frame == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.semIsUnique_frame == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.semDealloc_frees_its_provenance == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.addrOfInt_lt_two_pow_64 == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.alloc_preserves_layoutWF == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.alloc_base_aligned == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.provenanceAt_inside == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.load_after_store_ptr_recovers_inside == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.decode_encode_address == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.inttoptr_resolves_in_the_one_layout == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.dealloc_zero_size_frees_itself == [] modern []

#trustIrAxiomsPinned TrustIr.dealloc_one_past_end_is_ub == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.aligned_store_after_byte_local_ok == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.load_one_past_end_is_ub == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.load_misaligned_without_declared_align_is_ub == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.gep_keeps_no_provenance == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.inttoptr_negative_is_dangling_not_null == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.BorrowMemoryProps.one_past_address_moves_no_permission == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.BorrowMemoryProps.dead_allocation_moves_no_permission == [] modern []

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

trustIrCompilerCommand (
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
) (
/--
error: Application type mismatch: The argument
  rfl
has type
  ?m.131 = ?m.131
but is expected to have type
  matchSwitchCase (Value.int 64 2) entryCases = some { value := Constant.int 1, target := bbFinal, args := [] }
in the application
  entry_run_case ctx 1 depth (Model.intrinsic 2) a fid (suspendExit s0 a fid 0 2 stateTwoBytes) stateTwoBytes 2 1
    bbFinal hFrame' hRead1 rfl rfl
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
)

end CoroMutant

-- Authoritative compact byte images: complete extents and pointwise reads.
#trustIrAxiomsPinned TrustIr.ByteStore.size_snapshot == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteStore.get_snapshot == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.Memory.bytes_copyImage == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.Memory.bytes_fillImage == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.get_slice == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.get_append == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

-- WS3.20 (F-057): the MemCopy byte-level contract.
#trustIrAxiomsPinned TrustIr.memcopy_preserves_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.memcopy_untouched_below == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

-- v50: the uniform array. `ExtractElement i ∘ ArraySplat = v` for every `n`
-- (the replicated list is never enumerated), and its constant twin.
#trustIrAxiomsByCompiler TrustIr.extract_array_splat == [propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.getElement_ofConstant_splat == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

-- Amendment D (§20): a drop is a call of its type's glue. The resolution
-- lemmas, and the evaluator lift: running a CFG whose drops were rewritten
-- to calls of their glue IS running the original.
#trustIrAxiomsPinned TrustIr.resolveDrop_drop == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.resolveDrop_dropInvoke == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.resolveDrop_unresolved == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.resolveDrop_idem == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.stepNWithContext_resolveDrops == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.drop_unresolved_is_unsupported == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.dropInvoke_unresolved_is_unsupported == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

-- Amendment D, Part 2 (§21): unwinding as an exit. The abort run is a prefix
-- of the unwind run (the relational fuel induction), lifted to the entry as the
-- three abort-projection theorems; a plain call propagates an unwinding; Resume
-- re-raises; pad entry is blind to drop resolution (so the §20 evaluator lift
-- holds under both strategies).
#trustIrAxiomsPinned TrustIr.semEnterPad_resolveCfg == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.stepTermUnwind_resolveCfg == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepNWithContext_abort_prefix == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.evalFunctionInContext_abort_prefix == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.abort_projection_normal_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.abort_projection_ub == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.abort_projection_out_of_fuel == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.plain_call_propagates_unwinding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.resume_reraises_in_hand_exception == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

-- Amendment S (`docs/SPEC_RATIFICATIONS.md` §22): level-S substitution is
-- the identity on ground types and total on a scoped template; the drop
-- rewrite removes exactly the erased drops and commutes with drop resolution
-- when no erased type has a glue row. No first-party axiom.
#trustIrAxiomsPinned TrustIr.substTy_embed == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.substTys_embeds == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.substTy_total == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.substTys_total == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.substConst_embed == [] modern []

#trustIrAxiomsPinned TrustIr.substConst_total == [] modern []

#trustIrAxiomsPinned TrustIr.eraseDrops_removes_erased == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.eraseDrops_terminator == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.eraseDrops_keeps_others == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.eraseTerminator_idem == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.eraseDrops_body_idem == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.resolveBlock_eraseDrops_body == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.resolveDrop_eraseTerminator == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.resolveBlock_eraseDropsBlock == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.resolveCfg_eraseDrops == [Quot.sound, propext] modern [propext, Quot.sound]

-- Nominal closure contracts and the actual evaluator use only Lean-core axioms.
#trustIrAxiomsPinned TrustIr.closureTyEq_iff == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.closureTyListEq_iff == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.checkClosureValue_ptr == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.makeClosureValue_of_checked == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepInstWithContext_makeClosure == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.closureCall_of_checked == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.closureInsert_of_checked == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.closureExtract_of_checked == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.evaluator_closure_preserves_pointer == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.evaluator_closure_preserves_memory == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.evaluator_closure_update_preserves_original == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.evaluator_closure_update_preserves_memory == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.Sem.run_nextFloatZeroChoice == [] modern []

#trustIrAxiomsPinned TrustIr.semFloatMinMaxAt_permitted == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.semFloatMinMaxAt_both_choices == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.program_refines_withFloatChoices == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.unreachableToReturn_program_refinesWithFloatChoices == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.minmax_encoding_refused == [] modern []

-- General vector execution and the shared typed Bool boundary.

#trustIrAxiomsByCompiler TrustIr.executableVectorLaneValueMatches_check == [propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.executableVectorLanePayloadMatches_member == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.executableVectorLanePayloadMatches_nonempty == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.executableVectorLanePayloadMatches_semantic == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.executableVectorPayloadMatches_shape == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.executableVectorPayloadMatches_lanePayload == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.getVectorElement_of_executablePayload == [propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.setVectorElement_of_executablePayload == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.semVectorUnOp_length == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.semVectorBinOp_length == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.semUnOpValue_bool_not_replicate == [propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.semUnOpValue_zero_vector == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.checkVectorLaneType_undef_inspect == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.checkVectorLaneType_undef_transport == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.getVectorElement_bool_head == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.setVectorElement_transports_unselected_poison == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.semBoolBinOp_conjunction == [] modern []

#trustIrAxiomsPinned TrustIr.semBoolBinOp_disjunction == [] modern []

#trustIrAxiomsPinned TrustIr.semBoolBinOp_exclusive_or == [] modern []

#trustIrAxiomsByCompiler TrustIr.semVectorBinOpLane_bool_agrees == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.semBinOpValues_bool_agrees == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.semBoolBinOpValues_int_refused == [] modern []

#trustIrAxiomsPinned TrustIr.semBoolBinOpValues_rhs_undef_priority == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.run_contextual_bool_binop_int_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- State-local extraction domain and concrete kernel controls.

#trustIrAxiomsPinned TrustIr.VectorDialect.runsAgree_extract_lane == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.VectorDialect.runsAgree_insert_lane == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.VectorDialect.extract_lane_refinement_valid_state == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.VectorDialect.extract_lane_result_type_mismatch_refused == [] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.VectorDialect.extract_lane_valid_state_instance == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.VectorDialect.extract_lane_poison_state_instance == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.VectorDialect.extract_lane_wrong_census_refused == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.VectorDialect.extract_lane_wrong_lane_type_agrees == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.VectorDialect.extract_lane_out_of_bounds_agrees == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.VectorDialect.insert_lane_refinement_valid_state == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.VectorDialect.insert_lane_unselected_poison_transport == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.VectorDialect.insert_lane_new_poison_refused == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.VectorDialect.insert_lane_wrong_lane_type_refused == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

-- Source-derived SSA metadata and typed integer consumers. These exact
-- guards retain only the existing Lean-core trust boundary.

#trustIrAxiomsPinned TrustIr.typedIntegerValue_i8 == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.typedIntegerValue_u8 == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.typedIntegerValue_negative_offset == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.typed_signed_index_refused == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.typed_unsigned_index_255 == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.typed_isize32_high_bit == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.typed_usize32_high_bit == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.typed_integer_width_refused == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.typed_integer_poison_priority == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.integerOperand_missing_metadata == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.integerOperand_poison_before_metadata == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.integerOperand_missing_declaration == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.inferLocalTypes_source_producers == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.inferLocalTypes_fat_borrow_chain == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.inferLocalTypes_thin_borrow == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.inferLocalTypes_duplicate_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.inferLocalTypes_result_census_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.inferLocalTypes_borrow_cycle_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.localTypes_mapFunctionCFGs == [] modern []

#trustIrAxiomsPinned TrustIr.forFunction_mapFunctionCFGs == [] modern []

#trustIrAxiomsPinned TrustIr.integerOperand_mapFunctionCFGs == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.elementIndex_mapFunctionCFGs == [propext, Classical.choice, Quot.sound] modern [propext]


-- Top-level Char binding and source association, private-result retirement,
-- exact sparse index laws, and finite source-graph declarations. These are
-- kernel proofs; no native/checker or project axiom is added here.
#trustIrAxiomsPinned TrustIr.ssaChar_int_success_iff == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ssaChar_width_independent == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_non_integer_transport == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_other_type == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_poison_transport == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_partial_transport == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_uninit_transport == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_aggregate_transport == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_valid_edges == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_invalid_edges == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_u32_control == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_mixed_top_level_only == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_block_parameter_valid == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_block_parameter_invalid == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_block_arity_priority == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_manual_source_declaration == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_source_missing_destination == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_source_result_count == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_manual_borrow_boundary == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_manual_header_boundary == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_classification_result_count == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_discarded_result_checked == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_missing_association_before_value_check == [] modern []

#trustIrAxiomsPinned TrustIr.ssaChar_manual_call_result_order == [] modern []

#trustIrAxiomsPinned TrustIr.checkInstructionResults_single_nonChar == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.bindInstructionResults_single_nonChar == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.single_result_private_retired == [] modern []

#trustIrAxiomsPinned TrustIr.single_result_same_id == [] modern []

#trustIrAxiomsPinned TrustIr.single_result_implicit_keeps_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.single_result_future_declaration_retired == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.single_result_later_source_destination == [] modern []

#trustIrAxiomsPinned TrustIr.NatIndexTree.insert_unfold == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexTree.lookupSteps_le_depth == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexTree.keyDepth_le_of_lt_two_pow == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexTree.depth_insert_le == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexTree.find_unfold == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.NatIndexTree.find_insert == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndex.find?_empty == [] modern []

#trustIrAxiomsPinned TrustIr.NatIndex.find?_insert == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndex.find?_insert_same == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndex.find?_insert_ne == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndex.find?_insert_commute == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.resultTypeHeaders_mapFunctionCFGs == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.instructionResultTypes_mapFunctionCFGs == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.checkInstructionResults_mapFunctionCFGs == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.bindCallResults_mapFunctionCFGs == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.bindInstructionResults_mapFunctionCFGs == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.CoroGen.Model.localTypes_present == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.CoroGen.expansion_ids_absent_from_original == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.CoroGen.expanded_source_declarations == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.CoroGen.expanded_preserves_original_declarations == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameOk.legacy_iff == [Quot.sound, propext] modern [propext, Quot.sound]

-- Qualified inference/construction/frame scaffolds for the source-aware
-- coroutine replacement. The actual total expansion theorem remains OPEN;
-- these guards do not claim that a callee-relation premise proves it.
#trustIrAxiomsPinned TrustIr.HeldMemoryFrames.semGEPValuesUsing_eqv == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.HeldMemoryFrames.semStoreValueUsing_eqv == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.index_lt_valueBound == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.freshId_not_source == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.freshId_offset_injective == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.inferredFreshId_not_source == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.inferredFreshId_not_declared == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.inferredFreshId_offset_injective == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.mem_map_of_mem == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.mem_bind_of_mem == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.graphParam_mem == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.graphNode_dest_mem == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.graphNode_operand_mem == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.functionOfGraphWithEvidence_projection == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.expandedEntry_params == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.graphParams_expandFirstEntry == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.cfgOf_expandFirstEntry == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.expandedEntry_result_classifications == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.sourceEntry_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.restoreFrame_callerWorld == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.restoreFrame_eq_of_callerWorld == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.finishCall_eq_of_effectRelation == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.callFrame_eq_of_effectRelation == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.runCallReq_found == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.runCallReq_eq_of_effectRelation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.AgreesExcept.insert_same == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.AgreesExcept.insert_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.AgreesExcept.trans == [] modern []

#trustIrAxiomsPinned TrustIr.LocalTypeInference.fillPath_agreesExcept == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.fillPath_preserves_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.finishPath_agreesExcept == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.finishPath_preserves_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.resolve_fresh_extension == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.resolve_direct_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.resolveAll_cons == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.resolveAll_fresh_extension == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.addSource_fresh_extension == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.addSources_fresh_extension == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.zip_fst_mem == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.addNode_fresh_extension == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.collectNodes_fresh_extension == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.original_empty == [] modern []

#trustIrAxiomsPinned TrustIr.LocalTypeInference.addSource_original == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.addSources_original == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.zip_snd_mem == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.addNode_original == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.collectNodes_original == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.withoutFresh_eq_self == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.freshNode_seed == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.withoutFresh_length_le == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.DeclarationExtension.length_le == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.addNode_empty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.collectNodes_insert_empty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.addNode_success_census == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.collectParams_original == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.inference_eq_collection == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.collectedInference_fresh_extension == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.infer_insert_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- SSA publication freshness and checked parameter binding.
#trustIrAxiomsPinned TrustIr.SSAFreshFrames.cleared_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshFrames.set_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshFrames.publish_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshFrames.bindFresh_publish_run == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshFrames.bindBlockParams_preserves_fresh == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshFrames.bindBlockParamsChecked_preserves_fresh == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

-- Checked pointer observations add no project-specific axiom.
#trustIrAxiomsPinned TrustIr.bindPointerInteger_run == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.bindPointerInteger_success == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.encodeMemoryAt_pointer_address_bound == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.encodeMemoryAt_fat_pointer_address_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

-- Total source-aware coroutine entry expansion and exact u32 capacity.

#trustIrAxiomsPinned TrustIr.LocalTypeInference.resolve_preserves_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.resolveAll_preserves_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.collectedInference_missing == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.infer_missing == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.append_member_cases == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.InputAvoids.insert_declared == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.infer_insert_of_avoid == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.collectNodes_success_census == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.infer_success_census == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.infer_insert_empty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.infer_insert_three == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LocalTypeInference.InputAvoids.mono == [] modern []

#trustIrAxiomsPinned TrustIr.LocalTypeInference.InputAvoids.removeNode == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshIds.map_member == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshIds.unused_le_length == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshIds.fold_find == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshIds.occupied_find == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshIds.occupied_correct == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshIds.scanGap_some == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshIds.scanGap_none == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshIds.nextGap_some == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshIds.nextGap_none == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshIds.contains_insert == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshIds.correct_insert == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshIds.max_u32_does_not_force_overflow == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshIds.original_undefined_uses_stay_reserved == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshIds.two_remaining_ids_are_capacity == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshIds.duplicates_do_not_create_false_capacity == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshIds.left_member_of_append_not_right == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshIds.capacity_excludes_triple == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.declared_map_avoids == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.classified_sources_avoid == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.graph_params_original == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.graph_destinations_original == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.graph_sources_original == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.graph_input_avoids == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.graph_inference_unused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.reservation_unused == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.GraphNames.unused == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.functionsOfExpansion_source_error == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.functionsOfExpansion_capacity == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.cfgOf_decompose == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.expandFirstEntry_at == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.graphNodes_append == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.graphNodes_cons == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.graphNodes_sourceEntry == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.graphNodes_expandedEntry == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.expandedGraph_inference == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.functionOfGraph_of_inference == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.functionsOfExpansion_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.replaceSSA_of_callerWorld == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.equivariant_preservesSSA == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.equivariant_transport == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.carrierIntegerOperand_i64 == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsByCompiler TrustIr.GenericCoro.gepOffset_singleton_keys == [] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.heldGEP_i64_index == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.encodeMemoryWithFunctions_i64 == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.GenericCoro.bindInstructionResults_store == [Quot.sound] modern [Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.instructionResultTypes_declared == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.targetEntry_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.publishFresh_run == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.publishState_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.publishState_world == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.publishState_lookup_same == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.publishState_lookup_other == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.replaceSSA_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.replaceSSA_world == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.replaceSSA_lookup == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.lookupValue_run == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.expandedValues_held == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.expandedValues_effect == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.suspend_entry_operands == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.GraphNames.different_original == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.expandedGraph_effect == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.callEntry_succ == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.callEntry_zero_depth == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.withFunction_found == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.callEntry_eq_of_runCallReq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.expandedGraph_callEquivalent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.functionsOfExpansion_correct == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Controls.dense_graph_uses_actual_gaps == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Controls.sparse_graph_uses_low_gaps == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Controls.maximum_u32_graph_stays_serializable == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Controls.maximum_u32_actual_call_equivalence == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Controls.unvisited_rows_reserve_identifiers == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Controls.undeclared_yield_and_unused_rows_are_reserved == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Controls.missing_yield_retains_complete_call_contract == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Controls.source_metadata_cycle_is_propagated == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Controls.cyclic_metadata_refuses_before_expansion == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Controls.zero_block_fuel_precedes_missing_cfg == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Controls.zero_depth_preserves_parameter_arity_error == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Controls.zero_depth_preserves_undefined_argument == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Controls.zero_depth_precedes_callee_lookup == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.expandedGraph_runCallEquivalent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

end AxiomAudit
end TrustIr

-- Contextual aggregate operand transport and non-partial Undef.
#trustIrAxiomsByCompiler TrustIr.checkAggregateLane_tuple_transport == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.checkAggregateLane_record_transport == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.checkAggregateLane_nested_poison_is_not_inspected == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.checkAggregateLane_immediate_poison_refused == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.checkAggregateLane_wrong_bool_carrier_refused == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.checkAggregateLane_wrong_integer_width_refused == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.stepInstWithContext_nonpartial_undef == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.makeAggregateValueWithContext_transports_unwritten_tuple == [propext, Quot.sound] modern [propext, Classical.choice]

-- Host-supplied raw pointer carrier and operation-specific integer exposure.
#trustIrAxiomsPinned TrustIr.rawPointerInteger_run == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.derivedPointerInteger_unchanged == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.rawPointerInteger_width_error_first == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.rawPointerInteger_success == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ptrToInt_raw_lookup == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.rawPointerInteger_in_range == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.raw_far32_to_u128 == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.raw_far32_to_u32 == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.raw_far32_to_usize == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.raw_u64_max_to_u128 == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.raw_u64_overflow_refused == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.derived_far32_still_refused == [propext, Classical.choice, Quot.sound] modern [propext]

-- Exact compressed-index logical view, storage and cost laws.

#trustIrAxiomsPinned TrustIr.NatIndexTree.depth_insert_eq == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexTree.keyDepthFast_eq == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexTree.nodeCount_empty_insert == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexTree.nodeCount_insert == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexTree.newPathSteps_le_keyDepth == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexStorage.KeyDepthCertificate == [] modern []

#trustIrAxiomsPinned TrustIr.NatIndexStorage.DepthCertificate == [] modern []

#trustIrAxiomsPinned TrustIr.NatIndexStorage.keyDepth_certificate == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.NatIndexStorage.KeyDepthCertificate.eq_depth == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.NatIndexStorage.DepthCertificate.eq_view == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexStorage.depth_certificate == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexStorage.toTree_ofTree == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.NatIndexStorage.toTree_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexStorage.toTree_even == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexStorage.toTree_odd == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexStorage.toTree_find == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexStorage.toTree_insert == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexStorage.find_insert == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexStorage.lookupSteps_le_depth == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexStorage.nodeCount_le_view == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexStorage.depth_le_view == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndexStorage.ofTree_find == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndex.tree_ofTree == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndex.depth_eq_tree == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndex.tree_find == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndex.tree_outsideBound == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndex.find?_ofTree == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndex.depth_ofTree == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndex.keyBound_ofTree == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndex.inserted_tree == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndex.inserted_keyBound == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.NatIndex.inserted_depth == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- Successful instruction freshness and actual invoke restoration.

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.ite_fresh == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.except_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.rejectPartial_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.rejectPoisonValues_fresh == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.bindFreshPair_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.nextFloatZeroChoice_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.addrOfInt_fresh == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.bindPointerInteger_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.bindPointerIntegerWithProvenance_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semCast_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.SSAFreshInstructions.semBinOpDeterministic_fresh == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semBoolBinOpInst_fresh == [propext] modern [propext]

#trustIrAxiomsByCompiler TrustIr.SSAFreshInstructions.semUnOp_fresh == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semOverflow_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semICmpInst_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsByCompiler TrustIr.SSAFreshInstructions.semFCmpInst_fresh == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semOpenFrame_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semBindSlot_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semLoadSlot_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semCloseFrame_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semBr_fresh == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semCondBr_fresh == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semReturn_fresh == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.SSAFreshInstructions.semFloatMinMaxAt_fresh == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semFloatMinMaxScalarValue_fresh == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semFloatMinMaxLanes_fresh == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semFloatMinMaxValues_fresh == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semFloatMinMax_fresh == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semBinOp_fresh == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.lookupLanes_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semExtractField_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semInsertField_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semMakeAggregate_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semArraySplat_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semSeqMapAddK_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semSeqMapNot_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.context_elementIndex_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsByCompiler TrustIr.SSAFreshInstructions.semExtractElementUsing_fresh == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.SSAFreshInstructions.semInsertElementUsing_fresh == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semExtractElement_fresh == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.SSAFreshInstructions.semInsertElement_fresh == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.SSAFreshMemory.fromMemoryExcept_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshMemory.getState_bind_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshMemory.setState_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshMemory.semStoreUsing_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshMemory.semGEPUsing_fresh == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshMemory.semAllocateUsing_fresh == [Quot.sound, propext, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshMemory.expectPointer_fresh == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshMemory.targetAddress_fresh == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshMemory.checkTargetRange_fresh == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshMemory.declaredOrNaturalAlign_fresh == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshMemory.accessAlign_fresh == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshMemory.checkedAccess_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshMemory.semLoadUsing_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshMemory.semAllocaUsing_fresh == [Quot.sound, propext, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshMemory.semHeapAllocUsing_fresh == [Quot.sound, propext, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshOwnership.getPermission_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshOwnership.setPermission_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshOwnership.borrowOperand_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshOwnership.getAllocIdFromPtrARC_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshOwnership.requireArcRef_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshOwnership.requireObjectBase_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshOwnership.deallocARC_fresh == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshOwnership.semBorrow_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshOwnership.semBorrowMut_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshOwnership.semEndBorrow_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshOwnership.semIsUnique_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshOwnership.semRetain_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshOwnership.semRelease_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshAtomic.semAtomicLoadUsing_fresh == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshAtomic.semAtomicStoreUsing_fresh == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshAtomic.semAtomicRMWUsing_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshAtomic.semCmpXchgExchangeUsing_fresh == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.SSAFreshAtomic.semCmpXchg_fresh == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.SSAFreshAtomic.semFence_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshMemoryExtra.accessAddr_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshMemoryExtra.bulkByteCount_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshMemoryExtra.bulkPointer_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshMemoryExtra.semMemCopy_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshMemoryExtra.semMemSet_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshMemoryExtra.semDealloc_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshMemoryExtra.semGlobalAddr_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshMemoryExtra.semGlobalAddrUsing_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshMemoryExtra.semPtrData_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshMemoryExtra.semPtrMetadata_fresh == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshMemoryExtra.semPtrFromParts_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsByCompiler TrustIr.SSAFreshDispatch.semAssertFail_fresh == [] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshDispatch.semCoroSuspend_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshDispatch.throwUB_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshDispatch.throwTypeError_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshDispatch.throwUnsupported_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshDispatch.semSwitch_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshDispatch.stepInst_fresh == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshContext.stepInstWithContext_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.finishInvokeReturnWith_eq == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.invokeCatch_run == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.finishInvokeWith_eq_of_effectRelation == [] modern []


-- Prepared aggregate memory preserves the actual SSA high-water invariant.

#trustIrAxiomsPinned TrustIr.SSAFreshAggregate.loadValue_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshAggregate.storeValue_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshAggregate.load_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshAggregate.store_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshAggregate.atomicLoad_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshAggregate.atomicStore_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshAggregate.atomicRMW_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshAggregate.cmpXchgExchange_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SSAFreshAggregate.semGlobalAddrInContext_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
-- Body unwinding freshness and complete terminator resolver congruence.

#trustIrAxiomsPinned TrustIr.SSAFreshUnwindBody.tryCatch_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.SSAFreshUnwindBody.semAllocException_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshUnwindBody.semRaise_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshUnwindBody.raiseIfUnwind_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SSAFreshUnwindBody.semLandingPadWith_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.closureTermWithContext_congr == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.stepTermWithContext_congr == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]


-- Actual list iteration and held-cell allocation preserve SSA frames.

#trustIrAxiomsPinned TrustIr.SSAFreshLoops.forIn_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.allocateCell_equivariant == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.allocateCell_fresh == [] modern []


-- Generic selected-entry prefix simulation: exact observed dependencies.

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.producedStepRaw == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.producedStepRaw_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.bodyDispatch == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalBodyStep_dispatch == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.semLandingPadWith_congr == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalBodyStep_congr == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.bodyCall_fresh == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.bodyIndirect_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.producedStep_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalBodyStep_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalBody_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.runCallEquivalent_of_selectedEffects == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.callEquivalent_of_runCallEquivalent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.callEquivalent_of_selectedEffects == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.bind_same == [Quot.sound] modern [Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.throw_bind_sem == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.run_throw_sem == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.run_get_sem == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.run_set_sem == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.bind_match_except == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.bind_match_option == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.bind_match_unit == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.bind_ite_sem == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsByCompiler TrustIr.GenericCoro.Prefix.typedClosure_ite == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.GenericCoro.Prefix.forIn_equivariant == [] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.finishCalleeWith == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.finishCalleeWith_eq_of_effectRelation == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.callFrameWith == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.callFrameWith_eq_of_effectRelation == [Quot.sound] modern [Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.checkReturns == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.checkReturns_equivariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.checkReturns_scoped == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.checkReturns_scoped_function == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.callFrameWith_checkReturns_bind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.callFrameWith_arity_bind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.CalleeEffects == [] modern []

#trustIrAxiomsByCompiler TrustIr.GenericCoro.Prefix.bodyCall == [] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalBodyStep_call == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.scopedContext_forFunction == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.bodyCall_congr == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.HeaderRelated == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.HeaderAgreement == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.scopedContext == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.headerAgreement_refl == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.headerAgreement_withFunction == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.HeaderRelated.resultHeaders == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.resultTypeHeaders_congr == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.constValueAtWithDefs_withLocalTypes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.checkClosureValueAt_withLocalTypes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.checkClosureValue_withLocalTypes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.constValueAtWithDefs_scoped == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.checkClosureValue_scoped == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.makeAggregateValueWithContext_scoped == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.functionCall_congr == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.checkedClosureCaptures_scoped == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.closureExtract_scoped == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.closureInsert_scoped == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.makeClosureValue_congr == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.closureCall_congr == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.PrefixControls.graph == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PrefixControls.selectedTarget == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PrefixControls.actual_factory_expands_nonempty_entry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.PrefixControls.prefix_destination_is_retained == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.PrefixControls.unused_trailing_rows_are_reserved == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.PrefixControls.actual_prefix_rows_are_normalized_before_append == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.PrefixControls.full_prefix_and_macro_are_retained == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.expandedGraph_prefix_runCallEquivalent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.expandedGraph_prefix_callEquivalent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.functionsOfExpansion_prefix_correct == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalLayer_sourceEntry_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalLayer_targetEntry_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.resolvedEntry_typesAgree == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.effect_after_fresh_prefix == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.suspend_prefix_operands == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.expandedPrefix_effect == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.callFrameWith_run == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.callFrameWith_equivariant == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.callFrameWith_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.callFrame_with_checkReturns == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.callFrame_equivariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.callFrame_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.resolveDrop_operands == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.resolveDrop_scoped == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.resolveBlock_scoped == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.bodyInsts_resolve == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.graphNode_ids == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.resolvedRow_typesAgree == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.entry_body_mem_graphNodes == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.expandedGraph_prefix_layer_effect == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.rawIndirectArguments == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.rawIndirectArgumentsWith == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.rawIndirectArguments_bind == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.rawIndirectArguments_congr == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.indirectArguments == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.indirectArgumentsWith == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.indirectArguments_bind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.indirectArguments_congr == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.indirectAddress == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.bodyIndirect == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalBodyStep_indirect == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.bodyIndirect_congr == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.effectRelation_refl == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evaluatorAt == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.SameGraphs == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.SelectedEffects == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.calleeEffects_of_update == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evaluator_simulation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.bodyInsts_normalized_append == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.graphNodes_prefix_sourceEntry == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.graphNodes_prefix_expandedEntry == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.expandedGraph_prefix_inference == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.invokeFrameWith == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.invokeFrameWith_eq_of_effectRelation == [Quot.sound] modern [Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.invokeFrameWith_checkReturns_bind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.invokeFrameWith_checkReturns == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.Recurse == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalBodyStep == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalBody == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalLayer == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.stepNWithContext_succ_layer == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalBody_congrOn == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalLayer_congr == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.OnlyYield == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.onlyYield_pure == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.onlyYield_throw == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.onlyYield_typeError == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.onlyYield_bind == [propext] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalBodyStep_onlyYield == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.onlyYield_bind_eq == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalBody_nil == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalBody_cons == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalBody_append == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalBody_congr == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.GenericCoro.Prefix.forIn_sem_congr == [Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.TypesAgreeOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.TypesAgreeOn.mono == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.TypesAgreeOn.at == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.localResultTypes_borrow_operand == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.mapM_congr_mem == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.integerOperand_congr == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.carrierIntegerOperand_congr == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.elementIndex_congr == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsByCompiler TrustIr.GenericCoro.Prefix.declaredFieldTy_scoped == [] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.checkDeclaredField_congr == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.resultSourceType_congr == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.ssaInstructionResultTypes_congr == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.instructionResultTypes_congr == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.checkInstructionResults_congr == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.bindCallResults_congr == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.bindInstructionResults_congr == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.PrefixProofControls.nonempty_copy_factory_retains_call_contract == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.PrefixProofControls.metadataCycleGraph == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PrefixProofControls.nonempty_prefix_metadata_cycle_is_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.PrefixProofControls.nonempty_prefix_metadata_refusal_retains_contract == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.PrefixProofControls.undefinedYieldGraph == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PrefixProofControls.undefined_yield_and_unused_rows_remain_reserved == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.PrefixProofControls.undefined_yield_prefix_retains_complete_call_contract == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.PrefixProofControls.recursiveSignature == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PrefixProofControls.recursiveHeaders == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PrefixProofControls.recursiveGraph == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PrefixProofControls.recursive_prefix_factory_retains_call_contract == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.PrefixProofControls.actual_copy_pair_preserves_zero_resource_contracts == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.semAllocateUsing_reader_congr == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.GenericCoro.Prefix.forIn_except_congr == [Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.GenericCoro.Prefix.gepOffsetUsing_reader_congr == [Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.lookupInput_key == [propext] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.lookupInputs_keys == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.semGEPUsing_reader_congr == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.seqMapStep == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.seqMapReturns == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.seqMapReturns_equivariant == [Classical.choice, propext, Quot.sound] modern [Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.seqMapElement == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.seqMapElement_scoped == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.GenericCoro.Prefix.seqMapInvoke == [] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.seqMapApply == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.seqMapRun == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.seqMapApplyCallWith == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.seqMapApply_framed == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.seqMapStep_calls == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.seqMapStep_framed == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.seqMapRun_congr == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.seqMapStep_congr == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.producedStep == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.producedStep_congr == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.seqMapElement_equivariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.seqMapElement_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.seqMapRun_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.seqMapStep_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.stepInstWithContext_const_scoped == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.stepInstWithContext_congr == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalTransfer == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalLayer_eq_transfer == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalTransfer_congr == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.captureCheckStep == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.checkClosureValueAt_succ_step == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.captureCheckStep_withLocalTypes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]


-- Complete finite-graph coroutine lowering: exact observed dependencies.

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_duplicate_labels_keep_first_match == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_duplicate_labels_keep_first_match.match_1 == [] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_expands_nonentry_graph == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_infers_all_generated_types == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_installs_both_expanded_blocks == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_installs_both_expanded_blocks.match_1 == [] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Controls.actual_factory_keeps_dropped_raw_ids_undeclared == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Controls.actual_graph_instantiates_factory_inference == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Controls.actual_partial_capacity_is_reported == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Controls.actual_plan_uses_two_distinct_triples == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Controls.actual_source_error_precedes_capacity == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Controls.cyclicGraph == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Controls.empty_graph_needs_no_identifier_capacity == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Controls.entry == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Controls.first == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Controls.graph == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Controls.header == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Controls.outputTag == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Controls.outputTag.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Controls.second == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Expansion == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Expansion.capacity == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Expansion.capacity.inj == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Expansion.capacity.injEq == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Expansion.capacity.sizeOf_spec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Expansion.casesOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Expansion.expanded == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Expansion.expanded.inj == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Expansion.expanded.injEq == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Expansion.expanded.sizeOf_spec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Expansion.noConfusion == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Expansion.noConfusionType == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Expansion.rec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Expansion.recOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Expansion.unchanged == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Expansion.unchanged.inj == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Expansion.unchanged.injEq == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.Expansion.unchanged.sizeOf_spec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.FactoryCorrect == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.FactoryCorrect.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.NoSchedule == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.ProofControls.actual_graph_call_equivalence == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.ProofControls.duplicate_occurrences_have_complete_call_equivalence == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.ProofControls.nonentry_br_graph_has_complete_call_equivalence == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.functions == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.functionsWithDomain == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.functionsWithDomain.match_1 == [propext, Quot.sound] modern [propext, Quot.sound]

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.AllBlocks.functionsWithDomain.proof_1' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocks.functionsWithDomain.proof_1

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.functions_correct == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.functions_defined == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.functions_expanded_of_ready == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.functions_source_error == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.functions_without_suspends == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.withInferredGraph == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocks.withInferredGraph_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksEffect.bind_effect == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksEntry.expandedPrefix_effect_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksInduction.PairedEffects == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksInduction.evaluator_simulation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksInduction.selected_of_paired == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksInference.Plans.inference == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksInference.Plans.inference.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksInference.Supported == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksInference.TraceTyped == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksInference.graphNames == [propext, Quot.sound] modern [propext, Quot.sound]

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_1

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_2

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_3

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_4

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_5

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_6' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_6

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_7' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_7

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_8

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_9' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.AllBlocksInference.graphNames.proof_9

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksInference.lowerRows_inference == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksKept.evalLayer_effect == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksKept.evalLayer_effect.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksLayer.lowerRows_layer_of_transfer == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksSimulation.lowerRows_layer_effect == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.AllBlocksSimulation.lowerRows_runCallEquivalent == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.GraphViews.blockInterface == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.GraphViews.cfgOf_observation == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.GraphViews.cfgOf_observation_of_rows == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.GraphViews.expandFirstEntry_observation == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.GraphViews.expandedEntry_interface == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.GraphViews.expandedEntry_pad == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.GraphViews.expandedGraph_interface == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.GraphViews.expandedGraph_padViews == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.GraphViews.expandedGraph_params == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.GraphViews.padViews_of_interface_rows == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.GraphViews.params_of_interface_rows == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.Controls.arbitrary_high_key_is_retained == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.Controls.duplicate_first_row_wins == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.Controls.empty_graph_is_missing == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.Controls.first == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.Controls.high == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.Controls.neighboring_high_key_is_missing == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.Controls.rows == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.Controls.shadowed == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.Controls.zero_key_is_retained == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.PreparedCFG == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.PreparedCFG.casesOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.PreparedCFG.cfg == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.PreparedCFG.index == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.PreparedCFG.mk == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.PreparedCFG.mk.inj == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.PreparedCFG.mk.injEq == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.PreparedCFG.mk.sizeOf_spec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.PreparedCFG.noConfusion == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.PreparedCFG.noConfusionType == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.PreparedCFG.rec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.PreparedCFG.recOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.indexedCFG == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.indexedCFG_eq_cfgOf == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.indexedCFG_index == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.indexedCFG_lookup == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.insertFirst == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.insertFirst.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.insertFirst_find == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.prepare == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.prepareFrom == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.prepareFrom.eq_1 == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.prepareFrom.eq_2 == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.prepareFrom.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.prepareFrom_lookup == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.prepare_first_row == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.IndexedCFG.prepare_lookup == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.Controls.absence_and_nonpad_are_distinct == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.Controls.actual_pad_entry_ignores_other_cfg_fields == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.Controls.catchAll == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.Controls.catch_all_selector_one == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.Controls.cleanup == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.Controls.cleanupWithTail == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.Controls.cleanup_selector_zero == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.Controls.different_cfgs_have_equal_pad_views == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.Controls.missing == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.Controls.missing_block_keeps_error == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.Controls.present_nonpad_keeps_error == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.Controls.raised == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.Controls.typedCatch == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.Controls.typed_catch_checks_exception_first == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.Controls.typed_catch_keeps_refusal == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.Controls.withoutPad == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.PadView == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.PadViewsAgree == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.closureTermWithContext_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.padView == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.semEnterPad_congr == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.semEnterPad_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.semResumeUnwind_fresh == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.stepTermUnwind_congr == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.stepTermUnwind_fresh == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.stepTermWithContext_congr == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.PadViews.stepTermWithContext_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalTransfer_call_scoped_congr == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalTransfer_indirect_scoped_congr == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalTransfer_invokeIndirect_succ == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.Prefix.evalTransfer_invoke_succ == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.Controls.actual_expanded_metadata_has_three_new_types == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.Controls.actual_shadowed_row_retains_full_inference_contract == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.Controls.actual_source_inference_succeeds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.Controls.beforeRows == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.Controls.earlier == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.Controls.first_lookup_still_selects_earlier_duplicate == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.Controls.names == [propext, Quot.sound] modern [propext, Quot.sound]

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.RowInference.Controls.names.proof_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.names.proof_1

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.RowInference.Controls.names.proof_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.names.proof_2

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.RowInference.Controls.names.proof_3' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.names.proof_3

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.RowInference.Controls.names.proof_4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.names.proof_4

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.RowInference.Controls.names.proof_5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.names.proof_5

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.RowInference.Controls.names.proof_6' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.names.proof_6

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.RowInference.Controls.names.proof_7' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.names.proof_7

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.RowInference.Controls.names.proof_8' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.names.proof_8

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.RowInference.Controls.names.proof_9' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.Controls.names.proof_9

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.Controls.selected == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.Controls.sourceGraph == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.Controls.targetGraph == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.Controls.unused_raw_rows_are_not_declarations == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.Controls.unused_raw_rows_reserve_the_actual_first_holes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.FollowUpControls.currentGraph == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.FollowUpControls.earlier_raw_tails_are_no_longer_in_current_graph == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.FollowUpControls.laterBlock == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames == [propext, Quot.sound] modern [propext, Quot.sound]

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_1' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_1

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_2

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_3' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_3

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_4

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_5' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_5

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_6' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_6

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_7' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_7

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_8' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_8

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_9' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames.proof_9

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.FollowUpControls.laterTarget == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.FollowUpControls.later_rewrite_keeps_dropped_raw_ids_none == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.FollowUpControls.later_target_identifiers_have_supported_origin == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.expandedRow_inference_except_generated == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.expandedRow_prefix_inference == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.expandedRow_valueIds_supported == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoro.RowInference.graphParams_expandedRow == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.Controls.abort_keeps_exact_unwind_error_state == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.Controls.callee_resource_error_is_exact == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.Controls.caller == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.Controls.caller_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.Controls.caught_unwind_restores_from_embedded_throw_world == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.Controls.checkedCorrupt == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.Controls.checker == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.Controls.checker_unwind_is_not_caught_as_callee_unwind == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.Controls.continuation_private_result_effect == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.Controls.corrupt == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.Controls.corrupt_is_not_fresh == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.Controls.nonfresh_callee_and_checker_still_keep_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.Controls.normal == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.Controls.poison_return_nonfresh_check_restores_complete_caller_frame == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.Controls.privateResult == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.Controls.privateResult_effect == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.Controls.returning == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.Controls.unwind == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_congr_on_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_effect_on_fresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_keepsFresh == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_run == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_run.match_1 == [] modern []

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_run.match_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_run.match_2

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.CapacityProgress == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Completion == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Completion.capacity == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Completion.capacity.inj == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Completion.capacity.injEq == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Completion.capacity.sizeOf_spec == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Completion.casesOn == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Completion.noConfusion == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Completion.noConfusionType == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Completion.ready == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Completion.ready.sizeOf_spec == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Completion.rec == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Completion.recOn == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.below == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.below.casesOn == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.below.expand == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.below.keep == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.below.nil == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.below.rec == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.casesOn == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.expand == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.history == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.history_count == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.keep == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.labels == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.nil == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.noSuspends == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.params == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.rec == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.recOn == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.suspendCount_target_zero == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.traceTriple == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Plans.trace_count == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Ready == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Ready.match_1 == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Result == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Result.casesOn == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Result.completion == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Result.cursor == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Result.mk == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Result.mk.inj == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Result.mk.injEq == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Result.mk.sizeOf_spec == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Result.noConfusion == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Result.noConfusionType == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Result.pending == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Result.rec == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Result.recOn == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Result.rows == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Result.trace == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Result.visits == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Rows == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.Trace == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TraceControls.actual_duplicate_trace == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TraceControls.actual_first_occurrence_has_original_graph_names == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TraceControls.actual_later_occurrence_has_original_graph_names == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TraceControls.entry == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TraceControls.later_witness_retains_recorded_fields == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TraceControls.sourceRows == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TraceControls.suspend == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.capacity == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.capacity.inj == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.capacity.injEq == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.capacity.sizeOf_spec == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.casesOn == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.noConfusion == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.noConfusionType == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.ready == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.ready.inj == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.ready.injEq == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.ready.sizeOf_spec == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.rec == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleOutcome.recOn == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleReservation == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.after == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.capacity_excludes_triple == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.casesOn == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.history_bound == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.mk == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.mk.inj == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.mk.injEq == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.mk.sizeOf_spec == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.monotone == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.noConfusion == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.noConfusionType == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.outcome == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.rec == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.recOn == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.visits == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.TripleReservation.work == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.duplicate_labels_get_separate_triples == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.example_capacity_excludes_six == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.expandedEntry_terminator_noSuspend == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.isSuspend == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.isSuspend.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.lowerRows == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.eq_1 == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.eq_2 == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.match_1 == [propext, Quot.sound] modern [propext, Quot.sound]

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.match_2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.match_2

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop_capacity_progress == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop_history_bound == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop_ready == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop_work == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.lowerRows_capacity_excludes_schedule == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.lowerRows_capacity_excludes_schedule.match_1 == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.lowerRows_distinct == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.lowerRows_in_range == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.lowerRows_ready == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.lowerRows_source_unused == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.lowerRows_visit_census_bound == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.lowerRows_visit_domain_bound == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.lowerRows_work == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.no_suspend_needs_no_fresh_names == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.planAllBlocks == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.planAllBlocks_ready_noSuspends == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.planAllBlocks_traceGraphNames == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.reserveTriple == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_1' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_1

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_10' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_10

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_11' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_11

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_12' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_12

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_13' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_13

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_14' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_14

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_15' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_15

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_16' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_16

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_17' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_17

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_18' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_18

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_19' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_19

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_2

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_20' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_20

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_21' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_21

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_22' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_22

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_23' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_23

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_24' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_24

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_25' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_25

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_26' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_26

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_27' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_27

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_28' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_28

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_29' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_29

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_3' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_3

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_30' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_30

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_31' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_31

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_32' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_32

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_33' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_33

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_34' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_34

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_4' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_4

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_5' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_5

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_6' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_6

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_7' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_7

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_8' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_8

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_9' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroAllBlocksPlanner.reserveTriple.proof_9

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.reverseNames == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.second_row_partial_capacity == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.suspendCount == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.suspendCount.eq_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.suspendCount.eq_2 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.suspendCount.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.suspendCount_append == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.traceObservation == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.tripleObservation == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.triple_held_cursor_does_not_restart == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.triple_one_success_capacity == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.triple_ready_holes == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.triple_two_success_capacity == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.triple_zero_success_capacity == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.two_nonentry_occurrences == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksPlanner.two_nonentry_rows_are_actual_expandedEntry == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksTransfer.PairedCallbacks == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksTransfer.effect_refl == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksTransfer.evalTransfer_effect == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksTransfer.invokeFrame_effect == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksTransfer.invokeIndirect_effect == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksTransfer.invokeNormal_effect == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksTransfer.invokeUnwind_effect == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksTransfer.invoke_effect == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Controls.actual_cleanup_entry_keeps_selector == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Controls.cleanupSuspend == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Controls.duplicateRows == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Controls.duplicate_first_match_actual_names == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Controls.duplicate_first_match_pad == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Controls.duplicate_first_match_parameters == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Controls.emptySuspend == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Controls.empty_body_present_nonpad_stays_distinct_from_absence == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Controls.empty_graph_lookup == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Controls.empty_graph_views == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Controls.keptFirstRows == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Controls.missing_block_stays_absent == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Controls.present_nonpad_is_not_missing == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Controls.retained_first_row_lookup_contract == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Controls.retained_first_row_shadows_later_expansion == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Controls.shadow == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Lookup == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Lookup.casesOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Lookup.expanded == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Lookup.extend == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Lookup.kept == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Lookup.missing == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Lookup.rec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.Lookup.recOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.cfg_interface == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.cfg_params == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.interface_rows == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.lookup == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.lookup_none_iff == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.lookup_some == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.padViews == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.planAllBlocks_ready_lookup == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.planAllBlocks_ready_padViews == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.planAllBlocks_ready_params == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.semEnterPad_eq == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroAllBlocksViews.stepTermUnwind_eq == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.below == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.bound == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.casesOn == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.contains_of_member == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.correct == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.distinct == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.index == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.member_of_contains == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.mk == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.mk.inj == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.mk.injEq == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.mk.sizeOf_spec == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.next == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.next_le_census == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.noConfusion == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.noConfusionType == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.rec == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.recOn == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.reserved == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.reservedBefore == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.reservedBound == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Cursor.reservedUnused == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Distinct == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Distinct.below == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Distinct.below.casesOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Distinct.below.cons == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Distinct.below.nil == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Distinct.below.rec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Distinct.brecOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Distinct.casesOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Distinct.cons == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Distinct.length_le_of_subset == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Distinct.nil == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Distinct.rec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Distinct.recOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.after == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.casesOn == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.exhausted == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.fresh == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.fullCursor == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.full_before == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.history == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.inRange == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.key == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.keyCursor == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.length == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.member_preserved == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.mk == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.mk.inj == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.mk.injEq == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.mk.sizeOf_spec == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.monotone == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.noConfusion == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.noConfusionType == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.rec == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.recOn == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.visits == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Reservation.work == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Search == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Search.casesOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Search.key == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Search.mk == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Search.mk.inj == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Search.mk.injEq == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Search.mk.sizeOf_spec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Search.next == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Search.noConfusion == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Search.noConfusionType == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Search.rec == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Search.recOn == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.Search.visits == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.capacity_excludes_schedule == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.duplicates_do_not_add_candidate_visits == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.exact_capacity == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.exhausted_cursor_needs_no_repeat_visit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.first_hole == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.grouped_work == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.grouped_work_control == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.high_keys_do_not_force_a_high_cursor == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.next_hole_skips_no_old_prefix == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.observe == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.prepare == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.prepare.proof_1' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.prepare.proof_1

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.prepare.proof_2' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.prepare.proof_2

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.prepare.proof_3' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.prepare.proof_3

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.prepare.proof_4' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.prepare.proof_4

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.prepareU32 == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.prepare_many_visit_census_bound == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.requests_after_capacity_add_no_candidate_visits == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.reserve == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_1' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_1

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_10' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_10

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_11' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_11

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_12' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_12

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_13' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_13

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_14' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_14

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_15' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_15

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_16' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_16

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_17' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_17

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_18' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_18

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_19' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_19

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_2

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_20' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_20

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_21' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_21

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_22' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_22

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_23' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_23

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_24' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_24

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_25' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_25

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_26' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_26

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_27' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_27

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_28' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_28

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_29' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_29

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_3' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_3

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_30' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_30

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_31' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_31

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_32' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_32

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_33' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_33

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_4' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_4

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_5' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_5

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_6' depends on axioms: [propext, Quot.sound, Classical.choice] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_6

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_7' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_7

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_8

trustIrCanonicalOnly
/-- info: 'TrustIr.GenericCoroFreshCursor.reserve.proof_9' does not depend on any axioms -/
#guard_msgs in
#print axioms TrustIr.GenericCoroFreshCursor.reserve.proof_9

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.reserveMany == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.reserveManyLoop == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.reserveManyLoop.eq_1 == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.reserveManyLoop.eq_2 == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.reserveManyLoop.match_1 == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.reserveManyLoop_capacity == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.reserveManyLoop_length == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.reserveManyLoop_member_preserved == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.reserveManyLoop_work == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.reserveMany_capacity == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.reserveMany_distinct == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.reserveMany_in_range == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.reserveMany_source_unused == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.reserveMany_visit_domain_bound == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.reserveMany_work == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.seek == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.seek.eq_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.seek.eq_2 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.seek.match_1 == [] modern []

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.seek_before == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.seek_key == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.seek_next_none == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.seek_next_some == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.seek_work == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.two_free_ids_exclude_three == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.GenericCoroFreshCursor.zero_domain_needs_no_candidate_visit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]


-- Runtime binding-frame identity, snapshot invalidation and no-revival laws.
#trustIrAxiomsPinned TrustIr.FrameLifetime.close_run == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.open_run == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.bind_run == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.close_alias_load == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.close_alias_bind == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.close_alias_double_close == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.bind_close_load == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.open_does_not_revive_alias == [propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.HistoryExtends.trans == [] modern []

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.open_success_history == [propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.history_restore == [Quot.sound] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.forged_future_identity_can_revive == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.nonfresh_ssa_can_overwrite_snapshot == [] modern [propext]


-- Exact zero-gate bit/byte permutations and original integer unary semantics.
#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.rewire_check == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.bitReverse_value == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.byteSwap_value == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.bitReverse_involution == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.byteSwap_involution == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.bitReverse_boundInput == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.byteSwap_boundInput == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.byteSwap_boundCheck == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]


-- Canonical extract/concat permutation targets and checked request receipts.
#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTTerm.reverseChunks_toNat == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTTerm.reverseChunks_bindings == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTCheckedTerm.bitReverse_request == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTCheckedTerm.byteSwap_request == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.bitReverse_checkedTarget == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.byteSwap_checkedTarget == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.composeBitReverse_target == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]


-- Source-indexed scalar permutation instructions, input guards and actual receipts.
#trustIrAxiomsPinned TrustIr.IntegerPermutationOp.target_semIntUnOp == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.int_unop_step_result == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.int_unop_missing_operand == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.int_unop_guard_error == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.IntegerPermutationSubject.ofType_identity == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.IntegerPermutationSubject.checkedCode_eq_some == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.IntegerPermutationSubject.checkedCode_number == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.IntegerPermutationSite.request_outcome == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.IntegerPermutationSite.request_state == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.IntegerPermutationSite.gate_outcome == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.IntegerPermutationSite.gate_request_value == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]


-- Balanced population-count target and actual scalar opcode.
#trustIrAxiomsPinned TrustIr.TrustIrExpr.populationBits_capacity == [propext, Quot.sound, Classical.choice] modern [propext]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.populationSlice_semantics == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.PopulationPlan.target_toNat == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.PopulationPlan.target_bindings == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTCheckedTerm.popCount_toNat == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTCheckedTerm.popCount_bound == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTCheckedTerm.popCount_request == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTCheckedTerm.popCount_semIntUnOp == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]


-- Original source-indexed scalar CtPop requests and full state.
#trustIrAxiomsPinned TrustIr.PopulationSubject.ofType_identity == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.PopulationSubject.request_target == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.PopulationSubject.request_bound == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.PopulationSubject.request_semIntUnOp == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.PopulationSite.bare_request_outcome == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PopulationSite.request_outcome == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PopulationSite.request_state == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PopulationSite.missing_operand == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PopulationSite.guard_error == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]


-- Balanced population-count gate programs and actual source receipts.
#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.populationExtend_check == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.populationExtend_toNat == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.populationLeaf_check == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.populationLeaf_value == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.PopulationPlan.code_check == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.PopulationPlan.code_toNat == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PopulationSubject.code_check == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PopulationSubject.code_toNat == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PopulationSubject.checkedCode_eq_some == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PopulationSubject.checkedCode_number == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PopulationSite.gate_request_value == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PopulationSite.gate_outcome == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]


-- Exact leading/trailing zero-count targets and actual requests.
#trustIrAxiomsPinned TrustIr.TrustIrExpr.zeroScan_leading == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.zeroScan_trailing == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.zeroScan_complete == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTTerm.zeroBitSet_eval == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTTerm.zeroCountScan_toNat == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTTerm.zeroCountScan_wellFormed == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTTerm.zeroCountScan_bindings == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTCheckedTerm.zeroCount_toNat == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTCheckedTerm.zeroCount_bound == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTCheckedTerm.zeroCount_zero == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTCheckedTerm.zeroCount_request == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTCheckedTerm.zeroCount_semIntUnOp == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]


-- Original leading/trailing zero-count instruction requests and state.
#trustIrAxiomsPinned TrustIr.ZeroCountSubject.ofType_identity == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.ZeroCountSubject.request_target == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ZeroCountSubject.request_bound == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ZeroCountSubject.request_semIntUnOp == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ZeroCountSite.bare_request_outcome == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ZeroCountSite.request_outcome == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ZeroCountSite.request_state == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ZeroCountSite.missing_operand == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ZeroCountSite.guard_error == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ZeroCountSubject.request_zero == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]


-- Narrow leading/trailing zero-count gate scans and original outcomes.
#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.chooseConstant_check == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.chooseConstant_value == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYGateCNF.WordCode.chooseConstant_length == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.ZeroCountDirection.scanCode_check == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.ZeroCountDirection.scanCode_toNat == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.ZeroCountDirection.scanCode_length == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ZeroCountSubject.code_check == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ZeroCountSubject.code_toNat == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ZeroCountSubject.checkedCode_eq_some == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ZeroCountSubject.checkedCode_number == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ZeroCountSite.gate_request_value == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ZeroCountSite.gate_outcome == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]


-- Original production body publication of actual unary requests/gates.
#trustIrAxiomsPinned TrustIr.unaryBody_of_step == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.unaryBody_error == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.IntegerPermutationSite.body_request == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.IntegerPermutationSite.body_gate == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PopulationSite.body_request == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PopulationSite.body_gate == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ZeroCountSite.body_request == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ZeroCountSite.body_gate == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]


-- Complete source-indexed unary body replay and continuation.
#trustIrAxiomsPinned TrustIr.AYUnaryReplay.Site.positive == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.Site.body_request == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.Site.body_error == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.Node.correct == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.Trace.correct == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.Trace.built_correct == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.Trace.continuation_correct == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.Trace.visited_le == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]


-- Actual CFG Return-block replay, parameter binding and fuel precedence.
#trustIrAxiomsPinned TrustIr.AYUnaryReplay.evalLayer_return == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.ReturnBlock.layer_correct == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.ReturnBlock.correct == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.ReturnBlock.built_correct == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]


-- Original control syntax, bounded CFG replay and fuel precedence.
#trustIrAxiomsPinned TrustIr.AYUnaryReplay.Control.stepTerm == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.Prefix.control_error == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.Prefix.unreachable == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.Prefix.transfer == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.CFGTrace.correct == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.CFGTrace.blocks_le == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.CFGTrace.build_zero == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.CFGTrace.built_correct == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.mintedValue_iff_shape == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.values_handles == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.open_success == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.WellMintedState.bind_success == [propext] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.WellMintedState.load_success == [propext] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.WellMintedState.close_success == [propext] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.restore == [Quot.sound, propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.nested_future_rejected == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.SlotsTyped.length == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.SlotsTyped.lookup == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.SlotsTyped.update == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.open_success_signature == [propext] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.bind_success_signature == [propext] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.load_success_declared_signature == [propext] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.load_success_signature == [propext] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.close_success_signature == [propext] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.requested_type_needs_validation == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.inserted_type_needs_validation == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.single_publication_run == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.single_publication == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.result_checks_success_state == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.bind_value_success == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.frame_step_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.frame_body_computed == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.frame_body_error == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.frame_body_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.frame_body_list_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.published_frame_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.params_success == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.checked_params_success == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.lookup_args_success == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.br_transfer_success == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.cond_transfer_success == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.switch_transfer_success == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.return_transfer_success == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.FrameControl.stepTerm == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.FrameControl.action_success == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.FrameControl.term_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.frame_layer_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.frame_cfg_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.transfer_example_grammar == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.incoming_identity_premise_needed == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.fresh_success == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.copy_step_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.select_lanes_minted == [propext] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.vector_select_minted == [propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.select_step_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.select_transport_success == [propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.select_step_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.mintedValue_int == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.mintedValue_float == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.mintedValue_null == [] modern []

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.unary_lane_minted == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.unary_lanes_minted == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.unary_value_minted == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.WellMintedState.unary_success == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.FrameLifetime.bool_binary_minted == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.binary_lane_minted == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.binary_lanes_minted == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.FrameLifetime.binary_value_minted == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.of_choice_erasure == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.binary_success == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.bool_binary_success == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.binary_step_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.binary_action_success == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]


#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.bind_result_dests_success == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.bind_values_core_success == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.bind_values_success == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.bind_instruction_success == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.overflow_success == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.integer_compare_lanes_minted == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.bool_compare_lanes_minted == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.integer_compare_value_minted == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.float_compare_lanes_minted == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.FrameLifetime.float_compare_value_minted == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.integer_compare_success == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.float_compare_success == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.FrameLifetime.mintedValue_pointer == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.cast_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.field_get_minted == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.field_set_minted == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.element_get_minted == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.element_set_minted == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.array_from_lanes_minted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.array_uniform_minted == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.vector_element_get_minted == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.vector_element_set_minted == [propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.lookup_lanes_success == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.make_aggregate_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.array_splat_success == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.extract_field_success == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.insert_field_success == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.element_index_success_state == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.extract_element_success == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.insert_element_success == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.record_lanes_minted == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.enum_lanes_minted == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.contextual_aggregate_value_minted == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.contextual_array_value_minted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.contextual_closure_value_minted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.make_aggregate_step_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.make_closure_step_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.array_splat_step_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.closure_extract_minted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.closure_insert_minted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.extract_field_step_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.insert_field_step_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.pointer_data_minted == [propext] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.pointer_metadata_minted == [propext] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.pointer_from_parts_minted == [propext] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.pointer_data_success == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.pointer_metadata_success == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.pointer_from_parts_success == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.set_union_minted == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.set_intersection_minted == [propext] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.sequence_concat_minted == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.sequence_add_lanes_minted == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.sequence_not_lanes_minted == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.sequence_add_success == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.sequence_not_success == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.sequence_map_request_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.HistoryEffects.bind_history == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.HistoryEffects.KeepsHistory.extends == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.HistoryEffects.semCast_history == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.HistoryEffects.semBinOp_history == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.FrameLifetime.HistoryEffects.contextual_insert_history == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.HistoryEffects.semPtrFromParts_history == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.HistoryEffects.lookupLanes_history == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.ssa_edit_history == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.instruction_results_history == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.checked_params_history == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.frame_step_history == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.frame_body_history == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.frame_body_list_history == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.frame_layer_history == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.frame_cfg_history == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.restore_after_frame_cfg == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.DirectFrameCFG.forFunction == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.DirectFrameProgram.forFunction == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.WellMintedState.call_results_success == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.call_results_history == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.call_frame_success == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.direct_call_body_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.direct_frame_body_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.direct_frame_body_list_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.direct_frame_layer_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.direct_frame_cfg_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.FrameCFG.direct == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.check_returns_readonly == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.checked_call_frame_success == [Quot.sound, propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.indirect_return_frame_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.closure_call_arguments == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.closure_call_arguments_minted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.raw_indirect_arguments_success == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.indirect_arguments_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.indirect_call_body_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.CallFrameCFG.forFunction == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.CallFrameProgram.forFunction == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.call_frame_body_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.call_frame_body_list_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.call_frame_layer_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.call_frame_cfg_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.DirectFrameCFG.calls == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.terminal_call_request_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.terminal_direct_transfer_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.terminal_direct_transfer_cfg_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.call_frame_body_with_callees == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.call_frame_body_list_with_callees == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.TailFrameCFG.forFunction == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.TailFrameProgram.forFunction == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.TailFrameRecursion.callees == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.tail_frame_layer_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.tail_frame_cfg_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.CallFrameCFG.tail == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.CallFrameProgram.tail == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.raw_terminal_request_success == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.indirect_terminal_request_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.raw_terminal_transfer_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.AllTailFrameCFG.forFunction == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.AllTailFrameProgram.forFunction == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.AllTailFrameRecursion.callees == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.all_tail_frame_layer_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.all_tail_frame_cfg_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.TailFrameCFG.indirect == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.TailFrameProgram.indirect == [] modern []

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.invoke_catch_frame_exit == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.restore_frame_after_exit == [Quot.sound, propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.invoke_frame_success == [propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.checked_invoke_frame_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.exception_allocation_frame_success == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.exception_allocation_no_unwind == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.raise_frame_exit == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.enter_pad_frame_success == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.FrameCalleeExit.history == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.invoke_returns_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.invoke_frame_exit == [Quot.sound, propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.checked_invoke_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.resume_unwind_state == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.enter_pad_unwind_state == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.FrameActionExit.history == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.FrameActionExit.callee == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.FrameActionValid.bind == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.frame_action_pure == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.frame_action_of_success_no_unwind == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.CallCheckNoUnwind.bind == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.exception_allocation_frame_action == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.raise_frame_action == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.enter_pad_frame_action == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.open_frame_no_unwind == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.bind_slot_no_unwind == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.load_slot_no_unwind == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.close_frame_no_unwind == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.open_frame_action == [Classical.choice, propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.bind_slot_action == [Classical.choice, propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.load_slot_action == [Classical.choice, propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.close_frame_action == [Classical.choice, propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.lookup_arguments_no_unwind == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.lookup_arguments_action == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.call_frame_with_eq_invoke_abort == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.call_frame_with_error == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.call_frame_with_exit == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.direct_call_frame_eq_checked == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.direct_call_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.direct_call_frame_error == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.direct_call_frame_action == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.StaticFunctionErrors.no_unwind == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.static_function_errors_empty == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.StaticFunctionErrors.forFunction == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.StaticFunctionErrors.scoped == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.prepared_function_errors_static == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decoded_context_errors_static == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.function_call_no_unwind == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.function_arguments_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.function_arguments_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.direct_lookup_no_unwind == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.direct_lookup_frame_action == [propext] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.FrameActionExit.bind == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.ExceptNoUnwind.bind == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.ExceptNoUnwind.mapM == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.char_value_no_unwind == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.char_values_no_unwind == [propext] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.result_source_type_no_unwind == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.instruction_types_no_unwind == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.lift_validation_no_unwind == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.result_checks_no_unwind == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.result_dests_no_unwind == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.instruction_dests_no_unwind == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.call_results_no_unwind == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.instruction_results_no_unwind == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.result_checks_frame_action == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.result_dests_frame_exit == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.call_results_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.instruction_results_frame_action == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.block_params_no_unwind == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.checked_params_no_unwind == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.checked_params_frame_exit == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.direct_header_readonly == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.direct_header_no_unwind == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.direct_header_frame_exit == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.direct_lookup_arguments_exit == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.direct_body_call_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.FrameControl.action_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.FrameControl.action_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.FrameControl.term_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.FrameControl.term_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.ordinary_transfer_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.FrameControl.dispatch_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.target_lookup_arguments_exit == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.invoke_normal_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.invoke_unwind_frame_exit == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.direct_invoke_transfer_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.invoke_request_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.direct_invoke_dispatch_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.indirect_invoke_transfer_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.indirect_invoke_request_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.indirect_invoke_request_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.indirect_invoke_request_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.indirect_invoke_dispatch_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.ExceptNoUnwind.forIn == [] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.ExceptNoUnwind.forM == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.tree_range_no_unwind == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.tree_stored_no_unwind == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.closure_value_at_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.closure_value_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.closure_contract_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.make_closure_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.closure_call_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.CallCheckNoUnwind.forIn == [] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.checked_returns_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.checked_call_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.lookup_value_frame_action == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.indirect_arguments_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.indirect_arguments_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.indirect_body_call_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.checked_closure_captures_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.closure_extract_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.closure_insert_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.unary_value_no_unwind == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.binary_values_no_unwind == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.integer_compare_values_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.float_compare_values_no_unwind == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.unary_action_no_unwind == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.binary_action_no_unwind == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.overflow_action_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.integer_compare_action_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.float_compare_action_no_unwind == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.semCast_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.frame_step_exit_of_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.frame_body_exit_of_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.FrameActionValid.forIn == [] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.frame_body_list_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.unary_body_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.binary_body_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.overflow_body_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.integer_compare_body_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.float_compare_body_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.cast_body_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.copy_body_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.undef_body_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.null_body_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.open_body_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.bind_body_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.load_body_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.close_body_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.aggregate_lane_no_unwind == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.aggregate_value_no_unwind == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.array_value_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.declared_field_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.select_values_no_unwind == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.sequence_add_values_no_unwind == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.sequence_not_values_no_unwind == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_element_index_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.extract_element_action_no_unwind == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.insert_element_action_no_unwind == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.pointer_data_action_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.pointer_metadata_action_no_unwind == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.pointer_parts_action_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.contextual_extract_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.contextual_insert_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.contextual_splat_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.contextual_closure_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.contextual_aggregate_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.contextual_select_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.FrameInstruction.step_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.FrameInstruction.step_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.FrameInstruction.body_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.frame_ordinary_body_list_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.DirectFrameInstruction.body_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.CallFrameInstruction.body_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.frame_call_body_list_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.call_frame_layer_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.call_frame_cfg_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.ordinary_frame_layer_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.ordinary_frame_cfg_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.assert_operand_no_unwind == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.assert_message_no_unwind == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.panic_location_no_unwind == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.assert_failure_no_unwind == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.assert_step_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.assert_step_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.raise_if_unwind_frame_exit == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.assert_body_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.landing_pad_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.landing_pad_body_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.resume_term_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.FrameActionExit.weaken == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.assert_invoke_bare_frame_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.assert_invoke_term_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.ordinary_dispatch_of_term_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.resume_dispatch_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.UnwindFrameCFG.forFunction == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.UnwindFrameProgram.forFunction == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.CallFrameCFG.toUnwindCFG == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.UnwindFrameInstruction.body_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.unwind_frame_body_list_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.UnwindFrameControl.dispatch_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.unwind_frame_layer_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.unwind_frame_cfg_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.exit_unwinding_frame_exit == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.unwind_frame_entry_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.terminal_direct_transfer_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.raw_terminal_transfer_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.terminal_direct_dispatch_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.indirect_terminal_request_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.indirect_terminal_request_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.terminal_indirect_dispatch_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.TerminalFrameCFG.forFunction == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.TerminalFrameProgram.forFunction == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.UnwindFrameCFG.toTerminalCFG == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.AllTailFrameCFG.toTerminalCFG == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.UnwindFrameProgram.toTerminalProgram == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.AllTailFrameProgram.toTerminalProgram == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.TerminalFrameControl.dispatch_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.terminal_frame_layer_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.terminal_frame_cfg_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.terminal_frame_entry_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.DecodeFrameExit.bind == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.DecodeFrameExit.of_no_unwind == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.DecodeFrameExit.no_unwind == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decode_value_minted == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decode_value_model_minted == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decode_float_no_unwind == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decode_char_frame_exit == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decode_vector_lane_frame_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decode_vector_lanes_frame_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decode_scalar_vector_frame_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decode_image_frame_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decode_image_model_frame_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.resolve_decoded_minted == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decode_value_at_frame_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decode_typed_model_frame_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decode_memory_frame_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.function_target_no_unwind == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decode_functions_frame_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.reject_partial_frame_action == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.expect_pointer_frame_action == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.access_align_frame_action == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.checked_access_frame_action == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.load_value_using_frame_exit == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.scalar_load_value_frame_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.fresh_minted_frame_exit == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.scalar_load_step_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.canonical_load_step_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.scalar_load_body_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.canonical_context_load_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.BlockResult.bind == [] modern []

#trustIrAxiomsPinned TrustIr.ByteImage.BlockTreeValid.uniform == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.ByteImage.BlockTreeValid.empty == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.BlockTreeValid.split == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.ByteImage.BlockTreeValid.periodic == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.ByteImage.mapBlocksSpec_valid == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.mapBlocks_valid == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.block_result_frame_iff == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.map_blocks_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.mapped_array_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.BlockResult.error_of_eq == [] modern []

#trustIrAxiomsPinned TrustIr.ByteImage.checkBlocksSpec_errors == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.checkBlocks_errors == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.covered_errors == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.covered_fields_errors == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.covered_variant_errors == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decode_valid == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decodeUnwritten_valid == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.aggregate_covered_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.aggregate_decode_frame_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.aggregate_unwritten_decode_frame_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.prepared_memory_error_policy == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.aggregate_load_value_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_load_value_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_load_step_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_load_body_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.prepared_memory_context_errors == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_errors == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.encode_functions_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.aggregate_encode_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.aggregate_store_value_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.scalar_store_value_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_store_value_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_store_step_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_store_body_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.equal_errors == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.scalar_atomic_load_frame_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.scalar_atomic_store_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.scalar_atomic_rmw_frame_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.scalar_exchange_frame_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.aggregate_equal_no_unwind == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.aggregate_rmw_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.aggregate_exchange_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.atomic_load_step_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.atomic_store_step_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.atomic_rmw_step_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.cmpxchg_step_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.atomic_step_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.atomic_body_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.word_operand_no_unwind == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.word_mul_no_unwind == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.word_add_no_unwind == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.memory_alignment_no_unwind == [Classical.choice, propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.word_allocation_no_unwind == [Quot.sound, propext, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.carrier_integer_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_memory_layout_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.allocate_using_frame_exit == [Quot.sound, propext, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.dealloc_frame_exit == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.allocation_step_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.allocation_body_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.gep_offset_no_unwind == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.gep_address_frame_exit == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.gep_values_frame_exit == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.gep_step_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.gep_body_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.frame_get_bind_exit == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.frame_carry_value_exit == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.bulk_count_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.bulk_pointer_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.memcopy_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.memset_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.bulk_step_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.bulk_body_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.borrow_operand_frame_exit == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.permission_get_frame_exit == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.permission_set_frame_exit == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.borrow_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.borrow_mut_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.end_borrow_frame_exit == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.arc_pointer_frame_exit == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.arc_permission_frame_exit == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.arc_object_base_frame_exit == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.arc_dealloc_frame_exit == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.retain_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.release_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.is_unique_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.ownership_step_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.ownership_body_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.MemoryContextErrors.forFunction == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.MemoryFrameInstruction.body_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.memory_frame_body_list_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.MemoryFrameCFG.forFunction == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.MemoryFrameProgram.forFunction == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.TerminalFrameCFG.toMemoryCFG == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.TerminalFrameProgram.toMemoryProgram == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.memory_frame_layer_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.memory_frame_cfg_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.memory_frame_entry_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.prepared_memory_frame_entry_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.HeaderContextErrors.forFunction == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.HeaderContextErrors.no_unwind == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.header_context_errors_empty == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.decoded_header_fold_errors == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decoded_context_header_errors == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decoded_context_memory_errors == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.seqmap_cell_world_exit == [Quot.sound, propext, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.seqmap_element_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.seqmap_element_check_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.seqmap_invoke_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.seqmap_apply_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.seqmap_elements_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.seqmap_run_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.seqmap_returns_readonly == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.seqmap_returns_no_unwind == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.seqmap_step_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.seqmap_body_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.SequenceFrameInstruction.body_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.sequence_frame_body_list_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.SequenceFrameCFG.forFunction == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.SequenceFrameProgram.forFunction == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.MemoryFrameCFG.toSequenceCFG == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.MemoryFrameProgram.toSequenceProgram == [] modern []

#trustIrAxiomsPinned TrustIr.FrameLifetime.sequence_frame_layer_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.sequence_frame_cfg_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.sequence_frame_entry_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decoded_sequence_frame_entry_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.constValueAtWithDefsIn_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.constUninitFieldsAtWithDefsIn_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.constFieldsAtWithDefsIn_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.constLanesAtWithDefsIn_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.constRecordFieldsAtWithDefsIn_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.checked_constant_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.checked_fields_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.checked_lanes_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_constant_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_uninit_fields_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_fields_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_lanes_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_record_fields_no_unwind == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.frame_readonly_bind_exit == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.global_using_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_global_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_global_step_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_global_body_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.checked_constant_minted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.checked_fields_minted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.checked_lanes_minted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_constant_minted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_uninit_fields_minted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_fields_minted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_lanes_minted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_record_fields_minted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.checked_constant_decode_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_constant_decode_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.checked_constant_step_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_constant_step_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.context_constant_body_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.scalar_layout_no_unwind == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.coro_suspend_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.coro_suspend_term_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.coro_suspend_dispatch_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.static_step_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.static_body_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.unresolved_drop_invoke_dispatch_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.every_body_instruction_admitted == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.every_terminator_admitted == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.resolve_drop_terminator_flag == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.FrameBlockShape.admitted == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.FrameProgramShape.admitted == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.shaped_frame_entry_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decoded_shaped_frame_entry_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FrameLifetime.decoded_frame_shape_check == [] modern [propext]

#trustIrAxiomsPinned TrustIr.FrameLifetime.prepared_function_property == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.converted_function_block_shape == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decoded_context_program_shape == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.shaped_function_frame_exit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decoded_module_frame_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FrameLifetime.decoded_module_empty_frame_exit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.entry_decomposition == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.finishEntry_congr == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.EntryTrace.correct == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.EntryTrace.built_correct == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.EntryTrace.build_zero == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.EntryTrace.build_rejected == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYCastReplay.Carrier.build == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.AYCastReplay.plan == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYCastReplay.Site.build == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TrustIrExpr.SMTSourceInput.build == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYCastReplay.body_request == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYCastReplay.body_error == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYCastReplay.Node.correct == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYCastReplay.Node.build == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYDivisionReplay.Site.build == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.AYDivisionReplay.publishDecoded == [] modern []

#trustIrAxiomsPinned TrustIr.AYDivisionReplay.body_decoded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYDivisionReplay.body_request == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYDivisionReplay.body_error == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYDivisionReplay.Node.correct == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYDivisionReplay.Node.build == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIrEval.runDecodedBatchWith_eq_map == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.DecodedEntryTrace.correct == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.DecodedModuleTrace.correct == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.DecodedEntryTrace.build_zero == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.DecodedModuleTrace.build_zero == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.DecodedBatchEntries.correct == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.DecodedBatchTrace.correct == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AYUnaryReplay.DecodedBatchTrace.consume_correct == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.Ty.bitWidthAtPointerBits == [propext, Classical.choice, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.TargetWidthDefinition.default_unchanged == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TargetWidthDefinition.model_unchanged == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.TargetWidthDefinition.query_unchanged == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.finish_result == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.finish_ok_iff == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.finish_overflow_iff == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.MemoDerivation.empty == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.MemoDerivation.insert == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.solve_derivation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.query_derivation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.present == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.done_result == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.query_finished_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.DerivationControls.forged_cache_is_returned == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.DerivationControls.forged_cache_has_no_derivation == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.DerivationControls.forged_cache_is_invalid == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.DerivationControls.fresh_missing_root_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.Extends.refl == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.Extends.trans == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.weaken == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.MemoDerivation.weaken == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.Bounded.empty == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.Bounded.allocate == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.Extends.allocate == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.Bounded.put == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.Growth.refl == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.Growth.trans == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.PreservesGraph.bind == [] modern []

#trustIrAxiomsByCompiler TrustIr.SourceLayout.PreservesState.forIn == [] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.prepare_derivation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.query_preserves_derivation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.index_eq == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.extends_prepared == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.cached == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.query_session_derivation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.SessionControls.stale_memo_is_derived == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.SessionControls.stale_query_returns_old_cache == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.SessionControls.overwritten_memo_invalid == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.SessionControls.stale_not_reachable == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.SessionControls.normal_first_query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.SessionControls.normal_repeat_query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.SessionControls.normal_repeat_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.execution == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.to_node == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.sequence_body == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.alias_child == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.enumEquation_finish_property == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.scaled_bounds == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.finalizes == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.enum_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.sequence_finalizes == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.query_alias_derivation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.query_enum_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.query_sequence_body == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.query_sequence_scaled_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CombinatorControls.prefix_refusal == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CombinatorControls.body_refusal == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CombinatorControls.alias_exact == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CombinatorControls.alias_child_derived == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CombinatorControls.refused_enum_finalizer == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.CombinatorControls.refused_enum_cannot_execute == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.satisfies == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.SummaryInvariant.empty == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.SummaryInvariant.insert == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.solve_satisfies == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.query_satisfies == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.WordGuarded.rule == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.finish_word_bounds == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.WordBounds.unit == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.WordBounds.never == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.WordGuarded.done == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.WordGuarded.failed == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.WordGuarded.canonicalFields == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.WordGuarded.declaredFields == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.WordGuarded.scaled == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.WordGuarded.enumeration == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.WordGuarded.sequence == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.WordGuarded.unit == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.prepare_word == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.query_preserves_word == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.query_word_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.word_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.cached_word_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.query_word_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.WordInvariantControls.oversized_not_bounded == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.WordInvariantControls.empty_graph_invariant == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.WordInvariantControls.forged_oversized_returned == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.WordInvariantControls.forged_memo_invalid == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.WordInvariantControls.cyclic_alias_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.WordInvariantControls.cyclic_alias_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

-- Node-indexed derivations and mixed-mode layout bounds.

#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.satisfies_at == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.IndexedRule.alias == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.IndexedInvariant.empty == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.IndexedInvariant.insert == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.MemoDerivation.satisfies_at == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.solve_satisfies_at == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.query_satisfies_at == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.SummaryInvariant.indexed == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.IndexedRule.done == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Finalizes.indexed == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.FinishBounds.unit == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.FinishBounds.never == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.FinishBounds.execution == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.mode_alias == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.execution_alias == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.canonicalFields_mode_rule == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.declaredFields_mode_rule == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.scaled_mode_rule == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.enum_mode_rule == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.query_mode_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.MemoDerivation.mode_bounds == [] modern []

#trustIrAxiomsByCompiler TrustIr.SourceLayout.IndexedInvariantControls.byte_only_execution == [propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.IndexedInvariantControls.byte_only_not_shape == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.IndexedInvariantControls.wrong_mode_alias_returns == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.IndexedInvariantControls.wrong_mode_alias_has_no_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.IndexedInvariantControls.cyclic_mode_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.IndexedInvariantControls.cyclic_mode_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

-- Exact target-specific scalar interning and real session histories.

#trustIrAxiomsPinned TrustIr.SourceLayout.ScalarSummary.key_injective == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ScalarSummary.of_finish == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.ScalarSummary.finish_bounds == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.ScalarInvariant.empty == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.ScalarInvariant.lookup == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.ScalarInvariant.weaken == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.ScalarInvariant.put == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.ScalarInvariant.cache == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.ScalarInvariant.derivation_value == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.prepare_scalars == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.query_preserves_scalars == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.scalar_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.cached_scalar_value == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.cached_scalar_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ScalarInvariantControls.requested_scalar == [] modern []

#trustIrAxiomsByCompiler TrustIr.SourceLayout.ScalarInvariantControls.arbitrary_key_collision == [] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.ScalarInvariantControls.colliding_values_differ == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.ScalarInvariantControls.counterfeit_shape_bounded == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.ScalarInvariantControls.counterfeit_query_returns == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ScalarInvariantControls.counterfeit_cache_invalid == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- Exact compiler origins for reachable source-layout root caches.
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.query_selection == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.CompiledRoot.weaken == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.roots_compiled == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.query_compilation_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.query_compilation_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.RootOriginControls.different_types_same_bucket == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.RootOriginControls.first_query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.RootOriginControls.colliding_query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.RootOriginControls.colliding_entries_retained == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.RootOriginControls.colliding_history_compiled == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.RootOriginControls.wrong_type_entry_skipped == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.RootOriginControls.wrong_mode_entry_skipped == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.RootOriginControls.forged_derivation_valid == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.RootOriginControls.forged_matching_entry_returned == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.RootOriginControls.forged_not_reachable == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- Actual aggregate construction retains mode-sensitive guards and copy obligations.
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.IndexedRule.reowner == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Index.nodeMode_node == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Index.nodeMode_dynamic == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.ModeGuarded.indexed == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.ModeGuarded.execution == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.ModeGuarded.done == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.ModeGuarded.failed == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Finalizes.mode_guarded == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.ModeGuarded.canonicalFields == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.ModeGuarded.declaredFields == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.ModeGuarded.scaled == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.ModeGuarded.enumeration == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.ModeGuarded.sequence == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.ModeGuarded.unit == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.mode_guarded == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.IndexedRule.copy_mode == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.IndexedRule.copy_execution == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.ModeInvariant.copy_same == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.ModeInvariant.copy_execution == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.StructCompilation.mode_guarded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.StructCompilation.derivation_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.StructCompilation.reserved_rule == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ClosureCompilation.mode_guarded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ClosureCompilation.derivation_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ClosureCompilation.reserved_rule == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.BuilderModeControls.actual_struct_construction == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.BuilderModeControls.actual_struct_guarded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.BuilderModeControls.execution_accepts_byte_only == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.BuilderModeControls.shape_refuses_byte_only == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.BuilderModeControls.accepted_not_shape == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.BuilderModeControls.actual_shape_reserved == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.BuilderModeControls.actual_execution_reserved == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.BuilderModeControls.actual_closure_construction == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.BuilderModeControls.actual_closure_guarded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.BuilderModeControls.shape_closure_accepts == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.BuilderModeControls.execution_closure_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- Complete actual compiler/session shape and byte bounds.
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeRoot.weaken == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeRoot.copy_rule == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeRoot.derivation_bounds == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.shape_root == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.preserves_modes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.prepare_modes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.query_preserves_modes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.mode_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.CompiledRoot.shape_root == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.query_mode_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.cached_root_mode_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.query_mode_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.execution_first == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.shared_scalar_shape == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.shape_repeated == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.shared_history_modes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.shared_root_retained == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.typed_cached_shape_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.dynamic_shape_query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.dynamic_index_obligation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.dynamic_local_shape_guard == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.dynamic_result_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.sparse_shape == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.sparse_missing_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.cyclic_preparation_modes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.cyclic_shape_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- Ordered aggregate field containment and positive-storage separation.
#trustIrAxiomsPinned TrustIr.SourceLayout.Field.Separated.symm == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.overlap_false_iff_separated == [propext, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.hasOverlap_false_iff_separated == [propext, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldsSeparated.snoc == [Quot.sound, propext] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldsSeparated.reverse == [propext, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldsContained.reverse == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.alignUp_lower_bound == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.PlacementGeometry.empty == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.canonicalFields_steps_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.canonicalFields_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.declaredFields_finish_fields == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.declaredFields_finalizes_separated == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.declaredFields_steps_contained == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.declaredFields_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.FieldGuarded.failed == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.FieldGuarded.canonicalFields == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.FieldGuarded.declaredFields == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.FieldGuarded.sequence == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.field_geometry == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.StructCompilation.field_guarded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ClosureCompilation.field_guarded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.StructCompilation.derivation_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ClosureCompilation.derivation_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.GeometryControls.touching_shape_accepts == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.GeometryControls.touching_execution_accepts == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.GeometryControls.overlapping_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.GeometryControls.out_of_range_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.GeometryControls.empty_inside_storage_accepts == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.GeometryControls.omitted_empty_execution_accepts == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.GeometryControls.omitted_empty_shape_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.GeometryControls.unconditional_alignment_bound_false == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.GeometryControls.canonical_padding_accepts == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.GeometryControls.actual_struct_pair == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.GeometryControls.actual_struct_derivation == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.GeometryControls.actual_struct_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.GeometryControls.actual_closure_pair == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.GeometryControls.actual_closure_derivation == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.GeometryControls.actual_closure_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.GeometryControls.actual_closure_query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.GeometryControls.omitted_positive_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.GeometryControls.canonical_finalizer_accepts_forged_state == [] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.GeometryControls.forged_geometry_false == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.GeometryControls.canonical_finalizer_alone_insufficient == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.GeometryControls.forged_placement_not_derived == [] modern [propext]

-- Actual alignment divisibility, aggregate geometry and zero-sized omission boundaries.
#trustIrAxiomsPinned TrustIr.SourceLayout.alignUp_aligned == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldsAligned.reverse == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldsAligned.weaken == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.AlignmentGeometry.weaken == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.canonicalFields_steps_aligned == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.canonicalFields_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.declaredFields_steps_aligned == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.declaredFields_finish_exact == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.powerOfTwo_nonzero == [propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.declaredFields_initial_facts == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.declaredFields_power_of_two == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.declaredFields_alignment == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.AlignmentGuarded.failed == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.AlignmentGuarded.canonicalFields == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.AlignmentGuarded.declaredFields == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.AlignmentGuarded.sequence == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.alignment_geometry == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.StructCompilation.alignment_guarded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ClosureCompilation.alignment_guarded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.StructCompilation.derivation_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ClosureCompilation.derivation_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.AlignmentControls.zero_divisor_refuses == [] modern [propext]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.AlignmentControls.rounding_overflow_refuses == [] modern [propext]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.AlignmentControls.non_power_divisor_rounds == [] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.AlignmentControls.misaligned_field_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.AlignmentControls.excessive_field_alignment_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.AlignmentControls.nonmultiple_size_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.AlignmentControls.zero_aggregate_alignment_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.AlignmentControls.nonpower_aggregate_alignment_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.AlignmentControls.packed_query_accepts == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.AlignmentControls.actual_packed_construction == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.AlignmentControls.actual_packed_derivation == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.AlignmentControls.actual_packed_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.AlignmentControls.omitted_query_accepts == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.AlignmentControls.actual_omitted_construction == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.AlignmentControls.actual_omitted_derivation == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.AlignmentControls.omitted_alignment_preserved == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.AlignmentControls.omitted_unconditional_cap_false == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.AlignmentControls.closure_all_fields_aligned == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- Canonical enum payload storage, tag separation and actual ordered child derivations.
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.canonical_view == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.canonicalEnum_view == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Field.Separated.translate == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldsSeparated.translate == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldsContained.translate == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldsContained.weaken == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.payload_field_lower_bound == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.variant_size_le_payload == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.placePayload_geometry == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.canonical_geometry == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.canonical_tag_separated == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.enum_children_geometry == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.canonicalEnum_geometry == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.canonical_tag == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.canonicalEnum_tag_separated == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.canonicalEnum_geometry == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.canonicalEnum_tag_separated == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGeometryControls.variant_children_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGeometryControls.actual_graph_query == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGeometryControls.actual_graph_geometry == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGeometryControls.actual_graph_tag_separated == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGeometryControls.source_shape_query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGeometryControls.source_execution_query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.EnumGeometryControls.mutually_exclusive_variants_share_storage == [] modern [propext]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.EnumGeometryControls.raw_finalizer_accepts_corrupt_child == [] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGeometryControls.corrupt_child_geometry_false == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGeometryControls.corrupt_enum_geometry_false == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGeometryControls.corrupt_tag_still_separated == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

-- Descriptor enum storage, checked tag/niche lanes and actual child-collection contracts.
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.descriptor_finish == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.descriptor_checks == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.descriptorEnum_view == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.enum_children_property == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.descriptor_exact == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.descriptor_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.direct_lane == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.direct_tag_separated == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.niche_lane == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.niche_carrier == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.niche_other_fields_separated == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.enum_children_length == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.descriptorEnum_header == [propext, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.descriptorEnum_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.descriptorEnum_variant_count == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.descriptorEnum_direct_separated == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.niche_range_bounds == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.descriptorEnum_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.descriptorEnum_niche_carrier == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.descriptorEnum_niche_separated == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.descriptorEnum_direct_separated == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.descriptorEnum_niche_carrier == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.descriptorEnum_niche_separated == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.direct_children == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.direct_graph_query == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.direct_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.direct_source_shape == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.direct_source_execution == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.direct_overlap_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.unaligned_tag_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.out_of_range_tag_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.DescriptorEnumControls.niche_construction == [] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.niche_source_shape == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.niche_source_execution == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.niche_lane_within_parent == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.niche_carrier_witness == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.niche_invalid_interval_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.niche_mask_overflow_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.missing_carrier_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.encoded_payload_overlap_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.uncovered_inhabited_row_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.single_inhabited_preserves_rows == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.inactive_offsets_refuse == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.one_untagged_row_accepts == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.multiple_untagged_rows_refuse == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.own_child_geometry == [] modern []
#trustIrAxiomsByCompiler TrustIr.SourceLayout.DescriptorEnumControls.raw_accepts_parent_mismatch == [] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.parent_geometry_false == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.public_parent_mismatch_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.niche_graph_query == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.niche_node_carrier == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.nonempty_encoded_payload_accepts == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.StepsCertified.derivation == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.StepsCertified.invariant == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.satisfies_contextual == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.IndexedRule.contextual == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.IndexedInvariant.contextual == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.MemoDerivation.satisfies_contextual == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.solve_satisfies_contextual == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.query_satisfies_contextual == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.ContextualRule.alias == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.ContextualRule.reowner == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.ParentFieldGuarded.done == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.ParentFieldGuarded.failed == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.ParentFieldGuarded.declaredFields == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.ParentFieldGuarded.descriptorVariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.ParentFieldCertificates.weaken == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.ParentFieldCertificates.child == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.ContextualRule.descriptorEnum_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.ParentFieldCertificates.allocate == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.ParentFieldCertificates.put_below == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.ParentFieldCertificates.reverse == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.enum_certified_children_property == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.field_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.ContextualRule.canonicalEnum_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.direct_certificates == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.direct_contextual_rule == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.parent_mismatch_certificate_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.declared_variant_parent_contract == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.DynamicExtends.refl == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.DynamicExtends.trans == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.Extends.dynamic == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.DynamicExtends.put_below == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.StorageRule.weaken == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.StorageInvariant.contextual == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.StorageInvariant.empty == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.StorageInvariant.insert == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.StorageInvariant.allocate == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.StorageInvariant.put_below == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.StorageInvariant.leaves == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.StorageGuarded.rule == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.StorageGeometry.empty_fields == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.ScalarSummary.storage_geometry == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.StorageGuarded.done == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.StorageGuarded.failed == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.StorageGuarded.canonicalFields == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.StorageGuarded.declaredFields == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.StorageGuarded.scaled == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.StorageGuarded.sequence == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.StorageGuarded.unit == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.StorageRule.alias == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.StorageRule.canonicalEnum == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.StorageRule.descriptorEnum == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.query_storage_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.prepare_storage == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.preserves_storage == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.query_preserves_storage == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.storage_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.query_storage_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.memo_storage_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.query_storage_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.query_field_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.query_enumeration_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.shared_history_storage == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.repeated_cached_storage == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.shared_memo_storage == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.dynamic_result_storage == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGeometryControls.canonical_public_storage == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.direct_public_storage == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.niche_public_storage == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.single_public_storage == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.untagged_public_storage == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.IndexedRule.sequence == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.powerOfTwo_iff_power == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.powerOfTwo_max == [propext, Classical.choice, Quot.sound] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.powerOfTwo_dvd_of_le == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ScalarSummary.power_alignment == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.PowerAlignment.of_finish == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.BoundedAlignment.of_finish == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.canonicalFields_steps_power == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.PowerAlignmentRule.canonicalFields == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.PowerAlignmentRule.declaredFields == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.PowerAlignmentRule.done == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.PowerAlignmentRule.failed == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.PowerAlignmentRule.scaled == [propext, Classical.choice, Quot.sound] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.PowerAlignmentRule.unit == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.tag_alignment_power == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.payload_alignment_power == [propext, Classical.choice, Quot.sound] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.canonical_power_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.PowerAlignmentRule.enumeration == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.PowerAlignmentRule.sequence == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.BoundedAlignment.unit == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.prepare_power_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.preserves_power_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.query_preserves_power_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.power_alignment_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.query_power_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.memo_power_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.query_power_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.query_alignment_nonzero == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.shared_history_power_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.repeated_cached_power_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.shared_memo_power_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.dynamic_result_power_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGeometryControls.canonical_public_power_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.direct_public_power_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.niche_public_power_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.PowerAlignmentControls.forged_child_accepts == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.PowerAlignmentControls.forged_child_power_false == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.PowerAlignmentControls.forged_scaled_accepts == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.PowerAlignmentControls.forged_scaled_multiple_false == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.PowerAlignmentControls.never_alignment_absent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.PowerAlignmentControls.never_power_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.PowerAlignmentControls.power_six_refuses == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.PowerAlignmentControls.power_eight_divides_sixty_four == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.FieldPowers.reverse == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.normalized_alignment_power == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.canonicalFields_steps_field_powers == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.declaredFields_steps_field_powers == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.canonicalFields_field_powers == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.declaredFields_field_powers == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldAlignmentSummary.empty == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldAlignmentSummary.of_geometry == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.failed == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.done == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.canonicalFields == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.declaredFields == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.scaled == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.sequence == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.unit == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.ScalarSummary.field_alignment == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.PersistentRule.weaken == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.PersistentInvariant.contextual == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.PersistentInvariant.empty == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.PersistentInvariant.insert == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.PersistentInvariant.allocate == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.PersistentInvariant.put_below == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.PersistentInvariant.leaves == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.FieldAlignmentGuarded.rule == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.FieldAlignmentRule.alias == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.VariantAlignmentGuarded.failed == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.VariantAlignmentGuarded.canonicalFields == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.VariantAlignmentGuarded.declaredFields == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.VariantAlignmentCertificates.weaken == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.VariantAlignmentCertificates.reverse == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.VariantAlignmentCertificates.allocate == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.VariantAlignmentCertificates.dynamic_weaken == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.VariantAlignmentCertificates.child == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldPowers.translate == [propext, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldsAligned.translate == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.variant_alignment_le_payload == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.canonical_field_alignment == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.descriptor_field_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.FieldAlignmentRule.enumeration == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.prepare_field_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.preserves_field_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.query_preserves_field_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.field_alignment_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.query_field_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.memo_field_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.query_field_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.query_layout_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.query_positive_field_divides == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.query_enum_field_divides == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.shared_history_field_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.repeated_cached_field_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.shared_memo_field_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.AlignmentControls.packed_public_layout_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGeometryControls.canonical_public_field_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.direct_public_field_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.niche_public_field_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldAlignmentControls.actual_empty_child_query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldAlignmentControls.actual_empty_child_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldAlignmentControls.actual_empty_child_power == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.FieldAlignmentControls.raw_enum_empty_shift_accepts == [] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldAlignmentControls.raw_enum_empty_shift_false == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldAlignmentControls.actual_enum_empty_shift_query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldAlignmentControls.actual_enum_empty_shift_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldAlignmentControls.empty_child_cap_exception == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.FieldAlignmentControls.invalid_packed_clamp_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumEncodingGeometry.no_enum == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.canonical_encoding_geometry == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.enum_encoding_geometry == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.EncodingGuarded.rule == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.EncodingGuarded.enumeration == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.EncodingGuarded.failed == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.EncodingGuarded.done == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.EncodingGuarded.canonicalFields == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.EncodingGuarded.declaredFields == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.EncodingGuarded.scaled == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.EncodingGuarded.sequence == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.EncodingGuarded.unit == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.ScalarSummary.enum_encoding_geometry == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.prepare_encoding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.preserves_encoding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.query_preserves_encoding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.encoding_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.query_encoding_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.memo_encoding_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.query_encoding_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.query_physical_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.query_direct_tag_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.query_niche_carrier == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.shared_history_encoding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.repeated_cached_encoding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.shared_memo_encoding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGeometryControls.canonical_public_encoding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.direct_public_encoding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.niche_public_encoding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.single_public_encoding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.untagged_public_encoding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.wrapping_start_accepts == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.wrapping_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.wrapping_sum_exceeds_mask == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.forged_tag_storage_valid == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.forged_tag_geometry_false == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.UniqueDiscriminants.snoc == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.UniqueDiscriminants.reverse == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.metadata_range_length == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.discriminants_go_facts == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.discriminants_facts == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.canonicalTag_fits == [Classical.choice, propext, Quot.sound] modern [propext]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.EnumMetadata.no_enum == [] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.numbered_metadata_length == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumConstruction.metadata == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.enum_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.Equation.MetadataGuarded.rule == [] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.MetadataGuarded.enumeration == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.Equation.MetadataGuarded.failed == [] modern [propext]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.Equation.MetadataGuarded.done == [] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.MetadataGuarded.canonicalFields == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.MetadataGuarded.declaredFields == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.MetadataGuarded.scaled == [propext] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.MetadataGuarded.sequence == [propext] modern [propext]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.Equation.MetadataGuarded.unit == [] modern [propext]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.ScalarSummary.enum_metadata == [] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.prepare_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.preserves_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.query_preserves_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.discriminants_go_eval == [propext, Classical.choice, Quot.sound] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.discriminants_eval == [propext, Classical.choice, Quot.sound] modern [propext]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.tagFits_eval == [] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.tagBits_eval == [] modern []
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.metadata_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.query_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.memo_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.query_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.query_layout_invariants == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.query_value_tag_fits == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.shared_history_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.repeated_cached_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.ShapeModeControls.shared_memo_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGeometryControls.canonical_public_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.direct_public_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.niche_public_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.DescriptorEnumControls.single_public_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.EnumMetadataControls.mixed_effective_labels == [] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumMetadataControls.mixed_value_agreement == [propext, Classical.choice, Quot.sound] modern [propext]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.EnumMetadataControls.signed_tag_selected == [] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumMetadataControls.mixed_labels_unique == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.EnumMetadataControls.implicit_explicit_collision_refuses == [] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumMetadataControls.collision_value_refuses == [propext, Classical.choice, Quot.sound] modern [propext]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.EnumMetadataControls.exhausted_implicit_refuses == [] modern [propext]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.EnumMetadataControls.explicit_reset_after_exhaustion == [] modern [propext]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.EnumMetadataControls.unsigned_tag_negative_refuses == [] modern [propext]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumMetadataControls.actual_query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumMetadataControls.actual_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]
#trustIrAxiomsPinned TrustIr.SourceLayout.EnumMetadataControls.raw_wrong_row_count_accepts == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.EnumMetadataControls.raw_wrong_row_metadata_false == [] modern [propext]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.EnumMetadataControls.raw_wrong_flag_count_accepts == [] modern [propext]
#trustIrAxiomsByCompiler TrustIr.SourceLayout.EnumMetadataControls.raw_wrong_flag_metadata_false == [] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.uninhabitedFacts_derivation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.FactDerivation.sound == [propext, Classical.choice, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.uninhabitedFacts_sound == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.definitionGroups_exact == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.definitionGroups_member == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.firstPositionIndex_exact == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.firstPositionIndex_witness == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.positionIndex_witness == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.numbered_source_member == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.positionIndex_group == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.firstPositionIndex_group == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Index.structPosition_group == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Index.enumPosition_group == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Index.recordPosition_group == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Index.structShapePosition_group == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Index.enumShapePosition_group == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Formula.allHold_member == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.groupedRule_execution_selected == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.groupedRule_shape_selected == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.equations_source == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.uninhabitedFacts_source_induction == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.uninhabitedFacts_source_witness == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.Value.Initialized.not_unwritten == [] modern []

#trustIrAxiomsPinned TrustIr.Value.Initialized.not_poison == [] modern []

#trustIrAxiomsPinned TrustIr.Value.Initialized.aggregate_child == [] modern []

#trustIrAxiomsPinned TrustIr.Value.Initialized.array_child == [] modern []

#trustIrAxiomsPinned TrustIr.Value.Initialized.record_child == [] modern []

#trustIrAxiomsPinned TrustIr.SourceValueMembership.forM_checked_member == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.check_never_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.tuple_checked == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.tuple_child == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.array_checked == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.array_child == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.tuple_shape == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.array_shape == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.never_empty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.tuple_empty_of_field == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.array_empty_of_element == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.struct_checked == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.struct_child == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.record_checked == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.record_child == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.struct_shape == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.record_shape == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.struct_empty_of_field == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.record_empty_of_field == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.enum_checked == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.enum_initialized_payload == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.enum_shape == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.enum_empty_of_variants == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.Controls.unwritten_never_tuple_accepted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.Controls.unwritten_never_tuple_not_initialized == [] modern []

#trustIrAxiomsPinned TrustIr.SourceValueMembership.Controls.initialized_never_tuple_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.Controls.empty_array_initialized == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.Controls.empty_array_never_accepted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.Controls.empty_array_is_not_empty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceValueMembership.Controls.uniform_unwritten_not_initialized == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.numbered_range_lookup == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.numbered_lookup == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.numbered_get == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.numbered_member_iff_get == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.numbered_position_unique == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.numbered_position_bound == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.SourceNodeDenotes.lookup == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.SourceNodeDenotes.functional == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.SourceNodeDenotes.of_lookup == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.sourceNodeType_iff == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.SourceNodeDenotes.bound == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Index.structBase_ofEnvironment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Index.enumBase_ofEnvironment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Index.closureBase_ofEnvironment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.SourceNodeDenotes.struct_alias == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.SourceNodeDenotes.enum_alias == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.SourceNodeDenotes.record_alias == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.SourceEquation.has_source_type == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.uninhabitedFacts_denotes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.uninhabitedFacts_source_type == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.uninhabitedFacts_source_bound == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.uninhabitedFacts_no_source_type == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.SourceLayout.SourceNodeControls.sparse_kinds_remain_distinct == [] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.SourceNodeControls.canonical_alias_keeps_type == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.SourceNodeControls.actual_alias_derives_flag == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.SourceNodeControls.actual_never_seed_derives_flag == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.SourceNodeControls.actual_type_hole_has_no_flag == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.SourceNodeControls.outside_all_regions_has_no_flag == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.inhabitFormula_capture_sound == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.inhabitFormulas_capture_sound == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.source_equation_capture_sound == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.uninhabitedFacts_capture_sound == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.source_type_uninhabited_capture_empty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.variant_uninhabited_capture_field == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.variant_uninhabited_no_initialized_payload == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.contextOf_capture_service == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.contextOf_capture_source == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.contextOf_uninhabited_capture_empty == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CaptureSoundControls.actual_context_prepares == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CaptureSoundControls.actual_record_keys == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.CaptureSoundControls.actual_first_struct_resolves == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CaptureSoundControls.actual_canonical_position_differs == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CaptureSoundControls.actual_alias_struct_empty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CaptureSoundControls.actual_record_empty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CaptureSoundControls.actual_enum_empty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CaptureSoundControls.actual_array_empty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CaptureSoundControls.flagged_struct_payload_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CaptureSoundControls.skewed_context_prepares == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CaptureSoundControls.skewed_source_flag_is_true == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CaptureSoundControls.skewed_value_is_accepted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CaptureSoundControls.skewed_keys_disagree == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CaptureSoundControls.skewed_context_not_associated == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CaptureSoundControls.skewed_type_not_empty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CaptureSoundControls.unsupported_first_record_stays_missing == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CaptureSoundControls.unsupported_first_record_keys_agree == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.CaptureSoundControls.unsupported_first_record_associated == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumTagSelects.functional == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.enum_checked_tag_selection == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.enum_capture_active_flag_false == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.singleInhabitedValid_inactive_flag == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.enum_capture_single_inhabited_active == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.enum_execution_position_resolves == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.enum_shape_position_resolves == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.enum_execution_single_inhabited_active == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.duplicate_context_prepares == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.duplicate_capture_source == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.duplicate_evaluator_selects_first == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.duplicate_execution_selects_second == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.duplicate_shape_selects_first == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.duplicate_selected_row == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.duplicate_layout_guard_accepts == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.duplicate_evaluator_guard_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.duplicate_inactive_value_initialized == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.duplicate_inactive_value_accepted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.duplicate_lookup_agreement_fails == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.equal_duplicates_agree == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.equal_duplicates_execution_resolves == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.equal_duplicates_shape_resolves == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.positive_context_prepares == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.positive_capture_source == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.positive_lookup_agrees == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.positive_selected_value_accepted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.positive_selected_value_initialized == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.ActiveEnumControls.positive_guard_selects_actual_payload == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.enumIdScan_spec == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.enumIdsAdmitted_iff == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.enum_lookup_agrees_of_admission == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.enum_execution_active_of_admission == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumAdmissionControls.empty_admitted == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumAdmissionControls.sparse_ids_admitted == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumAdmissionControls.sparse_permutation_admitted == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumAdmissionControls.identical_duplicate_refused == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumAdmissionControls.altered_duplicate_refused == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumAdmissionControls.nonadjacent_duplicate_refused == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumAdmissionControls.reserved_key_refused == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumAdmissionControls.other_reserved_key_admitted == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumAdmissionControls.sparse_rows_distinct == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumAdmissionControls.raw_duplicate_context_still_prepares == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumAdmissionControls.raw_duplicate_context_has_no_admission == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumAdmissionControls.raw_duplicate_distinctness_impossible == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumAdmissionControls.out_of_range_refused == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumAdmissionControls.wide_out_of_range_refused == [] modern []

#trustIrAxiomsByCompiler TrustIr.SourceLayout.enumPhysicalSelection_eq_original == [] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.enumPhysicalSelection_some == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.enum_physical_omission_refuses_initialized == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.enum_execution_omission_refuses_initialized == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.enum_capture_active_not_omitted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.actual_selection == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.actual_dead_omitted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.actual_live_retained == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.active_value_initialized == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.active_value_accepted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.actual_capture_never_omits_active == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.unwritten_inactive_value_accepted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.unwritten_inactive_not_initialized == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.unwritten_definition_omits_inactive == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.inactive_offset_blocks_selection == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.selected_never_blocks_selection == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.canonical_has_no_physical_skip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.duplicate_context_prepares == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.duplicate_execution_selects_other == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.duplicate_layout_omits_live_capture_row == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.duplicate_value_initialized == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.duplicate_live_capture_accepted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.duplicate_has_no_admission == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.initialization_hypothesis_needed == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PhysicalOmissionControls.nominal_admission_hypothesis_needed == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Index.node_injective == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumSourceAt.above == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumSourceAt.other_slot == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.enum_origin == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.IndexedRule.enum_origin == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumOrigin.flags == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.enum_origin_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Index.enum_selected_source == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.CompiledRoot.enum_selected == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.enum_value_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.query_enum_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.memo_enum_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.query_enum_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.query_enum_flags == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.query_enum_capture_active_flag_false == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.query_enum_capture_active_flag_false == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGraphControls.forged_flags_pass_metadata == [propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGraphControls.forged_flags_have_no_source_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGraphControls.raw_forged_graph_derives == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGraphControls.forged_graph_fails_origin_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGraphControls.raw_forged_memo_is_returned == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGraphControls.forged_memo_has_no_derivation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGraphControls.shape_selects_original_first == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGraphControls.execution_selects_original_matching == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGraphControls.duplicate_shape_position_witness == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumGraphControls.duplicate_execution_position_witness == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.prepare_enum_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.preserves_enum_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.query_preserves_enum_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.enum_selected == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.Plan.Origin.type == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.Plan.Origin.own == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepare_query_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.Service.queryWithWork_result == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.Plan.Origin.enum_view == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.VariantOrigins.live_at == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VariantOrigins.absent_iff == [propext] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.VariantOrigins.length == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.actual_summary_policy == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_plan_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_enum_plan_view == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_enum_plan_source == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_enum_active_payload == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.PlanOriginControls.live_unit_payload == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.PlanOriginControls.ordered_payloads == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.PlanOriginControls.false_flag_cannot_be_absent == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.PlanOriginControls.true_flag_cannot_be_present == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.PlanOriginControls.equal_lengths_do_not_authenticate_order == [propext] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.PlanOriginControls.enum_cannot_use_scalar_plan == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.PlanOriginControls.forged_flags_have_no_actual_summary == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.PlanOriginControls.forged_plan_has_no_actual_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumOrigin.tag_data == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.discriminantIndex == [] modern []

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.enumTagValue == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.enumTagValue_inline == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.EnumEncodingSelects == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.EnumEncodingSelects.of_lookup == [propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.canonicalTag_eval == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.enumTagValue_fitted == [Classical.choice, propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.enumTagValue_residue == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.discriminantIndex_residue == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.discriminantIndex_eval == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.enum_checked_tag_contract == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.enum_tag_integer_contract == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.enum_encoding_of_checked_selection == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_enum_capture_encoding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.CodecSelectionControls.wrong_width_has_selector_witness == [] modern []

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.CodecSelectionControls.wrong_width_refuses_encoding == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.CodecSelectionControls.wrong_width_refuses_checker == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.CodecSelectionControls.encoder_alone_accepts_oversized_raw == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.CodecSelectionControls.oversized_raw_refuses_checker == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.CodecSelectionControls.oversized_raw_has_no_selector == [] modern []

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.CodecSelectionControls.signed_residue_reads_negative == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.CodecSelectionControls.unsigned_residue_stays_positive == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.CodecSelectionControls.signed_128_residue_reads_negative == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.CodecSelectionControls.nonfitting_table_breaks_residue_lookup == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.CodecSelectionControls.wrong_tag_has_no_source_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.Plan.Origin.enum_layout_view == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteLane == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.ImageOverwrite == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ImageOverwrite.extent == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ImageOverwrite.lane == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ImageOverwrite.outside == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumTagPrefix == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumTagPrefix.direct_lane == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumTagPrefix.direct_exists == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumTagPrefix.untagged_index == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumTagPrefix.single_index == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumTagPrefix.niche_lane == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.NichePayloadChecked == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.NichePayloadChecked.untagged_outside == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumEncodingSelects.lookup == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteLane.after_write == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumTagPrefix.untagged_exists == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumTagPrefix.single_exists == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumTagPrefix.niche_untagged_exists == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumTagPrefix.niche_tagged_exists == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.InitializedLane == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecodingSelects == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecodingSelects.untagged == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecodingSelects.single == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecodingSelects.direct == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecodingSelects.niche_tagged == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecodingSelects.niche_untagged == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.InitializedLane.of_materialized == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.InitializedLane.materialized == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.InitializedLane.defaulted == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.image_materialized_length == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.image_materialized_lookup == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteLane.initialized == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decode_encode_integer == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.tag_byte_capacity == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.direct_prefix_decoding_agrees == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.untagged_prefix_decoding_agrees == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.single_prefix_decoding_agrees == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.niche_relative_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.niche_prefix_decoding_agrees == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.niche_payload_decoding_agrees == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumPrefixSound == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.enum_prefix_sound == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_enum_capture_prefix == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.DecoderPrefixControls.initialized_empty_slice_is_not_a_full_lane == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.DecoderPrefixControls.empty_image_cannot_contain_byte == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.DecoderPrefixControls.overlapping_write_changes_tag == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.DecoderPrefixControls.disjoint_write_preserves_actual_tag == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.DecoderPrefixControls.niche_wraparound_reconstructs_position == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.DecoderPrefixControls.out_of_range_first_breaks_inverse == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.DecoderPrefixControls.out_of_range_relative_breaks_inverse == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.DecoderPrefixControls.missing_carrier_can_pass_encoder_guard == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.DecoderPrefixControls.missing_carrier_refuses_decoder == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.DecoderPrefixControls.wrong_extent_has_no_origin == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.DecoderPrefixControls.wrong_alignment_has_no_origin == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsEncoded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VariantEncoded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsEncoded.extent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VariantEncoded.extent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumTagPrefix.extent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_enumeration_steps == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_enumeration_extent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_extent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsAvoidLane == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsEncoded.preserves_lane == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VariantEncoded.fields == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VariantEncoded.preserves_lane == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.EnumEncodingSelects.functional == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumTagPrefix.direct_tag == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecodingSelects.transfer_direct == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecodingSelects.transfer_niche == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumPayloadAvoidsTag == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumUntaggedCarrierReady == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.enum_encoded_selection == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_enum_capture_encoded_selection == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumImageControls.overlapping_payload_changes_selection == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumImageControls.overlapping_retained_range_is_not_separated == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumImageControls.disjoint_payload_keeps_selection == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumImageControls.wrong_child_extent_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumImageControls.wrong_payload_census_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumImageControls.unwritten_transport_retains_extent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumImageControls.forbidden_unwritten_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumImageControls.successful_encoding_does_not_imply_carrier_initialization == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumImageControls.reserved_default_payload_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.Plan.fieldInputTypes == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldBindings == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.VariantBindings == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.VariantBindings.nil == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.VariantBindings.omitted == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.VariantBindings.live == [] modern []

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.Plan.Origin == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.Plan.Origin.leaf == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.Plan.Origin.fields == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.Origin.array == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.Origin.enumeration == [] modern []

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.Plan.Origin.layout_view == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldBindings.length == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldBindings.at == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldBindings.source_at == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VariantBindings.fields_at == [propext] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.Plan.Origin.enum_binding_view == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldBindings.source_child == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VariantBindings.source_at == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VariantOrigins.children_at == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_plan_query_extent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_enum_field_queries == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldBindingControls.same_size_wrong_type_refuses == [] modern []

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.FieldBindingControls.wrong_offset_refuses == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldBindingControls.swapped_same_size_fields_refuse == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldBindingControls.missing_child_refuses == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldBindingControls.dead_row_does_not_compile_never == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldBindingControls.live_row_cannot_disappear == [] modern []

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.FieldBindingControls.right_type_and_offset_do_not_authenticate_size == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.FieldBindingControls.wrong_child_alignment_refuses == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.FieldBindingControls.tuple_types_follow_original_input == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldExtents == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.VariantExtents == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.VariantExtents.nil == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.VariantExtents.omitted == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.VariantExtents.live == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldExtents.at == [propext] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.Plan.Origin.enum_extent_view == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteLane.after_disjoint_write == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.FieldBindings.avoids_lane == [propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.enum_checked_fields_avoid_tag == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_enum_payload_avoids_tag == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_enum_capture_coherent_encoded_selection == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteLane.compose == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteLane.materialized_slice == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.InitializedLane.after_placement == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ImageOverwrite.initialized_child == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.InitializedLane.byte_lane == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsEncoded.preserves_initialized_lane == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsEncoded.retains_initialized_child == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumUntaggedCarrierReady.of_retained_child == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteCoverageControls.actual_child_placement == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteCoverageControls.actual_later_write == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteCoverageControls.nested_carrier_survives == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteCoverageControls.padding_is_not_authorized == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteCoverageControls.clipped_read_needs_bound == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_leaf_materialized == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.initialized_ofList_range == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_leaf_range_initialized == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsEncoded.retains_encoded_leaf == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumUntaggedCarrierReady.of_encoded_leaf == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.LeafCoverageControls.encoded_leaf_carrier_survives == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.LeafCoverageControls.interior_byte_is_actual == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.LeafCoverageControls.wrong_leaf_extent_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.LeafCoverageControls.ordinary_unwritten_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.LeafCoverageControls.allowed_unwritten_does_not_initialize == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsEncoded.nil_iff == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsEncoded.cons_iff == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsEncoded.head == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsEncoded.length == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsEncoded.at == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_fields_steps == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.CoversLane == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.CoversLane.leaf == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.CoversLane.fields == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.CoversLane.bounds == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.CoversLane.initialized == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsEncoded.covered_at_initialized == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumUntaggedCarrierReady.of_covered_field_run == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.enum_encoded_covered_carrier_ready == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_enum_capture_covered_encoded_selection == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldStepControls.nested_coverage_path == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldStepControls.actual_nested_encoding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldStepControls.actual_full_field_run == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldStepControls.nested_read_from_actual_encoding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldStepControls.adjacent_padding_has_no_coverage_path == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldStepControls.selected_middle_field_coverage == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldStepControls.unwritten_step_retains_shifted_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldStepControls.extra_values_refuse == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldStepControls.missing_values_refuse == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Field.Separated.subrange == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.FieldsSeparated.later_at == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldBindings.drop_metadata == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldExtents.drop_metadata == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldBindings.later_avoids_subrange == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.Origin.fields_metadata_view == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.Origin.covers_fields_child == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.LanePath == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.LanePath.leaf == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.LanePath.fields == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.Origin.lane_path_covers == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_lane_path_covers == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_enum_field_siblings_avoid == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_enum_capture_path_encoded_selection == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SiblingGeometryControls.checked_row_separated == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SiblingGeometryControls.actual_siblings_avoid_interior_lane == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SiblingGeometryControls.path_needs_no_parent_layout_premises == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.SiblingGeometryControls.nonempty_overlap_refuses_separation == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.SiblingGeometryControls.type_and_offset_do_not_replace_extent_check == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SiblingGeometryControls.empty_selected_subrange_is_disjoint == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayImageEncoded.preserves == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_array_steps == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.FullyInitialized.empty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.FullyInitialized.append == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.FullyInitialized.tile == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_leaf_fully_initialized == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_array_fully_initialized == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.LeafArrays.fully_initialized == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.fully_initialized_padding_refusal == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.fully_initialized_empty_tile == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.Plan.Origin.array_type == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.Plan.Origin.array_view == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_array_identity == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_array_count == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_array_encoded_census == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_scalar_array_refusal == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_wrong_array_count_refusal == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.Plan.Origin.array_binding_view == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.QueryOriginPolicy == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.QueryOriginPolicy.query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.QueryOriginPolicy.resolve == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceElement == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceElement.row == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceElement.functional == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_array_element_binding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_array_element_query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_wrong_element_refusal == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_array_context_element == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.source_element_signed_byte_refusal == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.source_element_missing_refusal == [] modern []

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.Plan.LeafType == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.Plan.FieldsType == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.Plan.LeafType.not_fields == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.Plan.SourceShape == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.Plan.Origin.source_shape == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_plan_source_shape == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_array_source_view == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_source_array_encoding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.source_array_leaf_refusal == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.source_scalar_fields_refusal == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.empty_tuple_field_shape == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.source_empty_tuple_leaf_refusal == [] modern [propext]

#trustIrAxiomsPinned TrustIr.ByteImage.StridedInitialized == [] modern []

#trustIrAxiomsPinned TrustIr.ByteImage.StridedInitialized.empty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.StridedInitialized.append == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.StridedInitialized.tile == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.InitializedLane.present == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.initialized_of_present == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.InitializedLane.strided == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.strided_initialized_window == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_array_strided == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_array_initialized_slot == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.CoversLane.array == [] modern []

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.ArrayLaneControls.element_lane == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.ArrayLaneControls.nested_array_field_path == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.uniform_retains_lane_and_padding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.dense_retains_lane_and_padding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.split_retains_lane_and_padding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.shifted_periodic_retains_lane_and_padding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.periodic_hidden_poison_not_forced == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.visible_unwritten_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.empty_array_has_no_coverage == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.zero_stride_empty_lane == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.misaligned_repeat_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.functional == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.StepsDerivation.functional == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.functional == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.unique_after_growth == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.scaled_extent == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.scaled_prior_child == [Classical.choice, propext, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.QueryChain == [propext, Classical.choice, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.QueryChain.refl == [propext, Classical.choice, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.QueryChain.queried == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.QueryChain.reachable == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.QueryChain.graph_extends == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.QueryChain.memo_agrees == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.QueryChain.query_agrees_with_prior_memo == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.DeterminismControls.actual_forward_query == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.DeterminismControls.actual_cycle_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.DeterminismControls.actual_ordered_query == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.DeterminismControls.ordered_result_unique == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.DeterminismControls.unrelated_graph_growth_preserves_query == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.DeterminismControls.rewritten_equation_is_not_growth == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.DeterminismControls.forged_cache_returns_wrong_result == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.DeterminismControls.forged_cache_is_invalid == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.DeterminismControls.actual_source_query_chain == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.DeterminismControls.actual_repeat_result == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.DeterminismControls.actual_scaled_product == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.DeterminismControls.actual_zero_count_product == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.DeterminismControls.actual_seed_memo == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.DeterminismControls.actual_typed_query_prior_memo == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.array_equation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.array_scaled_execution == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.CompiledRoot.array_scaled_execution == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.query_array_child == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.query_array_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.query_array_prior_child == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.QueryChain.array_count_scaling == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ArrayOriginControls.actual_array_query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ArrayOriginControls.actual_shape_query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ArrayOriginControls.actual_cached_array_query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ArrayOriginControls.actual_child_memo == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ArrayOriginControls.actual_prior_child_any_count == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ArrayOriginControls.actual_interleaved_scaling == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ArrayOriginControls.actual_zero_count == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ArrayOriginControls.actual_zero_stride == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ArrayOriginControls.actual_missing_type_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ArrayOriginControls.actual_overflow_count_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ArrayOriginControls.actual_noncanonical_target_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.StepsIn == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.ClosedRegion == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.restrict_region == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.closed_region_agrees == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.prepared_region_derivation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.forked_region_memo_agrees == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.forked_array_scaling == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ClosedRegionControls.actual_prepared_scalar_region == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ClosedRegionControls.actual_forked_arrays == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ClosedRegionControls.actual_forks_not_extensions == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ClosedRegionControls.actual_prepared_array_region == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ClosedRegionControls.actual_forked_nested_arrays == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ClosedRegionControls.missing_dependency_can_be_added == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ClosedRegionControls.original_missing_dependency_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ClosedRegionControls.extension_fills_dependency == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ClosedRegionControls.original_has_no_derivation == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.ClosedRegionControls.open_region_is_not_closed == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.ClosedRegionControls.cycle_is_closed == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.ClosedRegionControls.closed_cycle_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypesCompilation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypesCompilation.roots_bound == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.root_bound == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.compiled_root_bound == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.compiled_types_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootFrontierControls.actual_nested_vector_compilation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootFrontierControls.actual_nested_vector_root_bound == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootFrontierControls.actual_repeated_children == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootFrontierControls.actual_repeated_children_bounded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootFrontierControls.actual_scalar_cache_hit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootFrontierControls.actual_cached_root_bound == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootFrontierControls.actual_nominal_execution_root == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootFrontierControls.actual_nominal_shape_root == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootFrontierControls.actual_nominal_both_bounded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.SourceLayout.RootFrontierControls.bounded_nominal_root_can_be_absent == [] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootFrontierControls.actual_refinement_shape_root == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootFrontierControls.actual_closure_shape_root == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootFrontierControls.actual_checked_failure_root == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootFrontierControls.actual_failure_root_bounded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootFrontierControls.forged_cache_returns_outside_root == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootFrontierControls.forged_cache_breaks_scalar_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.ReferenceBounds == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.Complete == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.StepsIn.mono == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.StepsIn.append == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.StepsIn.children == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.references_done == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.references_alias == [] modern []

#trustIrAxiomsByCompiler TrustIr.SourceLayout.Equation.references_scaled == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.SourceLayout.Equation.references_canonicalFields == [] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.references_declaredFields == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.references_enum == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.references_sequence == [] modern []

#trustIrAxiomsByCompiler TrustIr.SourceLayout.Equation.references_canonicalZip == [] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.references_declaredZip == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.references_declaredMapZip == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.ReferenceBounds.empty == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.ReferenceBounds.insert == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.closed_prefix == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.preserves_references == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypesCompilation.preserves_references == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.StructCompilation.references == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ClosureCompilation.references == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.query_reference_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.QueryChain.reference_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ReferenceControls.actual_prepared_graph == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ReferenceControls.actual_prepared_references == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ReferenceControls.actual_array_query_references == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ReferenceControls.actual_cached_query_references == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ReferenceControls.actual_nested_vector_references == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ReferenceControls.actual_struct_construction == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ReferenceControls.actual_struct_references == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ReferenceControls.actual_closure_construction == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ReferenceControls.actual_closure_references == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ReferenceControls.complete_does_not_bound_references == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ReferenceControls.outside_reference_is_rejected == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.ReferenceControls.bounds_do_not_install_equations == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.ReferenceControls.empty_reserved_prefix_is_incomplete == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.ReferenceControls.cycle_references_bounded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ReferenceControls.cycle_prefix_complete == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.ReferenceControls.cycle_closed_without_termination == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.references_variantFields == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumNodesCompilation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.EnumNodesCompilation.references == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.prepare_references == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.reference_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.query_reference_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.prepared_closed_if_complete == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.restrict_prepared_if_complete == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.physical_never_children == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.logical_never_children == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.physical_and_logical_references == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.ordinary_execution_never_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.refused_execution_never_references == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.refused_field_still_bounded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.refused_field_references == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.actual_enum_extent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.actual_enum_prepared_references == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.missing_tuple_validator_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.missing_closure_validator_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.refusing_validators_still_bounded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.source_cycle_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.source_cycle_references == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.forward_array_extent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.forward_query_references == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.forward_cached_references == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.Present == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.DomainCovers == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.DomainCovers.refl == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.DomainCovers.trans == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.present_insert == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.DomainCovers.write == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.DomainCovers.allocate == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.DomainCovers.complete_with_reserved == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.DomainCovers.complete == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CoversGraph == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.CoversGraph.pure == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CoversGraph.get == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CoversGraph.bind == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CoversGraph.forIn == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Installs == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Installs.bind_left == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Installs.bind_right == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Installs.forIn_member == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.domain_covers == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypesCompilation.domain_covers == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.preserves_complete == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypesCompilation.preserves_complete == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.prepare_allocated_present == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.prepare_validators_present == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.prepare_complete == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.query_complete == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.complete_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.closed_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.prepared_closed == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.restrict_prepared == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.mixed_reserved_lookups == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.mixed_complete == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.refusing_validators_complete == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.cyclic_source_complete == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.cyclic_source_closed == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.forward_query_complete == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.forward_cached_complete == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.forward_query_closed == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.array_equation_source == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.CompiledRoot.array_source_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.query_array_prepared_child == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.forked_array_prepared == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.forked_array_layout == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.automatic_forked_array_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.automatic_cached_array_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.missing_zero_array_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.empty_source_row_zero_array_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.cyclic_zero_array_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.excessive_count_refuses_before_zero_stride == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.zero_stride_array_succeeds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedReferenceControls.scalar_target_refusal_precedes_array_source == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.StepsCorrespond == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Corresponds == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.Correspondence == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.StepsCorrespond.mono == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Corresponds.mono == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.StepsCorrespond.self_on == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Corresponds.self_on == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.Correspondence.grow == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.Correspondence.adjoin == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.Correspondence.closed_region == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.transport_nodes == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.corresponding_unique == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.NodeDerivation.below_frontier == [] modern []

#trustIrAxiomsByCompiler TrustIr.SourceLayout.Equation.Corresponds.scaled == [] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Corresponds.alias == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Corresponds.done == [] modern []

#trustIrAxiomsByCompiler TrustIr.SourceLayout.Graph.Correspondence.scaled_roots == [] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.CompiledRoot.array_success_equation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.forked_array_summary == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CorrespondenceControls.aliases_with_colliding_numbers == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.CorrespondenceControls.complete_metadata_transports == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.CorrespondenceControls.same_extent_different_metadata == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.CorrespondenceControls.metadata_mismatch_rejects_correspondence == [] modern []

#trustIrAxiomsByCompiler TrustIr.SourceLayout.CorrespondenceControls.reversed_children_reject_diagonal == [] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.CorrespondenceControls.checks_cannot_be_replaced_by_children == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.CorrespondenceControls.cyclic_graphs_can_correspond == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.CorrespondenceControls.cycle_refusals_keep_local_ids == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CorrespondenceControls.actual_forks_disagree_outside_source == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CorrespondenceControls.actual_array_forks_succeed == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CorrespondenceControls.actual_array_forks_unique == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ActualSummary.array_unique == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_array_layout_unique == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldBindingControls.array_plan_after_byte_preparation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldBindingControls.array_plan_after_wide_and_other_count_preparation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RowsCorrespond == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.RowsCorrespond.same_length == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.RowsCorrespond.mono == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.RowsCorrespond.map == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.RowsCorrespond.zip_left_same == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.RowsCorrespond.zip_right_same == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.StepsCorrespond.append == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.Correspondence.allocate_pair == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.SourceLayout.Equation.Corresponds.canonicalFields == [] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Corresponds.declaredFields == [propext] modern [propext]

#trustIrAxiomsByCompiler TrustIr.SourceLayout.Equation.Corresponds.canonicalZip == [] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Corresponds.declaredMapZip == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Corresponds.sequence == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.FieldCorrespondenceControls.shared_scalar_rows == [] modern []

#trustIrAxiomsByCompiler TrustIr.SourceLayout.FieldCorrespondenceControls.canonical_field_equations == [] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.FieldCorrespondenceControls.allocated_canonical_parents == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.FieldCorrespondenceControls.canonical_queries_keep_types_and_order == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.FieldCorrespondenceControls.canonical_metadata_transports == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.FieldCorrespondenceControls.packed_field_equations == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.FieldCorrespondenceControls.packed_queries_keep_effective_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.FieldCorrespondenceControls.missing_nonzero_offset_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.FieldCorrespondenceControls.omitted_zero_field_retains_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.FieldCorrespondenceControls.transparent_multiple_carriers_refuse == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.FieldCorrespondenceControls.prefix_sequences_correspond_before_initial_failure == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.FieldCorrespondenceControls.prefix_refusal_precedes_deferred_initial_failure == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.FieldCorrespondenceControls.same_extent_field_types_cannot_be_substituted == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.FieldCorrespondenceControls.declared_offsets_cannot_be_shifted == [] modern []

#trustIrAxiomsByCompiler TrustIr.SourceLayout.FieldCorrespondenceControls.truncated_child_rows_are_rejected == [] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.corresponds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypesCompilation.corresponds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.CompiledRoot.corresponds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.forked_typed_summary == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypedCorrespondenceControls.scalar_hit_and_miss_return_same_summary == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypedCorrespondenceControls.scalar_hit_and_miss_have_different_frontiers == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypedCorrespondenceControls.cached_scalar_root_is_reused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypedCorrespondenceControls.cached_scalar_and_fresh_query_are_unique == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypedCorrespondenceControls.scalar_hit_and_miss_are_unique == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypedCorrespondenceControls.nested_vectors_in_disagreeing_graphs == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypedCorrespondenceControls.canonical_tuple_keeps_all_child_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypedCorrespondenceControls.canonical_tuple_full_summary_is_unique == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypedCorrespondenceControls.declared_tuple_uses_shape_children == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypedCorrespondenceControls.nominal_lookup_modes_are_not_conflated == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypedCorrespondenceControls.refinement_shape_keeps_original_reference == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypedCorrespondenceControls.refinement_execution_still_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypedCorrespondenceControls.typed_closure_shape_retains_capture_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypedCorrespondenceControls.typed_closure_execution_still_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypedCorrespondenceControls.unsupported_shape_tuple_still_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypedCorrespondenceControls.invalid_global_tuple_metadata_still_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypedCorrespondenceControls.cyclic_nested_array_still_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ActualSummary.functional == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_plan_layout_unique == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldBindingControls.tuple_plan_after_byte_preparation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldBindingControls.tuple_plan_after_wide_and_array_preparation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Graph.Extends.insert_fresh == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.corresponds_in_extensions == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypesCompilation.corresponds_in_extensions == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.preserves_reserved == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypesCompilation.preserves_reserved == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CompletionCorrespondenceControls.early_original_correspondence_is_unavailable == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.CompletionCorrespondenceControls.array_compilation_keeps_unfilled_reference == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CompletionCorrespondenceControls.array_compilation_keeps_installed_originals == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CompletionCorrespondenceControls.array_outputs_correspond_after_filling == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CompletionCorrespondenceControls.completed_array_queries_succeed == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CompletionCorrespondenceControls.completed_array_derivation_transports == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CompletionCorrespondenceControls.replacing_emitted_equation_is_not_an_extension == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CompletionCorrespondenceControls.missing_reference_compiles_before_installation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CompletionCorrespondenceControls.reference_outputs_correspond_after_installation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CompletionCorrespondenceControls.installed_reference_query_succeeds == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.CompletionCorrespondenceControls.late_cyclic_reference_remains_a_refusal == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.prepare_type_compilation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.prepared_type_summary == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ActualSummary.prepared_type_row == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ActualSummary.array_element_extent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.Origin.source_array_extent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_array_element_extent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.LanePath.array == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedRowControls.backward_row_copies_installed_body == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedRowControls.forward_row_installs_alias == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedRowControls.copied_row_agrees_with_any_actual_query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedRowControls.forward_alias_agrees_with_any_actual_query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedRowControls.self_alias_still_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedRowControls.cyclic_source_row_has_no_finite_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedRowControls.execution_row_aliases_later_nominal_definition == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.PreparedRowControls.execution_nominal_row_agrees_with_any_actual_query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.SourceArrayExtentControls.nested_array_path_without_parent_bound == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceArrayExtentControls.actual_nested_array_path_is_covered == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceArrayExtentControls.actual_nested_array_path_is_bounded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceArrayExtentControls.actual_nested_array_path_initializes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceArrayExtentControls.undersized_parent_has_no_actual_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceArrayExtentControls.forged_child_stride_has_no_actual_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceArrayExtentControls.zero_sized_elements_keep_exact_extent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceArrayExtentControls.zero_count_has_no_logical_lane == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.integer_encoding_residue == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.decode_encode_integer_residue == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.integer_memory_width_aligned == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.encodeMemory_integer_residue == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.decodeMemory_integer_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.integer_memory_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.boolean_memory_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.integer_memory_roundtrip_valid == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.integer_aggregate_leaf_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.boolean_aggregate_leaf_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ScalarCodecControls.negative_i128 == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ScalarCodecControls.target_sized_32 == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ScalarCodecControls.target_sized_64 == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ScalarCodecControls.oversized_u8 == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ScalarCodecControls.char_surrogate_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ScalarCodecControls.valid_char == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ScalarCodecControls.wrong_leaf_width_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ScalarCodecControls.wrong_leaf_extent_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_integer_leaf_of_memory == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decode_leaf_of_bytes == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.encodeMemory_pointer_word == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.decodeMemory_pointer_bytes == [propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.pointer_memory_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.pointer_memory_refuses_overflow == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.pointer_memory_result == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.null_pointer_memory_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.decodeMemory_fat_pointer_words == [propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.encodeMemory_fat_length_words == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.fat_length_memory_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.encodeMemory_fat_vtable_words == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.fat_vtable_memory_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.fat_null_metadata_image == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.fat_null_vtable_memory_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.fat_pointer_memory_refuses_data == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.fat_pointer_memory_refuses_vtable == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.fat_length_store_valid == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.fat_vtable_store_valid == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.pointer_aggregate_leaf_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.null_pointer_aggregate_leaf_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.fat_length_aggregate_leaf_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.fat_vtable_aggregate_leaf_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.fat_null_store_valid == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.fat_null_vtable_aggregate_leaf_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PointerCodecControls.zero_pointer_canonicalizes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PointerCodecControls.forged_provenance_is_not_restored == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PointerCodecControls.dead_allocation_provenance_recovers == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PointerCodecControls.one_past_provenance_recovers == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PointerCodecControls.containment_precedes_one_past == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PointerCodecControls.reference_leaf_recovers_by_address == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PointerCodecControls.length_metadata_is_32_bit_residue == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PointerCodecControls.null_data_retains_length_lane == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PointerCodecControls.data_and_vtable_provenance_are_independent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PointerCodecControls.null_vtable_leaf_roundtrips == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PointerCodecControls.thin_overflow_is_not_truncated == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.PointerCodecControls.fat_data_overflow_is_not_truncated == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.PointerCodecControls.vtable_overflow_is_not_truncated == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.PointerCodecControls.wrong_metadata_kind_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PointerCodecControls.wrong_thin_leaf_extent_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PointerCodecControls.target32_aggregate_fat_guard_precedes_word_overflow == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PointerCodecControls.target64_aggregate_fat_word_overflow_is_ub == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PointerCodecControls.target32_length_metadata_rejects_64_bit_carrier == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.PointerCodecControls.target64_length_metadata_rejects_32_bit_carrier == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_pointer_leaf_of_memory == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_fat_pointer_leaf_of_memory == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteLane.append_left == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteLane.append_right == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteLane.tile_copy == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteLane.tile_slot == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayImageEncoded.dense_slots == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayImageEncoded.uniform_image == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_dense_array_slot == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_uniform_array_slot == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.zero_stride_visible_poison_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.zero_count_hidden_poison_is_unused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.zero_stride_uniform_slot_has_actual_child == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.dense_second_slot_has_selected_child == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayImageEncoded.slots_of_repetition == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayImageEncoded.slots == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_array_slot == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.split_left_boundary_child == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.split_right_boundary_child == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.cyclic_prefix_child == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.cyclic_middle_child == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.cyclic_tail_child == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.cyclic_tail_value_and_padding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.clipped_cycle_does_not_force_poison == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.clipped_cycle_selected_child == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.complete_cycle_forces_visible_poison == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.clipped_tail_forces_visible_poison == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.zero_stride_cyclic_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayLaneControls.zero_stride_cyclic_selected_child == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.WindowRuntime.canonicalImage_size == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.WindowRuntime.canonicalImage_get == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.WindowRuntime.canonicalImage_toList == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.WindowRuntime.canonicalImage_slice_get == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.WindowRuntime.canonicalImage_slice_toList == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.CanonicalWindowControls.nested_views_preserve_source_and_padding == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.CanonicalWindowControls.left_branch_window_preserves_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.CanonicalWindowControls.right_branch_window_preserves_absence == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.CanonicalWindowControls.crossing_window_retains_both_branches == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.CanonicalWindowControls.oversized_request_stays_clipped == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.CanonicalWindowControls.empty_window_has_no_invented_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.CanonicalWindowControls.byte_equality_does_not_equate_constructor_callbacks == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.mapBlocksSpec_decoded_of_periods == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.mapBlocksSpec_decoded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.mapBlocks_decoded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decode_array_slots_of_mapper == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decode_array_slots == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decode_array_slot == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decode_source_array_slot == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_array_decoded_slot == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.array_slot_codec_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_array_slot_codec_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.DecoderSlotControls.periodic_prefix == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.DecoderSlotControls.periodic_middle == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.DecoderSlotControls.periodic_tail_and_outside == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.DecoderSlotControls.nontrivial_gcd_cycle == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.DecoderSlotControls.whole_period_width == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.DecoderSlotControls.ordinary_nested_views == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.DecoderSlotControls.append_descent_and_padding == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.DecoderSlotControls.zero_width_has_logical_slots == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.DecoderSlotControls.zero_count_ignores_callback_error == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.DecoderSlotControls.nonempty_zero_width_forces_callback_error == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.DecoderSlotControls.periodic_errors_keep_left_to_right == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.DecoderSlotControls.incorrect_extent_can_clip == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.DecoderSlotControls.periodic_slot_has_actual_callback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.DecoderSlotControls.ordinary_slot_has_actual_callback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayDecoderControls.tuple_array_keeps_padding_absent == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayDecoderControls.nested_char_retains_raw_word == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayDecoderControls.top_level_char_validation_stays_distinct == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayDecoderControls.zero_stride_decoder_has_actual_slots == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayDecoderControls.zero_count_decoder_does_not_force_child == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayDecoderControls.missing_covered_byte_refuses == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayDecoderControls.parent_extent_mismatch_refuses == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayDecoderControls.selected_child_keeps_padding == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ChildDecoded.extent == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsDecoded.nil_iff == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsDecoded.head == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decode_fields_steps == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsDecoded.length == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsDecoded.at == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteLane.slice == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decode_field_slot == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.field_slot_codec_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.Origin.fields_child_placement == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decode_source_field_slot == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_field_decoded_slot == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.field_slot_codec_bytes_of_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_field_slot_codec_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldDecoderControls.nested_padded_child_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldDecoderControls.padding_survives_later_field == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldDecoderControls.field_positions_are_logical == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldDecoderControls.zero_size_fields_keep_positions == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldDecoderControls.clipped_empty_child_does_not_prove_parent_bounds == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldDecoderControls.forged_empty_offset_has_no_lane == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldDecoderControls.forged_empty_offset_has_no_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldDecoderControls.overlapping_suffix_changes_earlier_value == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldDecoderControls.overlapping_fields_have_no_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldDecoderControls.nested_char_keeps_strict_raw_rule == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldDecoderControls.missing_covered_byte_refuses == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldDecoderControls.parent_extent_mismatch_refuses == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldDecoderControls.array_child_is_observed_pointwise == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldDecoderControls.prepared_child_geometry_includes_padding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldDecoderControls.prepared_child_callback_retains_padding == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VariantDecoded.fields == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecodingSelects.functional == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decode_enumeration_steps == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ChildDecoded.enumeration_steps == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decode_enum_selected_fields == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decode_enum_payload_slot == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.enum_payload_slot_codec_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.Origin.enum_payload_child_placement == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decode_source_enum_payload_slot == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_enum_decoded_payload_slot == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.enum_payload_slot_codec_bytes_of_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_enum_payload_slot_codec_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_enum_capture_payload_codec_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecoderControls.direct_payload_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecoderControls.tag_and_payload_positions_are_distinct == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecoderControls.live_empty_payload_keeps_logical_discriminant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecoderControls.untagged_zero_size_payload_is_present == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecoderControls.single_inhabited_uses_source_position == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecoderControls.default_niche_reads_real_payload == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecoderControls.tagged_niche_maps_to_logical_discriminant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecoderControls.default_niche_carrier_is_not_initialized_by_successful_store == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecoderControls.absent_payload_row_refuses == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecoderControls.uninhabited_flag_refuses_present_row == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecoderControls.signed_tag_uses_logical_table_value == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecoderControls.missing_covered_payload_byte_refuses == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecoderControls.parent_extent_mismatch_refuses == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecoderControls.payload_census_mismatch_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecoderControls.prepared_payload_geometry_includes_padding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecoderControls.selected_payload_callback_keeps_padding == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.toList_eq_of_observations == [Quot.sound] modern [Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.slice_get_eq_of_observations == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.slice_toList_eq_of_observations == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_uniform_array == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ChildDecoded.leaf_bytes_iff == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.selectVariant_eq_of_observations == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecodingSelects.iff_of_observations == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decode_leaf_eq_of_observations == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ChildDecoded.leaf_iff_of_observations == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.integer_child_leaf_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.integer_child_readback_of_encoded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsEncoded.child_lane == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteLane.integer_child_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.field_integer_child_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_field_integer_child_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.array_integer_child_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.enum_integer_child_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_enum_integer_child_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.IntegerReadbackControls.actual_parent_store == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.IntegerReadbackControls.stored_field_readback_without_parent_load == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.IntegerReadbackControls.negative_target32_child == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.IntegerReadbackControls.nested_surrogate_is_raw == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.IntegerReadbackControls.top_surrogate_still_refuses == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.IntegerReadbackControls.scalar_storage_shape_does_not_change_result == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.IntegerReadbackControls.missing_scalar_byte_still_refuses == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.IntegerReadbackControls.extent_is_independent_of_total_byte_reads == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.IntegerReadbackControls.clipped_empty_windows_keep_observations == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.IntegerReadbackControls.million_uniform_slot_readback == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsDecoded.cons == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsDecoded.of_get == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decode_fields_of_children == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ChildDecoded.fields_of_children == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VariantDecoded.of_fields == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decode_enumeration_of_payload == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ChildDecoded.enumeration_of_payload == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecodingSelects.bound == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EnumDecodingSelects.discriminant == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.IntegerFieldReadback.length == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.IntegerFieldReadback.at == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.IntegerFieldReadback.fields_decoded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.integer_fields_decode == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_integer_fields_decode == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.IntegerFieldReadback.enum_payload_decoded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_enum_capture_integer_decode == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.integer_fields_child_decode == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ParentDecoderControls.actual_parent_store == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ParentDecoderControls.whole_prepared_parent_load == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ParentDecoderControls.parent_padding_stays_absent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ParentDecoderControls.strict_nested_parent_load == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.ParentDecoderControls.logical_outputs_are_normalized == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ParentDecoderControls.empty_product_parent_load == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ParentDecoderControls.integer_relation_has_no_missing_outputs == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ParentDecoderControls.bool_is_not_silently_covered == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ParentDecoderControls.successful_child_does_not_erase_parent_extent_check == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ParentDecoderControls.selection_cannot_invent_discriminant == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ParentDecoderControls.actual_enum_payload_run == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ParentDecoderControls.whole_enum_load_from_payload_success == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ParentDecoderControls.strict_nested_enum_load == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ParentDecoderControls.checked_capture_whole_enum_load == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.CompactArray.Leaf.get_exists == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.CompactArray.Tree.get_exists == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.CompactArray.Packed.get_exists == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.BlockResult.map_error == [] modern []

#trustIrAxiomsPinned TrustIr.ByteImage.FailedSlots.congr == [] modern []

#trustIrAxiomsPinned TrustIr.ByteImage.FailedSlots.of_window == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.mapBlocksSpec_failure_of_periods == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.mapBlocksSpec_failure == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.mapBlocks_failure == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.mapBlocks_exists_of_windows == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.MapperFailureControls.visible_callback_failure == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.MapperFailureControls.visible_failure_has_actual_slot == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.MapperFailureControls.hidden_template_error_is_not_forced == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.MapperFailureControls.zero_count_does_not_call_failing_callback == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.MapperFailureControls.zero_width_callback_failure_has_visible_slot == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.MapperFailureControls.wrong_extent_has_no_complete_failure_window == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ChildDecoded.functional == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decode_array_exists_of_mapper == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ChildDecoded.array_exists_of_mapper == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ChildDecoded.array_iff_decode == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_array_geometry == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.decode_array_exists_of_children == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ChildDecoded.array_exists_of_children == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteLane.integer_window_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.integer_array_decode == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.integer_array_child_decode == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayParentControls.million_uniform_parent_decode == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayParentControls.dense_parent_decode == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayParentControls.split_parent_decode == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayParentControls.shifted_periodic_parent_decode == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayParentControls.empty_array_does_not_force_hidden_poison == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayParentControls.zero_stride_parent_keeps_logical_count == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayParentControls.nested_zero_stride_parent_keeps_mode == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ArrayParentControls.clipped_periodic_array_does_not_force_hidden_poison == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ChildDecoded.leaf_iff_decode == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ChildDecoded.ordinary_iff_decode == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarReadbackInput.readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteLane.of_parent_observations == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteLane.window_bytes == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ByteLane.slice_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ValueReadback.aggregate_nil == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.ValueReadback.aggregate_cons == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.ReadbackInput.readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarReadbackInput.character_view == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarReadbackInput.top_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ReadbackInput.top_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_recursive_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_recursive_child_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldReadbackInputs.length == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldReadbackInputs.at == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ReadbackInput.fields_of_pairs == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ReadbackInput.array_uniform == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.source_image_observations == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ReadbackInput.enumeration_of_prefix == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.RecursiveReadbackControls.prepared_mixed_recursive_readback == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.RecursiveReadbackControls.mixed_nested_recursive_readback == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.RecursiveReadbackControls.distinct_byte_representation_readback == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.RecursiveReadbackControls.nested_pointer_uses_receiving_memory == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.RecursiveReadbackControls.fat_metadata_uses_declared_kind == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.RecursiveReadbackControls.nested_zero_pointer_canonicalizes == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.RecursiveReadbackControls.nested_surrogate_stays_raw == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.RecursiveReadbackControls.outer_padding_remains_absent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.RecursiveReadbackControls.arrays_of_mixed_arrays_readback == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.RecursiveReadbackControls.recursive_enum_payload_readback == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.RecursiveReadbackControls.valid_top_character_readback == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.RecursiveReadbackControls.invalid_top_character_has_no_ready_certificate == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.RecursiveReadbackControls.invalid_top_character_still_refuses == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.RecursiveReadbackControls.float_is_not_implicitly_admitted == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.RecursiveReadbackControls.unwritten_is_not_implicitly_admitted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.RecursiveReadbackControls.target32_overflow_has_no_scalar_certificate == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.RecursiveReadbackControls.uninitialized_carrier_has_no_selection_certificate == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.RecursiveReadbackControls.overlapping_plan_has_no_source_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- Function-word aggregate readback and contextual refusal controls.

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_function_leaf_of_memory == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.function_aggregate_leaf_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.null_function_aggregate_leaf_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FunctionReadbackInput.codec == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ReadbackInput.readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ReadbackInput.top_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_recursive_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_recursive_child_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FunctionReadbackControls.prepared_record_and_function_array == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FunctionReadbackControls.target32_function_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FunctionReadbackControls.duplicate_table_uses_first_position == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FunctionReadbackControls.changed_table_changes_target == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FunctionReadbackControls.missing_table_refuses_store == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FunctionReadbackControls.missing_target_refuses_store == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FunctionReadbackControls.mismatched_signature_refuses_store == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FunctionReadbackControls.unknown_word_refuses_load == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FunctionReadbackControls.null_without_table_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FunctionReadbackControls.missing_table_has_no_function_certificate == [] modern []

-- Admission recovered from actual successful ordinary stores.

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_leaf_memory_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.functionAddressOf_success == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FunctionReadbackInput.of_memory_success == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FunctionReadbackInput.of_encoded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ReadbackInput.function_of_encoded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encoded_function_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsEncoded.readback_inputs == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ReadbackInput.fields_of_encoded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ReadbackInput.array_of_encoded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FunctionReadbackPlan.admit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_function_plan_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EncodedAdmissionControls.parent_store_supplies_recursive_admission == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EncodedAdmissionControls.prepared_parent_readback_without_value_certificates == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EncodedAdmissionControls.target32_store_supplies_admission == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EncodedAdmissionControls.distinct_image_exact_function_readback == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EncodedAdmissionControls.table_free_null_store_supplies_admission == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EncodedAdmissionControls.missing_table_cannot_supply_store == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EncodedAdmissionControls.mismatched_signature_cannot_supply_store == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EncodedAdmissionControls.wrong_extent_cannot_supply_store == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.EncodedAdmissionControls.empty_array_ignores_unused_unwritten_template == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- Scalar admission from actual lane checks and successful stores.

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_leaf_fat_valid == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.checked_integer_lane_shape == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.checked_pointer_lane_shape == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarReadbackInput.integer_of_checked_encoded == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarReadbackInput.pointer_of_checked_encoded == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarReadbackInput.boolean_of_checked == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarReadbackInput.unit_of_checked == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.metadata_length64_shape == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.metadata_length32_shape == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.metadata_pointer64_shape == [] modern []

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.metadata_pointer32_shape == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.checked_fat_metadata_shape == [Classical.choice, propext, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.fat_store_guard_shape == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarReadbackInput.fat_of_encoded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarReadbackPlan.input_certificate == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarReadbackPlan.admit == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarReadbackPlan.readback == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.top_char_ready_of_checked_closure == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarReadbackPlan.readback_of_checked_closure == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarAdmissionControls.integer_store_and_lane_check_supply_admission == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarAdmissionControls.target32_signed_transport_supplies_admission == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarAdmissionControls.distinct_byte_image_integer_readback == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarAdmissionControls.pointer_store_supplies_width_and_extent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarAdmissionControls.zero_pointer_canonical_readback == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarAdmissionControls.boolean_checker_supplies_admission == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarAdmissionControls.unit_checker_supplies_admission == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarAdmissionControls.target32_length_store_supplies_metadata_admission == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarAdmissionControls.vtable_store_supplies_both_address_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarAdmissionControls.null_vtable_store_supplies_admission == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarAdmissionControls.pointer_byte_storage_does_not_authenticate_lane == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarAdmissionControls.boolean_byte_storage_does_not_authenticate_lane == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarAdmissionControls.target32_pointer_lane_check_does_not_waive_overflow == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarAdmissionControls.wrong_fat_metadata_still_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarAdmissionControls.nested_surrogate_has_checked_store_admission == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarAdmissionControls.recursive_checker_supplies_valid_top_character == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarAdmissionControls.recursive_checker_refuses_surrogate == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarAdmissionControls.top_surrogate_load_still_refuses == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.ScalarAdmissionControls.float_has_no_implicit_scalar_plan == [] modern [propext]

-- Real recursive source checking derives visible admission through source-bound tuples and arrays.

#trustIrAxiomsPinned TrustIr.AggregateMemory.closure_checked_integer_lane == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.closure_checked_pointer_lane == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.closure_checked_boolean_lane == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.closure_checked_unit_lane == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarReadbackPlan.input_of_source_checked == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarReadbackPlan.admit_of_source_checked == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_ordinary_not_uninit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.Origin.tuple_types_and_children == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.list_zip_member_of_get == [propext, Quot.sound] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackShape.admit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.source_checked_recursive_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_checked_value_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceCheckedAdmissionControls.actual_recursive_checker_accepts_mixed_parent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceCheckedAdmissionControls.one_source_check_supplies_recursive_admission == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceCheckedAdmissionControls.prepared_mixed_source_readback == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceCheckedAdmissionControls.reconstructed_source_image_readback == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceCheckedAdmissionControls.recursive_checker_replaces_separate_scalar_lane_argument == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceCheckedAdmissionControls.empty_array_ignores_unsupported_unused_template_and_row == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceCheckedAdmissionControls.tuple_transport_exception_does_not_supply_ordinary_store == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceCheckedAdmissionControls.partial_carriers_still_refuse_source_check_and_store == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceCheckedAdmissionControls.byte_store_and_checker_do_not_authenticate_field_types == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceCheckedAdmissionControls.forged_field_types_have_no_source_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.SourceCheckedAdmissionControls.visible_array_row_disagreement_cannot_supply_shape == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceCheckedAdmissionControls.actual_checks_and_storage_do_not_waive_visible_row_agreement == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceCheckedAdmissionControls.target32_source_checker_supplies_scalar_admission == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceCheckedAdmissionControls.actual_target32_recursive_checker_accepts_mixed_parent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceCheckedAdmissionControls.prepared_target32_mixed_source_readback == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.zip_fst_exact == [] modern []

#trustIrAxiomsPinned TrustIr.SourceLayout.canonicalFields_steps_types == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.canonicalFields_types == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.SourceLayout.declaredFields_steps_types == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.Executes.declaredFields_types == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.StructSourceAt.above == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.StructSourceAt.other_slot == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Equation.IndexedRule.struct_types == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Index.struct_selected_source == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.struct_origin_invariant == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.CompiledRoot.struct_selected == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.struct_value_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.Reachable.query_struct_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.Plan.Origin.struct_types_and_children == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceNominalReadbackShape.admit == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.source_checked_nominal_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_checked_nominal_value_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceStructAdmissionControls.shape_selects_first_duplicate == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceStructAdmissionControls.execution_selects_matching_duplicate == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceStructAdmissionControls.execution_selects_sparse_id == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceStructAdmissionControls.nested_structs_admitted_from_real_checker_and_store == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceStructAdmissionControls.duplicate_context_disagreement_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceStructAdmissionControls.actual_entry_checks_nested_structs == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceStructAdmissionControls.prepared_nested_struct_readback == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceStructAdmissionControls.complete_external_image_readback == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceStructAdmissionControls.wrong_duplicate_row_fails_real_checker == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.SourceLayout.TypesCompilation.length == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.StructCompilation.field_types == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.struct_selected == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.prepare_struct_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.RootCompilation.preserves_struct_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.SourceLayout.Session.query_preserves_struct_origin == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- Executable source-bound readback policy: soundness, completeness and controls.
#trustIrAxiomsPinned TrustIr.AggregateMemory.selectedStructAgrees_sound == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.sourceReadbackPolicy_sound == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.scalarReadbackPolicy_complete == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.sourceReadbackShape_policy_complete == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.selectedStructAgrees_complete == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.sourceNominalReadbackShape_policy_complete == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.sourceReadbackPolicy_iff == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_policy_checked_value_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.scalar_accepted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.canonical_bool_accepted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.oversized_bool_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.misaligned_unit_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.float_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.pointer_vector_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.pointer_accepted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.char_accepted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.function_accepted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.fat_pointer_accepted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.enumeration_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.record_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.duplicate_selects_execution_row == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.first_duplicate_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.full_row_metadata_bound == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.absent_nominal_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.absent_evaluator_row_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.wrong_array_type_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.absent_array_type_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.array_count_mismatch_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.unused_empty_template_accepted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.unsupported_nested_child_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.nested_nominal_policy_accepted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.prepared_readback_without_manual_shape == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.SourceReadbackPolicyControls.real_origin_policy_equivalence == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.instDecidableEqFieldDef == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.instDecidableEqStructRepr == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.instDecidableEqStructDef == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- Exact float byte codec and ordinary-leaf failure correspondence.
#trustIrAxiomsPinned TrustIr.natToBytesLE_eq_integer_go == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.natToBytesLE_length == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.natOfBytesLE_eq_integer_go == [propext, Quot.sound, Classical.choice] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.natOfBytesLE_natToBytesLE == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.encodeFloatAt_nan_refuses == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.FloatStorageFormat.encode_success_iff == [propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FloatStorageFormat.encode_extent == [propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.FloatStorageFormat.decode_success_iff == [propext, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FloatStorageFormat.encoded_byte_readback == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_float_leaf_result == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_float_leaf_nan_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_float_leaf_wrong_extent == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_float_leaf_success == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_float_leaf_error_iff == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.float_leaf_stored_byte_view == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FloatStorageControls.little_endian_binary16 == [] modern []

#trustIrAxiomsPinned TrustIr.FloatStorageControls.little_endian_binary32 == [] modern []

#trustIrAxiomsPinned TrustIr.FloatStorageControls.little_endian_binary64 == [] modern []

#trustIrAxiomsPinned TrustIr.FloatStorageControls.low_bytes_only == [] modern []

#trustIrAxiomsPinned TrustIr.FloatStorageControls.full_binary16_residue == [] modern []

#trustIrAxiomsPinned TrustIr.FloatStorageControls.empty_byte_residue == [] modern []

#trustIrAxiomsByCompiler TrustIr.FloatStorageControls.binary16_decode_truncated_refuses == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.FloatStorageControls.binary32_decode_oversized_refuses == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.FloatStorageControls.binary64_decode_truncated_refuses == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.FloatStorageControls.binary16_decode_bytes == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.FloatStorageControls.binary32_decode_bytes == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.FloatStorageControls.binary64_decode_bytes == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.FloatStorageControls.nan_precedes_untyped_width == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.FloatStorageControls.nan_precedes_layout_failure == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FloatStorageControls.ordinary_f64_layout_refuses == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FloatStorageControls.ordinary_f16_image == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FloatStorageControls.ordinary_f32_image == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FloatStorageControls.ordinary_f64_image == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FloatStorageControls.successful_f32_store_supplies_byte_view == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FloatStorageControls.ordinary_f16_error_correspondence == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.FloatStorageControls.numeric_readback_policy_not_promoted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_float_leaf_of_type == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- Packed integer/Bool vector codecs and automatic recursive admission.
#trustIrAxiomsPinned TrustIr.VectorReadbackLane.byte_size == [] modern []

#trustIrAxiomsPinned TrustIr.vectorReadbackLane_iff == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.vector_integer_lane_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.vector_integer_lane_decodes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.vector_lane_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.encodeVectorLane_extent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.vector_lanes_roundtrip == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.vector_lane_ready_of_checked == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.vector_source_checked == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.encodeScalarVectorAt_steps == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.vector_lane_ready_of_encoded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.vector_lanes_ready_of_encoded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.vector_codec_readback_of_encoded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.checked_vector_codec_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.checked_immediate_vector_shape == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.vector_leaf_admission_of_encoded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.vector_child_readback_of_encoded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.VectorReadbackControls.all_fixed_lanes_classified == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VectorReadbackControls.boolean_mask_image == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VectorReadbackControls.vector_and_scalar_boolean_images_differ == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VectorReadbackControls.signed_lane_residue == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.VectorReadbackControls.signed_lane_readback == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VectorReadbackControls.u16_little_endian == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.VectorReadbackControls.u64_full_width == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VectorReadbackControls.unchecked_lane_wraps == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VectorReadbackControls.source_rejects_unbounded_lane == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VectorReadbackControls.wrong_lane_width_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VectorReadbackControls.boolean_integer_carrier_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VectorReadbackControls.zero_count_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VectorReadbackControls.wrong_lane_count_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.VectorReadbackControls.trailing_bytes_refused == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.VectorReadbackControls.truncated_bytes_refused == [propext, Quot.sound] modern [propext, Classical.choice]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.VectorReadbackControls.pointer_lane_refused == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.VectorReadbackControls.target_sized_lane_refused == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.VectorReadbackControls.wide_lane_refused == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.VectorReadbackControls.float_lane_refused == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.VectorReadbackControls.nested_lane_refused == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VectorReadbackControls.wrong_width_certificate_impossible == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VectorReadbackControls.zero_count_certificate_impossible == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VectorReadbackControls.wrong_extent_certificate_impossible == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VectorReadbackControls.checked_boolean_vector_reloads == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VectorReadbackControls.nested_policy_computed == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VectorReadbackControls.prepared_nested_vectors_readback == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.VectorReadbackControls.complete_receiving_window_readback == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.vectorReadbackLane == [] modern [propext]

#trustIrAxiomsPinned TrustIr.VectorLaneReady == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsByCompiler TrustIr.vectorLaneResult == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ValueReadback.vector == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarReadbackInput.vector == [propext, Classical.choice, Quot.sound] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ScalarReadbackPlan.vector == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.vector_lane_value_readback == [propext, Classical.choice, Quot.sound] modern [propext]

-- Ordinary-image metadata, including the actual unwritten-store boundary.

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsEncoded.unwritten_preserved == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_leaf_unwritten_empty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_array_unwritten_empty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_ordinary_unwritten_empty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_uninit_exact == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_ordinary_recordUnwritten == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.OrdinaryImageMetadataControls.padding_is_not_an_unwritten_lane == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.OrdinaryImageMetadataControls.nested_ordinary_metadata_empty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.OrdinaryImageMetadataControls.unwritten_permission_is_observable == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.OrdinaryImageMetadataControls.ordinary_whole_unwritten_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.OrdinaryImageMetadataControls.ordinary_nested_unwritten_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.OrdinaryImageMetadataControls.allowed_nested_unwritten_retains_offset == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.OrdinaryImageMetadataControls.empty_array_unused_template_has_no_records == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.OrdinaryImageMetadataControls.visible_array_unwritten_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.OrdinaryImageMetadataControls.enum_payload_metadata_empty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.OrdinaryImageMetadataControls.enum_payload_does_not_inherit_permission == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.OrdinaryImageMetadataControls.zero_sized_whole_record_is_retained_by_encoder == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.OrdinaryImageMetadataControls.zero_sized_record_is_omitted_by_memory == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.OrdinaryImageMetadataControls.ordinary_recording_preserves_existing_memory == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.OrdinaryImageMetadataControls.copying_padding_does_not_record_unwritten == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- Unwritten image and actual destination registration bounds.

#trustIrAxiomsPinned TrustIr.AggregateMemory.Image.UnwrittenBounded == [] modern []

#trustIrAxiomsPinned TrustIr.AggregateMemory.Image.unwritten_bounded_of_empty == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.FieldsEncoded.unwritten_bounded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_unwritten_bounded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_unwritten_plan_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.Image.recordUnwritten_bounds == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_registered_unwritten_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.UnwrittenImageBoundsControls.nested_offsets_are_added == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.UnwrittenImageBoundsControls.actual_nested_encoding_is_bounded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.UnwrittenImageBoundsControls.declared_extent_supplies_the_bound == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.UnwrittenImageBoundsControls.registration_moves_into_destination_window == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.UnwrittenImageBoundsControls.registration_retains_allocation_identity == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.UnwrittenImageBoundsControls.actual_encoding_supplies_registration_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.UnwrittenImageBoundsControls.fabricated_outside_record_is_not_bounded == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.UnwrittenImageBoundsControls.child_outside_parent_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.UnwrittenImageBoundsControls.zero_sized_child_outside_parent_also_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.UnwrittenImageBoundsControls.whole_array_unwritten_has_bounded_record == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.UnwrittenImageBoundsControls.zero_sized_record_at_endpoint_is_bounded == [propext] modern [propext]

#trustIrAxiomsByCompiler TrustIr.AggregateMemory.UnwrittenImageBoundsControls.zero_sized_registration_adds_no_record == [] modern [propext]

#trustIrAxiomsPinned TrustIr.AggregateMemory.UnwrittenImageBoundsControls.unrelated_old_records_are_preserved == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.UnwrittenImageBoundsControls.bounded_record_does_not_imply_absent_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- Exact unwritten coverage through clipping and authoritative byte writes.

#trustIrAxiomsPinned TrustIr.Memory.forgetUnwritten_coverage == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.Memory.writeImage_unwritten_coverage == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.Memory.writeImage_unwritten_inside == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.Memory.writeImage_unwritten_outside == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.Memory.writeImage_no_new_unwritten == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.Memory.writeBytesMaybeUninit_unwritten_coverage == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.Memory.writeBytes_unwritten_coverage == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.encode_ordinary_publication_coverage == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.UnwrittenOverwriteControls.absent_copy_clears_old_lane == [] modern []

#trustIrAxiomsPinned TrustIr.UnwrittenOverwriteControls.middle_write_preserves_both_sides == [] modern []

#trustIrAxiomsPinned TrustIr.UnwrittenOverwriteControls.half_open_endpoints_are_exact == [] modern []

#trustIrAxiomsPinned TrustIr.UnwrittenOverwriteControls.complete_overwrite_clears_every_covered_address == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.UnwrittenOverwriteControls.zero_length_write_preserves_lane == [] modern []

#trustIrAxiomsPinned TrustIr.UnwrittenOverwriteControls.adjacent_write_does_not_clip == [] modern []

#trustIrAxiomsPinned TrustIr.UnwrittenOverwriteControls.write_cannot_create_an_unwritten_claim == [] modern []

#trustIrAxiomsPinned TrustIr.UnwrittenOverwriteControls.distinct_allocation_does_not_gain_coverage == [] modern []

#trustIrAxiomsPinned TrustIr.UnwrittenOverwriteControls.duplicate_overlapping_records_are_all_clipped == [] modern []

#trustIrAxiomsPinned TrustIr.UnwrittenOverwriteControls.list_transport_has_same_clipping == [] modern []

#trustIrAxiomsPinned TrustIr.UnwrittenOverwriteControls.initialized_list_write_has_same_clipping == [] modern []

#trustIrAxiomsPinned TrustIr.UnwrittenOverwriteControls.malformed_old_record_cannot_create_coverage == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.UnwrittenOverwriteControls.actual_ordinary_publication_clears_old_record == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.UnwrittenOverwriteControls.source_publication_law_uses_actual_extent == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- Actual aggregate Store execution, transport branches, live extents and metadata.

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreImageAccepted == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.storeValue_success_steps == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreImageAccepted.unwritten_bounded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreImageAccepted.unwritten_empty == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.storeValue_success_live_allocation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.storeValue_success_unwritten_coverage == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.storeValue_success_registered_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.actual_scalar_store_executes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.actual_scalar_store_writes_byte == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.actual_scalar_store_clears_exact_window == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.scalar_store_retains_private_state == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.partial_transport_is_not_ordinary_encoding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.typed_poison_transport_has_no_new_records == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.wrong_poison_type_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.strict_poison_refuses_before_target_and_pointer == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.source_target_mismatch_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.alignment_refusal_precedes_pointer == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.null_pointer_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.dead_allocation_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.access_refusal_precedes_bad_carrier == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.target32_refusal_precedes_allocation == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.partial_image_extent_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.actual_unwritten_tuple_publication == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.strict_nested_unwritten_refuses == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.whole_unwritten_store_registers_a_new_lane == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.actual_scalar_store_then_load == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.actual_unwritten_tuple_store_then_load == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreExecutionControls.absent_transport_does_not_authorize_strict_load == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

-- Original SSA Store operands, actual context dispatch and descriptor execution.

#trustIrAxiomsPinned TrustIr.selectedStoreAction == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.selectedStoreAction_default_align == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepStore_lookup_action == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepStore_success_operands == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.aggregateStore_success_operands == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepStore_descriptor_execution == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepStore_canonical_execution == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.memoryServiceFor_descriptor_iff == [propext] modern [propext]

#trustIrAxiomsPinned TrustIr.stepStore_descriptor_success_steps == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepStore_descriptor_unwritten_coverage == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepStore_descriptor_registered_bounds == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreInstructionControls.descriptor_selector_uses_actual_service == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreInstructionControls.canonical_selector_keeps_scalar_path == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreInstructionControls.actual_store_node_executes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreInstructionControls.store_node_does_not_publish_ssa_temporaries == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreInstructionControls.store_node_publishes_selected_unwritten_image == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreInstructionControls.missing_pointer_lookup_precedes_other_refusals == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreInstructionControls.missing_value_lookup_is_not_a_missing_pointer == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreInstructionControls.canonical_store_ignores_wrong_target_descriptor == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreInstructionControls.descriptor_store_keeps_target_refusal == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreInstructionControls.missing_descriptor_has_no_fabricated_layout == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreInstructionControls.instruction_alignment_is_forwarded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreInstructionControls.descriptor_strict_poison_precedes_pointer_check == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreInstructionControls.canonical_pointer_check_precedes_strict_poison == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreInstructionControls.identical_operand_ids_are_read_from_original_state == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreInstructionControls.descriptor_store_then_load_publishes_only_the_load == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreInstructionControls.canonical_store_then_load_publishes_only_the_load == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.scalarLoadValue_readOnly == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.aggregateLoadValue_readOnly == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.selectedLoadAction_readOnly == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.selectedLoadAction_default_align == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepLoad_lookup_action == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepLoad_success_publication == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepLoad_success_iff == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepLoad_memory_unchanged == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepLoad_published_value == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepLoad_descriptor_execution == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepLoad_canonical_execution == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LoadInstructionControls.descriptor_load_publishes_actual_value_once == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LoadInstructionControls.scalar_load_keeps_canonical_path == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LoadInstructionControls.scalar_partial_load_publishes_poison == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LoadInstructionControls.scalar_strict_load_refuses_uninitialized == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LoadInstructionControls.descriptor_unexplained_hole_is_not_padding == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LoadInstructionControls.descriptor_unwritten_load_uses_original_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LoadInstructionControls.strict_descriptor_preserves_explicit_unwritten_policy == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LoadInstructionControls.unwritten_read_does_not_consume_metadata == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LoadInstructionControls.missing_operand_precedes_target_refusal == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LoadInstructionControls.descriptor_target_precedes_null_pointer == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LoadInstructionControls.scalar_null_pointer_precedes_bad_alignment == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LoadInstructionControls.descriptor_alignment_is_forwarded == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LoadInstructionControls.missing_service_does_not_fabricate_layout == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.LoadInstructionControls.colliding_next_id_still_looks_up_before_publication == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.loadValue_image_action == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.loadValue_success_steps == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.loadImageResult_success_cases == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.loadValue_success_image == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.loadImageAccepted_result == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.loadImageResult_success_iff == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepLoad_descriptor_image == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateLoadExecutionControls.plan_is_actual_source_query == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateLoadExecutionControls.complete_image_selects_ordinary_decode == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateLoadExecutionControls.missing_padding_is_not_partial_poison == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateLoadExecutionControls.padding_path_checks_only_covered_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateLoadExecutionControls.explained_fields_decode_original_unwritten_value == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateLoadExecutionControls.temporary_zeros_do_not_replace_original_image == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateLoadExecutionControls.temporary_zeros_are_not_a_loaded_zero_value == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateLoadExecutionControls.wrong_allocation_cannot_explain_a_hole == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateLoadExecutionControls.padding_record_cannot_explain_a_field == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateLoadExecutionControls.adjacent_record_does_not_cover_the_load == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateLoadExecutionControls.partial_scalar_transport_is_a_distinct_branch == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateLoadExecutionControls.strict_scalar_does_not_take_partial_transport == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateLoadExecutionControls.original_node_reads_padded_image == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateLoadExecutionControls.original_node_reads_unwritten_image == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.scalarLoadValue_success_steps == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.scalarLoadValue_of_checks == [Quot.sound, propext] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.scalarLoadValue_success_iff == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepLoad_scalar_image == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ScalarLoadExecutionControls.target32_reads_exactly_four_usize_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ScalarLoadExecutionControls.target64_reads_all_eight_usize_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ScalarLoadExecutionControls.target32_ignores_unread_high_half == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ScalarLoadExecutionControls.target64_transports_the_actual_partial_image == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ScalarLoadExecutionControls.pointer_decode_recovers_original_memory_provenance == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ScalarLoadExecutionControls.function_decode_uses_source_order == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ScalarLoadExecutionControls.changed_function_order_changes_actual_loaded_identity == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ScalarLoadExecutionControls.initialized_function_without_table_is_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ScalarLoadExecutionControls.null_function_does_not_require_a_table == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ScalarLoadExecutionControls.initialized_invalid_char_is_refused == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ScalarLoadExecutionControls.partial_char_keeps_the_partial_transport_path == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsByCompiler TrustIr.ScalarLoadExecutionControls.initialized_bytes_retain_the_actual_decoder_refusal == [] modern [propext]

#trustIrAxiomsByCompiler TrustIr.ScalarLoadExecutionControls.partial_transport_does_not_assume_decoder_success == [] modern [propext]

#trustIrAxiomsPinned TrustIr.Memory.recordUnwritten_bytes == [] modern []

#trustIrAxiomsPinned TrustIr.Memory.readImage_after_write_record == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.ReadbackInput.not_poison == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.StoreImageAccepted.ordinary_encode == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.storeValue_success_image_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.AggregateMemory.prepared_store_snapshot_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepStore_descriptor_image_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.stepStore_prepared_snapshot_readback == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreImageReadbackControls.actual_store_has_admitted_snapshot == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreImageReadbackControls.snapshot_contains_normalized_integer_not_raw_carrier == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreImageReadbackControls.raw_carrier_identity_is_not_the_readback_relation == [propext, Quot.sound, Classical.choice] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreImageReadbackControls.absent_padding_overwrites_stale_initialized_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreImageReadbackControls.ordinary_store_does_not_retain_stale_unwritten_coverage == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreImageReadbackControls.outside_snapshot_is_absent_even_when_following_memory_is_initialized == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreImageReadbackControls.original_store_then_load_reads_the_normalized_value == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreImageReadbackControls.partial_store_also_replaces_stale_bytes == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreImageReadbackControls.partial_transport_has_no_typed_readback_admission == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.StoreImageReadbackControls.empty_snapshot_has_no_outside_byte == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

-- Logical block-check completeness and actual callback controls.

#trustIrAxiomsPinned TrustIr.ByteImage.CheckedBlocks.congr == [] modern []

#trustIrAxiomsPinned TrustIr.ByteImage.CheckedBlocks.subrange == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.checkBlocksSpec_none_of_checked_of_periods == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.checkBlocks_none_of_checked == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.checkBlocks_subrange_none == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.BlockCheckCompletenessControls.logical_custody_drives_actual_check == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.BlockCheckCompletenessControls.bounded_subrange_keeps_callback_authority == [propext, Classical.choice, Quot.sound] modern [propext, Classical.choice, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.BlockCheckCompletenessControls.zero_count_does_not_call_a_refusing_callback == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.BlockCheckCompletenessControls.positive_count_zero_width_retains_callback_refusal == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.BlockCheckCompletenessControls.coprime_periodic_phases_are_checked == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.BlockCheckCompletenessControls.late_hole_in_period_is_not_hidden_by_initialized_prefix == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.BlockCheckCompletenessControls.later_error_keeps_precedence_over_earlier_hole == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.BlockCheckCompletenessControls.invisible_retained_hole_is_not_a_visible_block == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

#trustIrAxiomsPinned TrustIr.ByteImage.BlockCheckCompletenessControls.initialized_prefix_is_not_full_block_custody == [propext, Classical.choice, Quot.sound] modern [propext, Quot.sound]

-- Lean 4.30 changes compiler-generated proof/matcher names. Every absent
-- canonical name above remains checked on Lean 4.8. These closed rosters and
-- exact member footprints account for all actual modern replacements; additions,
-- removals, and new axiom dependencies fail rather than silently being skipped.

trustIrModernOnly
#trustIrModernAxiomFamily TrustIr.GenericCoro.AllBlocks.functionsWithDomain == [
  TrustIr.GenericCoro.AllBlocks.functionsWithDomain._proof_1,
  TrustIr.GenericCoro.AllBlocks.functionsWithDomain.eq_1,
  TrustIr.GenericCoro.AllBlocks.functionsWithDomain.match_1]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.functionsWithDomain._proof_1 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.functionsWithDomain.eq_1 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocks.functionsWithDomain.match_1 == [propext, Quot.sound]

trustIrModernOnly
#trustIrModernAxiomFamily TrustIr.GenericCoro.AllBlocksInference.graphNames == [
  TrustIr.GenericCoro.AllBlocksInference.graphNames._proof_1,
  TrustIr.GenericCoro.AllBlocksInference.graphNames._proof_2,
  TrustIr.GenericCoro.AllBlocksInference.graphNames._proof_3,
  TrustIr.GenericCoro.AllBlocksInference.graphNames._proof_4,
  TrustIr.GenericCoro.AllBlocksInference.graphNames._proof_5,
  TrustIr.GenericCoro.AllBlocksInference.graphNames._proof_6,
  TrustIr.GenericCoro.AllBlocksInference.graphNames._proof_7,
  TrustIr.GenericCoro.AllBlocksInference.graphNames._proof_8,
  TrustIr.GenericCoro.AllBlocksInference.graphNames._proof_9]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksInference.graphNames._proof_1 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksInference.graphNames._proof_2 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksInference.graphNames._proof_3 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksInference.graphNames._proof_4 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksInference.graphNames._proof_5 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksInference.graphNames._proof_6 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksInference.graphNames._proof_7 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksInference.graphNames._proof_8 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.AllBlocksInference.graphNames._proof_9 == [propext, Quot.sound]

trustIrModernOnly
#trustIrModernAxiomFamily TrustIr.GenericCoro.RowInference.Controls.names == [
  TrustIr.GenericCoro.RowInference.Controls.names._proof_1,
  TrustIr.GenericCoro.RowInference.Controls.names._proof_2,
  TrustIr.GenericCoro.RowInference.Controls.names._proof_3,
  TrustIr.GenericCoro.RowInference.Controls.names._proof_4,
  TrustIr.GenericCoro.RowInference.Controls.names._proof_5,
  TrustIr.GenericCoro.RowInference.Controls.names._proof_6,
  TrustIr.GenericCoro.RowInference.Controls.names._proof_7,
  TrustIr.GenericCoro.RowInference.Controls.names._proof_8,
  TrustIr.GenericCoro.RowInference.Controls.names._proof_9]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.RowInference.Controls.names._proof_1 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.RowInference.Controls.names._proof_2 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.RowInference.Controls.names._proof_3 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.RowInference.Controls.names._proof_4 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.RowInference.Controls.names._proof_5 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.RowInference.Controls.names._proof_6 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.RowInference.Controls.names._proof_7 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.RowInference.Controls.names._proof_8 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.RowInference.Controls.names._proof_9 == []

trustIrModernOnly
#trustIrModernAxiomFamily TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames == [
  TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames._proof_1,
  TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames._proof_2,
  TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames._proof_3,
  TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames._proof_4,
  TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames._proof_5,
  TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames._proof_6,
  TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames._proof_7,
  TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames._proof_8,
  TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames._proof_9]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames._proof_1 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames._proof_2 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames._proof_3 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames._proof_4 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames._proof_5 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames._proof_6 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames._proof_7 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames._proof_8 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoro.RowInference.FollowUpControls.laterNames._proof_9 == []

trustIrModernOnly
#trustIrModernAxiomFamily TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_run == [
  TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_run.match_1,
  TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_run.match_3]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_run.match_1 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksInvoke.invokeFrameWith_run.match_3 == []

trustIrModernOnly
#trustIrModernAxiomFamily TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop == [
  TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop._f,
  TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop._sunfold,
  TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop._unsafe_rec,
  TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.eq_1,
  TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.eq_2,
  TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.eq_def,
  TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.match_1,
  TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.match_3]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop._f == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop._sunfold == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop._unsafe_rec == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.eq_1 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.eq_2 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.eq_def == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.match_1 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.lowerRowsLoop.match_3 == [propext, Quot.sound]

trustIrModernOnly
#trustIrModernAxiomFamily TrustIr.GenericCoroAllBlocksPlanner.reserveTriple == [
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_1,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_10,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_11,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_12,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_13,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_14,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_15,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_16,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_17,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_18,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_19,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_2,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_20,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_21,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_22,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_23,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_24,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_25,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_26,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_27,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_28,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_29,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_3,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_30,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_31,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_32,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_33,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_34,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_35,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_4,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_5,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_6,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_7,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_8,
  TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_9]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_1 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_10 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_11 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_12 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_13 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_14 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_15 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_16 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_17 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_18 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_19 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_2 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_20 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_21 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_22 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_23 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_24 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_25 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_26 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_27 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_28 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_29 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_3 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_30 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_31 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_32 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_33 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_34 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_35 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_4 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_5 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_6 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_7 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_8 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroAllBlocksPlanner.reserveTriple._proof_9 == [propext, Classical.choice, Quot.sound]

trustIrModernOnly
#trustIrModernAxiomFamily TrustIr.GenericCoroFreshCursor.prepare == [
  TrustIr.GenericCoroFreshCursor.prepare._proof_1,
  TrustIr.GenericCoroFreshCursor.prepare._proof_2,
  TrustIr.GenericCoroFreshCursor.prepare._proof_3,
  TrustIr.GenericCoroFreshCursor.prepare._proof_4,
  TrustIr.GenericCoroFreshCursor.prepare._proof_5,
  TrustIr.GenericCoroFreshCursor.prepare.eq_1]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.prepare._proof_1 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.prepare._proof_2 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.prepare._proof_3 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.prepare._proof_4 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.prepare._proof_5 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.prepare.eq_1 == [propext, Classical.choice, Quot.sound]

trustIrModernOnly
#trustIrModernAxiomFamily TrustIr.GenericCoroFreshCursor.reserve == [
  TrustIr.GenericCoroFreshCursor.reserve._proof_1,
  TrustIr.GenericCoroFreshCursor.reserve._proof_10,
  TrustIr.GenericCoroFreshCursor.reserve._proof_11,
  TrustIr.GenericCoroFreshCursor.reserve._proof_12,
  TrustIr.GenericCoroFreshCursor.reserve._proof_13,
  TrustIr.GenericCoroFreshCursor.reserve._proof_14,
  TrustIr.GenericCoroFreshCursor.reserve._proof_15,
  TrustIr.GenericCoroFreshCursor.reserve._proof_16,
  TrustIr.GenericCoroFreshCursor.reserve._proof_17,
  TrustIr.GenericCoroFreshCursor.reserve._proof_18,
  TrustIr.GenericCoroFreshCursor.reserve._proof_19,
  TrustIr.GenericCoroFreshCursor.reserve._proof_2,
  TrustIr.GenericCoroFreshCursor.reserve._proof_20,
  TrustIr.GenericCoroFreshCursor.reserve._proof_21,
  TrustIr.GenericCoroFreshCursor.reserve._proof_22,
  TrustIr.GenericCoroFreshCursor.reserve._proof_23,
  TrustIr.GenericCoroFreshCursor.reserve._proof_24,
  TrustIr.GenericCoroFreshCursor.reserve._proof_25,
  TrustIr.GenericCoroFreshCursor.reserve._proof_26,
  TrustIr.GenericCoroFreshCursor.reserve._proof_27,
  TrustIr.GenericCoroFreshCursor.reserve._proof_28,
  TrustIr.GenericCoroFreshCursor.reserve._proof_29,
  TrustIr.GenericCoroFreshCursor.reserve._proof_3,
  TrustIr.GenericCoroFreshCursor.reserve._proof_30,
  TrustIr.GenericCoroFreshCursor.reserve._proof_31,
  TrustIr.GenericCoroFreshCursor.reserve._proof_32,
  TrustIr.GenericCoroFreshCursor.reserve._proof_33,
  TrustIr.GenericCoroFreshCursor.reserve._proof_34,
  TrustIr.GenericCoroFreshCursor.reserve._proof_35,
  TrustIr.GenericCoroFreshCursor.reserve._proof_36,
  TrustIr.GenericCoroFreshCursor.reserve._proof_37,
  TrustIr.GenericCoroFreshCursor.reserve._proof_38,
  TrustIr.GenericCoroFreshCursor.reserve._proof_39,
  TrustIr.GenericCoroFreshCursor.reserve._proof_4,
  TrustIr.GenericCoroFreshCursor.reserve._proof_40,
  TrustIr.GenericCoroFreshCursor.reserve._proof_41,
  TrustIr.GenericCoroFreshCursor.reserve._proof_42,
  TrustIr.GenericCoroFreshCursor.reserve._proof_43,
  TrustIr.GenericCoroFreshCursor.reserve._proof_44,
  TrustIr.GenericCoroFreshCursor.reserve._proof_5,
  TrustIr.GenericCoroFreshCursor.reserve._proof_6,
  TrustIr.GenericCoroFreshCursor.reserve._proof_7,
  TrustIr.GenericCoroFreshCursor.reserve._proof_8,
  TrustIr.GenericCoroFreshCursor.reserve._proof_9]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_1 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_10 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_11 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_12 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_13 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_14 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_15 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_16 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_17 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_18 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_19 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_2 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_20 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_21 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_22 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_23 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_24 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_25 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_26 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_27 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_28 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_29 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_3 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_30 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_31 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_32 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_33 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_34 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_35 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_36 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_37 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_38 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_39 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_4 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_40 == []
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_41 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_42 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_43 == [propext, Classical.choice, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_44 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_5 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_6 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_7 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_8 == [propext, Quot.sound]
trustIrModernOnly
#trustIrAxiomsExact TrustIr.GenericCoroFreshCursor.reserve._proof_9 == [propext, Quot.sound]
