-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Pure formal root: no executable fixtures or runtime implementation imports.
-- Re-exports all sub-modules.
--
-- This is the formal semantics of TrustIr — the Trusted Mid-level
-- Intermediate Representation for the t* verified compilation stack.
--
-- Reference: designs/2026-04-16-trust_ir-semantics-lean-architecture.md
-- Reference: Ho & Protzenko, "Aeneas: Rust verification by functional
--            translation", ICFP 2022.

import TrustIr.Basic
import TrustIr.BinOp
import TrustIr.CmpOp
import TrustIr.CastOp
import TrustIr.Ordering
import TrustIr.Constant
import TrustIr.Inst
import TrustIr.State.MachineState
import TrustIr.State.ValueMap
import TrustIr.State.Memory
import TrustIr.State.Permission
import TrustIr.Pred
import TrustIr.Semantics.Monad
import TrustIr.Semantics.FloatFormat
import TrustIr.Semantics.Arith
import TrustIr.Semantics.Compare
import TrustIr.Semantics.Cast
import TrustIr.Semantics.Control
import TrustIr.Semantics.Memory
import TrustIr.Semantics.TargetMemory
import TrustIr.Semantics.Borrow
import TrustIr.Semantics.ARC
import TrustIr.Semantics.Call
import TrustIr.Semantics.Atomic
import TrustIr.Semantics.Aggregate
import TrustIr.Semantics.Frame
import TrustIr.Semantics.VectorSelectPlan
import TrustIr.Semantics.Step
import TrustIr.Semantics.Eval
import TrustIr.Semantics.Dialect
import TrustIr.Semantics.VectorDialect
import TrustIr.Template
import TrustIr.Proofs.ArithProps
import TrustIr.Proofs.FloatChoiceProps
import TrustIr.Proofs.FloatChoiceRefinement
import TrustIr.Proofs.ByteImageTraversalProps
import TrustIr.Proofs.MemoryProps
import TrustIr.Proofs.TargetMemoryProps
import TrustIr.Proofs.TargetStepProps
import TrustIr.Proofs.DeclarationProjectionProps
import TrustIr.Proofs.BorrowProps
import TrustIr.Proofs.BorrowMemoryProps
import TrustIr.Proofs.ARCProps
import TrustIr.Proofs.CallProps
import TrustIr.Proofs.ClosureProps
import TrustIr.Proofs.CoroutineProps
import TrustIr.Proofs.AtomicProps
import TrustIr.Proofs.MetaTheorems
import TrustIr.Proofs.UninhabitedDirectProps
import TrustIr.Proofs.SingleInhabitedCodecProps
import TrustIr.Proofs.FunctionItemProps
import TrustIr.Proofs.BindingFrameSourceProps
import TrustIr.Proofs.MemorySafety
import TrustIr.Proofs.ContextualAllocationChecks
import TrustIr.Proofs.ClosureAllocationChecks
import TrustIr.Proofs.DecodedClosureStorageChecks
import TrustIr.Proofs.OriginalClosureMemoryReadback
import TrustIr.Proofs.OriginalClosureMemoryReadbackChecks
import TrustIr.Proofs.BorrowedClosureCalls
import TrustIr.Proofs.BorrowedClosureCallChecks
import TrustIr.Proofs.OriginalClosureMemoryChecks
import TrustIr.Proofs.HeldMemoryFrames
import TrustIr.Proofs.SSAFreshFrames
import TrustIr.Proofs.TransformCorrectness
import TrustIr.Proofs.TransformRefinementCtx
import TrustIr.Proofs.AYBridge
import TrustIr.Proofs.AYSMTLib
import TrustIr.Proofs.AYValueProps
import TrustIr.Proofs.AYModelProps
import TrustIr.Proofs.AYBitVecProps
import TrustIr.Proofs.AYBitVecArithmetic
import TrustIr.Proofs.AYBitVecBitwise
import TrustIr.Proofs.AYBitVecUnsignedDiv
import TrustIr.Proofs.AYBitVecSignedDiv
import TrustIr.Proofs.AYBitVecShifts
import TrustIr.Proofs.AYBitVecRotations
import TrustIr.Proofs.AYCoreValue
import TrustIr.Proofs.AYTargetCorrect
import TrustIr.Proofs.AYTargetInstruction
import TrustIr.Proofs.AYClosedCheck
import TrustIr.Proofs.AYGateCNF
import TrustIr.Proofs.AYAdderCNF
import TrustIr.Proofs.AYFreshGates
import TrustIr.Proofs.AYBooleanCompile
import TrustIr.Proofs.AYWordWires
import TrustIr.Proofs.AYWordAdd
import TrustIr.Proofs.AYWordSub
import TrustIr.Proofs.AYWordMul
import TrustIr.Proofs.AYSubCarry
import TrustIr.Proofs.AYRestoringStep
import TrustIr.Proofs.AYDivisionInvariant
import TrustIr.Proofs.AYDivisionLoop
import TrustIr.Proofs.AYUnsignedDivision
import TrustIr.Proofs.AYDivisionTarget
import TrustIr.Proofs.AYDivisionInstruction
import TrustIr.Proofs.AYSignedDivision
import TrustIr.Proofs.AYSignedDivisionInstruction
import TrustIr.Proofs.AYDivisionReplay
import TrustIr.Proofs.AYWordCompare
import TrustIr.Proofs.AYWordIte
import TrustIr.Proofs.AYWordShift
import TrustIr.Proofs.AYVariableShift
import TrustIr.Proofs.AYArithmeticShift
import TrustIr.Proofs.AYWordWidths
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
import TrustIr.Proofs.AYWidthTarget
import TrustIr.Proofs.AYTypedRequest
import TrustIr.Proofs.AYSourceInput
import TrustIr.Proofs.AYCastTarget
import TrustIr.Proofs.AYCastReplay
import TrustIr.Proofs.AYTypedBindingControls
import TrustIr.Proofs.AYSymbolProps
import TrustIr.Proofs.AggregateProps
import TrustIr.Proofs.BindingFrameProps
import TrustIr.Proofs.FrameLifetimeProps
import TrustIr.Proofs.FrameValueValidity
import TrustIr.Proofs.FrameContextualValidity
import TrustIr.Proofs.FrameContextualControls
import TrustIr.Proofs.FrameDecodeFreedom
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
import TrustIr.Proofs.VectorDialectProps
import TrustIr.Proofs.PredLatticeProps
import TrustIr.Proofs.DropProps
import TrustIr.Proofs.UnwindProps
import TrustIr.Proofs.TemplateProps
import TrustIr.Proofs.IntResidue
import TrustIr.Proofs.PointerObservationProps
import TrustIr.Proofs.CleanUInt32Ownership
import TrustIr.Proofs.AxiomAudit

import TrustIr.Proofs.GenericCoroControls

import TrustIr.Proofs.GenericCoroModuleAxiomAudit

import TrustIr.Proofs.DecodedFunctionLookupAxiomAudit

import TrustIr.Proofs.DecodedCFGAxiomAudit

import TrustIr.Proofs.FrameCheckedCalls
import TrustIr.Proofs.FrameIndirectArguments
import TrustIr.Proofs.FrameIndirectCalls
import TrustIr.Proofs.FrameTailBoundary
import TrustIr.Proofs.FrameTailRecursion
import TrustIr.Proofs.FrameIndirectTerminal
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

import TrustIr.Proofs.FrameExceptionalExits

import TrustIr.Proofs.FrameAssertInvokeExits

import TrustIr.Proofs.FrameUnwindRecursion

import TrustIr.Proofs.FrameTerminalExits

import TrustIr.Proofs.FrameTerminalRecursion

import TrustIr.Proofs.FrameMemoryDecodeExits

import TrustIr.Proofs.FrameMemoryLoads

import TrustIr.Proofs.FrameBlockDecoding

import TrustIr.Proofs.FrameAggregateDecoding
import TrustIr.Proofs.FrameAggregateLoads
import TrustIr.Proofs.FrameMemoryEncoding
import TrustIr.Proofs.FrameAggregateStores
import TrustIr.Proofs.FrameAtomicScalarExits
import TrustIr.Proofs.FrameAtomicExits
import TrustIr.Proofs.FrameAllocationExits
import TrustIr.Proofs.FrameGEPExits

import TrustIr.Proofs.FrameWorldUpdates
import TrustIr.Proofs.FrameBulkMemoryExits
import TrustIr.Proofs.FrameOwnershipExits

import TrustIr.Proofs.FrameMemoryRecursion

import TrustIr.Proofs.FrameSeqMapExits
import TrustIr.Proofs.FrameSequenceRecursion

import TrustIr.Proofs.ConstantContextEquations
import TrustIr.Proofs.FrameConstantExits

import TrustIr.Proofs.FrameGlobalExits

import TrustIr.Proofs.ConstantFrameValues
import TrustIr.Proofs.FrameConstantPublication

import TrustIr.Proofs.FrameCoroExits
import TrustIr.Proofs.FrameStaticExits
import TrustIr.Proofs.FrameInstructionAdmission

import TrustIr.Proofs.DecodedFrameEntry

import TrustIr.Proofs.TargetWidthDefinition

import TrustIr.Proofs.SourceLayoutBounds

import TrustIr.Proofs.SourceLayoutDerivation

import TrustIr.Proofs.SourceLayoutSession
import TrustIr.Proofs.SourceLayoutEquationBounds
import TrustIr.Proofs.SourceLayoutCombinators
import TrustIr.Semantics.CompactArrayFixtures

import TrustIr.Proofs.ImageMapStepAudit

import TrustIr.Proofs.ImageMapCacheAudit

import TrustIr.Proofs.UnsignedDivisionWpControls
import TrustIr.Proofs.UnsignedRemainderWp
