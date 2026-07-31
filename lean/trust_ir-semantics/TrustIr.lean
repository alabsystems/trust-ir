-- Copyright 2026 Andrew Yates
-- Author: Andrew Yates <andrewyates.name@gmail.com>
-- Licensed under the Apache License, Version 2.0
--
-- Root module for TrustIr Lean 4 formalization.
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
import TrustIr.Semantics.Arith
import TrustIr.Semantics.Compare
import TrustIr.Semantics.Cast
import TrustIr.Semantics.Control
import TrustIr.Semantics.Memory
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
import TrustIr.Semantics.ExecutableFixtures
import TrustIr.Proofs.ArithProps
import TrustIr.Proofs.MemoryProps
import TrustIr.Proofs.BorrowProps
import TrustIr.Proofs.ARCProps
import TrustIr.Proofs.CallProps
import TrustIr.Proofs.AtomicProps
import TrustIr.Proofs.MetaTheorems
import TrustIr.Proofs.MemorySafety
import TrustIr.Proofs.TransformCorrectness
import TrustIr.Proofs.AYBridge
import TrustIr.Proofs.AggregateProps
import TrustIr.Proofs.BindingFrameProps
import TrustIr.Proofs.VectorDialectProps
import TrustIr.Proofs.PredLatticeProps
import TrustIr.Proofs.AxiomAudit
