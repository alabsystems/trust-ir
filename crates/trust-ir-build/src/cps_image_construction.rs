// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Untrusted construction custody. The independently frozen source claim,
//! every original definition and complete image proof MUST still replay.
use super::*;
pub struct StructuredRunConstruction {
    // SAME actual input binder used to lambda-close ImageCandidate.run.
    pub input: ScopedLocal,
    pub root: Box<StructuredObservationConstruction>,
}
pub struct StructuredObservationConstruction {
    // Actual full first-order term, never an assumed semantic replacement.
    pub observation: Expr,
    pub step: StructuredObservationStep,
}
pub struct StructuredContinuationConstruction {
    // Actual fresh payload/poststate binder order from both-continuation image.
    pub payload: ScopedLocal,
    pub poststate: ScopedLocal,
    pub body: Box<StructuredObservationConstruction>,
}
pub enum StructuredObservationStep {
    Return {
        normal: bool,
        state: Expr,
        payload: Expr,
    },
    Case {
        head: Expr,
        parameters: Vec<Expr>,
        major: Expr,
        branches: Vec<(Vec<ScopedLocal>, StructuredObservationConstruction)>,
    },
    Handle {
        operator: Box<ScopedLocal>,
        original_arguments: Vec<Expr>,
        actual_run: Expr,
        actual_state: Expr,
        yes: Box<StructuredContinuationConstruction>,
        no: Box<StructuredContinuationConstruction>,
    },
}
// All trace fields are UNTRUSTED producer data. Consumers must retain complete
// source definitions, source-call equation and actual image proof; match exact
// owner/types/ABI/Run/state through the strict checker; preserve both outcomes,
// all captures/branches and original frozen endpoint. Trace labels or presence
// are never source membership, Frame, provider or physical loop authority.
// Trace allocation/probes/clones must prepay same component work ledger.

impl std::fmt::Debug for StructuredRunConstruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StructuredRunConstruction")
            .field("input", &self.input.id())
            .field("root", &self.root)
            .finish()
    }
}
impl std::fmt::Debug for StructuredObservationConstruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let kind = match &self.step {
            StructuredObservationStep::Return { .. } => "return",
            StructuredObservationStep::Case { .. } => "case",
            StructuredObservationStep::Handle { .. } => "handle",
        };
        f.debug_struct("StructuredObservationConstruction")
            .field("step", &kind)
            .finish_non_exhaustive()
    }
}
