// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete scoped proof components with exact mixed telescopes.
//!
//! The producer retains every value and closes internal binders with one
//! aggregate traversal. Replay checks each declaration in its actual preceding
//! context, matches the frozen full claim, then checks the root and dependencies.
//! The artifact and its measurements are untrusted until replay succeeds.

#[path = "proof_components_dependencies.rs"]
mod dependencies;
#[path = "proof_components_plan.rs"]
mod plan;
#[path = "proof_components_scoped.rs"]
mod scoped;
#[path = "proof_components_wire.rs"]
mod wire;

pub(crate) use plan::{ConstructedObservation, ExternalContext, ObservationReferences};

pub use plan::{
    InstantiatedScopedCandidate, OwnedDefinitionAlias, OwnedProofCapture, OwnedScopedDefinition,
    ProofComponents, SealedScopedDefinition,
};
pub use scoped::{
    ReplayedProofComponents, ScopedBuildWork, ScopedProofComponentBundle, ScopedProofDeclaration,
};

#[cfg(test)]
#[path = "proof_components_tests.rs"]
mod tests;
