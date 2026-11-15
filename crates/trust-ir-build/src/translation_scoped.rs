// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Endpoint-bound replay of complete scoped proof components.

use super::{
    KernelCheckedTranslationTerm, SourceTranslationModel, TranslationProofEncoding,
    TranslationRecheckError, TranslationRechecker,
};
use crate::proof_components::ScopedProofComponentBundle;
use trust_ir::Module;

impl<M: SourceTranslationModel> TranslationRechecker<M> {
    /// Replay the explicit scoped-component v1 carrier against both endpoints.
    ///
    /// Decode the entire bounded bundle before reconstructing the model's claim.
    /// The transported claim must match that reconstruction; it never supplies
    /// either endpoint's meaning. Every scoped definition and the complete root
    /// then undergo strict kernel replay with this checker's finite aggregate
    /// heartbeat limit and the scoped auditor's unchanged closing limits.
    ///
    /// No root containing free scoped locals is exposed as a closed proof term.
    /// The returned receipt instead borrows the actual model, endpoints and
    /// original bytes, exactly as the other explicit translation carriers do.
    /// This establishes only the selected model's proposition, not executable
    /// admission or fidelity of its source/runtime semantics.
    pub fn recheck_scoped_components_v1<'a>(
        &'a self,
        source: &'a M::Source,
        target: &'a Module,
        proof_term: &'a [u8],
    ) -> Result<KernelCheckedTranslationTerm<'a, M>, TranslationRecheckError> {
        let (bundle, transported_claim) = ScopedProofComponentBundle::decode_with_claim(proof_term)
            .map_err(|reason| TranslationRecheckError::new("decode", reason))?;
        let claim = M::reconstruct(source, target)
            .map_err(|reason| TranslationRecheckError::new("reconstruct", reason))?;
        if transported_claim != claim {
            return Err(TranslationRecheckError::new(
                "reconstruct",
                "scoped transport claim differs from the actual endpoint claim",
            ));
        }
        // ReplayedProofComponents is an environment-bound audit observation,
        // not an endpoint-bound receipt. Never return it as translation authority.
        bundle
            .replay(&self.environment, &claim, self.scoped_kernel_limit)
            .map_err(|reason| TranslationRecheckError::new("kernel audit", reason))?;
        Ok(KernelCheckedTranslationTerm {
            checker: self,
            source,
            target,
            proof_term,
            encoding: TranslationProofEncoding::ScopedComponentsV1,
        })
    }
}
