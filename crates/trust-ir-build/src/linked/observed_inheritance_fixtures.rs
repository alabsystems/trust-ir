// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! cfg(test)-only recorder inputs, never a production authentication constructor.
use super::*;
impl AuthenticatedImports {
    pub(crate) fn inherited_fixture_for_observed_tests(
        rows: Vec<(ProofCertificate, SiteOutcome)>,
    ) -> Self {
        let mut output = Self::default();
        for (certificate, outcome) in rows {
            output.record_inherited(&certificate, outcome);
        }
        output
    }
}
