// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact retained ordinary citation block, no other function-summary stage.
use super::*;
pub(super) fn ordinary(
    module: &Module,
    func: &Function,
    summary: &FunctionSummary,
    import_policy: ImportPolicy<'_>,
) -> (Vec<ValidationError>, SummaryCitation) {
    let mut errors = Vec::new();
    let externally_backed = match &summary.backed_by {
        None => false,
        Some(reference) => {
            let resolves = module
                .imports
                .get(reference.module.index() as usize)
                .is_some();
            if !resolves {
                errors.push(ValidationError::DanglingExternRef {
                    detail: format!(
                        "function #{} carries a summary backed by import #{}, which is not \
                         declared in `Module::imports`",
                        func.id.index(),
                        reference.module.index()
                    ),
                });
            }
            // `ExternRef::obligation == None` "names the entity only, no proof
            // claim" — so it authenticates nothing.
            let proof_bearing = resolves && reference.obligation.is_some();
            // A proof-bearing citation on a `proved` summary is a CLAIM. Under
            // `Structural` it is taken on faith (the v41 floor); under
            // `Refuse` it is reported; under `Authenticated` the linked
            // validator's outcome for this site decides. The citation stays
            // the summary's declared backing either way, so a refusal is ONE
            // named error rather than a refusal plus a "nothing backs this
            // locally" count — the second would only restate the first.
            if proof_bearing && summary.proved {
                let import = reference.module.index();
                let refused = |detail: String| ValidationError::UnauthenticatedImport {
                    import,
                    site: "backed_by",
                    detail,
                };
                match import_policy {
                    ImportPolicy::Structural => {}
                    ImportPolicy::Refuse => errors.push(refused(format!(
                        "function #{} cites obligation #{} of {:?} in import #{import}, but \
                         this entry point has no import resolver and takes no cross-crate \
                         claim on faith; authenticate it with `validate_linked_module`",
                        func.id.index(),
                        reference.obligation.map_or(0, |o| o.index()),
                        reference.symbol
                    ))),
                    ImportPolicy::Authenticated(authenticated) => {
                        use crate::linked::SiteOutcome;
                        match authenticated.backed_by_outcome(func.id) {
                            Some(SiteOutcome::Authenticated) | Some(SiteOutcome::Reported) => {}
                            Some(SiteOutcome::Refused(detail)) => {
                                errors.push(refused(detail.clone()));
                            }
                            None => errors.push(refused(format!(
                                "function #{}'s citation was not examined by the linked \
                                 validator",
                                func.id.index()
                            ))),
                        }
                    }
                }
            }
            proof_bearing
        }
    };
    (
        errors,
        if externally_backed {
            SummaryCitation::ProofBearing
        } else {
            SummaryCitation::Absent
        },
    )
}
