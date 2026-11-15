// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Exact contiguous original final block; no earlier summary checks.
use super::*;
use std::collections::BTreeSet;
pub(super) fn ordinary(
    module: &Module,
    func: &Function,
    summary: &FunctionSummary,
    citation: SummaryCitation,
) -> Vec<ValidationError> {
    let mut errors = Vec::new();
    let invalid = |detail: String| ValidationError::InvalidFunctionSummary {
        function: func.id.index(),
        detail,
    };
    let externally_backed = citation == SummaryCitation::ProofBearing;
    if summary.proved {
        // WS1.3: a role's clauses are a SET. A restated clause says nothing
        // new, and two content-identical backing rows in one function would
        // share one lineage, so a duplicate is refused rather than demanding a
        // second row for it. With duplicates refused, the injective
        // clause -> row match below is a set match.
        let mut duplicate: BTreeSet<(usize, usize)> = BTreeSet::new();
        for (slot, role) in ContractClauseRole::ALL.into_iter().enumerate() {
            let list = role.clauses(summary);
            for (index, clause) in list.iter().enumerate() {
                if let Some(first) = list[..index].iter().position(|earlier| earlier == clause) {
                    duplicate.insert((slot, index));
                    errors.push(invalid(format!(
                        "{} clause {index} duplicates clause {first}",
                        role.name()
                    )));
                }
            }
        }

        let mut refuted: Vec<u32> = Vec::new();
        // The formula-carrying Discharged/Certified contract rows scoped to
        // this function, by the role their kind backs. A formula-less row
        // backs nothing: it does not say WHICH clause it established.
        let mut backing: Vec<(ContractClauseRole, &trust_ir::ProofFormula)> = Vec::new();
        // A body-less declaration has no body for a local obligation to be
        // ABOUT: its contract is proved where it is defined, and `backed_by`
        // is the only thing that can authenticate its `proved` bit (the v41
        // field doc; `LocalSiteHasBody` binds the local side of a citation to
        // a declaration for the same reason). Counting rows scoped to a
        // declaration let a kernel-certified tautology beside `f` earn
        // `proved` for any clause text at all — and, through an import, let a
        // dependency that merely DECLARED a symbol back an importer's
        // contract. A `Failed` row still refutes on either shape.
        let counts_locally = !func.is_declaration();
        for obligation in &module.proof_obligations {
            if obligation.function != Some(func.id) {
                continue;
            }
            // `ObligationKind` is #[non_exhaustive] and carries a payload
            // variant; every non-contract kind is ignored.
            let Some(role) = ContractClauseRole::backed_by_kind(&obligation.kind) else {
                continue;
            };
            if obligation.status.is_discharged_tier() {
                if counts_locally && let Some(formula) = &obligation.formula {
                    backing.push((role, formula));
                }
            } else if obligation.status == ProofStatus::Failed {
                refuted.push(obligation.id.index());
            }
        }

        for obligation in refuted {
            errors.push(invalid(format!(
                "summary claims `proved` while contract obligation #{obligation}, scoped to this \
                 function, is Failed"
            )));
        }

        // A DEFINITION's clauses are matched locally even when it also
        // carries a proof-bearing `backed_by`: a cross-crate citation is only
        // ever authenticated from a body-less declaration (`LocalSiteHasBody`),
        // so on a definition it backs nothing, and letting it skip the match
        // would re-admit audit c02 R1 at the structural tier the moment an
        // import row is added beside the false clause (WS1.3 review).
        if !externally_backed || counts_locally {
            for (slot, role) in ContractClauseRole::ALL.into_iter().enumerate() {
                let list = role.clauses(summary);
                if !counts_locally {
                    if !list.is_empty() {
                        errors.push(invalid(format!(
                            "summary claims `proved` with {} {} clause(s) but no local \
                             {} obligation can back a clause here: a body-less declaration has no \
                             body a local obligation could be about, so its contract is proved \
                             only where it is defined and must cite that module with \
                             `backed_by`; `backed_by: None` is NOT RECORDED",
                            list.len(),
                            role.name(),
                            role.backing_kind_name()
                        )));
                    }
                    continue;
                }
                for (index, clause) in list.iter().enumerate() {
                    if duplicate.contains(&(slot, index)) {
                        continue;
                    }
                    let backed = backing
                        .iter()
                        .any(|(row_role, formula)| *row_role == role && *formula == clause);
                    if !backed {
                        errors.push(invalid(format!(
                            "{} clause {index} `{}` has no Discharged/Certified {} row scoped to \
                             this function stating exactly this clause (rows stating other \
                             clauses do not count)",
                            role.name(),
                            crate::contracts::clause_text(clause),
                            role.backing_kind_name()
                        )));
                    }
                }
            }
        }
    }
    errors
}
