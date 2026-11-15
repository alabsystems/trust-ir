// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Contract → obligation minting (the WS3-M1 contracts-flow seed).
//!
//! A [`trust_ir::FunctionSummary`] carries a function's separate-compilation
//! contract (`requires` / `ensures` / `decreases` clauses). This module mints
//! the module-level [`ProofObligation`] rows that make the contract's
//! verification state *visible and gateable*: one `Precondition` obligation
//! per `requires` clause, one `Postcondition` obligation per `ensures` clause
//! and one `Termination` obligation per `decreases` measure (WS1.9), each
//! scoped to the owning function (B4) and minted `Pending`.
//!
//! # Honest-seed boundaries
//!
//! * **Always `Pending`.** The summary's `proved` flag is a producer claim and
//!   is deliberately NOT trusted here — minting is bookkeeping, verification
//!   is the solver's job (the ay whole-function VC discharges or refutes; the
//!   `--forbid-failed` CLI gate aborts a build on refutation).
//! * **Each row carries its clause as its `formula` (WS1.3).** The clause is
//!   attached verbatim (`schema`, `payload`, `smtlib`, `sort` and `bindings`
//!   alike), and the description keeps a human rendering of it. The formula is
//!   what makes a row BACK a clause: the validator's `proved` rule matches
//!   every clause to a Discharged/Certified row of the right kind whose
//!   `formula` equals it exactly, and a formula-less row backs nothing. The
//!   description is never read back — recovering a clause from a human-facing
//!   string would be a scraper, not a check.
//! * **Consequence on the ay lane (fail closed).** The ay adapter's
//!   whole-function VC reports a formula-carrying obligation `Unsupported`
//!   (it has no in-process SMT-LIB bridge over bound places yet), so a row
//!   minted here is never ay-discharged, and ay alone cannot earn `proved`
//!   until the adapter learns to discharge a formula-carrying contract row
//!   (roadmap WS5 / F-091). Before WS1.3 such a row was discharged by an
//!   in-body assert that nothing tied to the clause — exactly the counting
//!   rule the validator no longer accepts.
//! * **`decreases` mints a `Termination` row (WS1.9, finding F-011).** The
//!   measure is the row's `formula`, exactly as a `requires` / `ensures`
//!   clause is, so the per-clause `proved` rule (`Termination`↔`decreases`)
//!   has a row to match. Before WS1.9 only `requires` and `ensures` were
//!   minted (archived row `b2.gap.mint_summary_obligations_skips_decreases`),
//!   so a `proved` summary with a `decreases` clause could never be earned
//!   through this minter. The DISCHARGE route for such a row is a consumer
//!   capability (ay / trust-mc: a well-founded-descent check reported as
//!   `Discharged` with its certificate) — the Clean kernel contract grounder
//!   deliberately refuses `Termination` (roadmap WS1.9 DECIDE A: no
//!   well-founded-measure kernel anchor now), so a `Termination` row is never
//!   `Certified` by this repo.

use trust_ir::Module;
use trust_ir::proof::{ObligationKind, ProofFormula, ProofObligation, ProofStatus};
use trust_ir::value::{FuncId, IdSpaceExhausted, ProofId};

/// Render a contract clause for an obligation description (and for the
/// validator's per-clause `proved` refusals): the SMT-LIB text when the clause
/// carries one, otherwise the schema-tagged opaque payload (never silently
/// empty). Human-facing only — no rule ever reads it back.
pub(crate) fn clause_text(clause: &ProofFormula) -> String {
    match &clause.smtlib {
        Some(smtlib) => smtlib.clone(),
        None => format!("[{}] {}", clause.schema, clause.payload),
    }
}

/// Mint the `Pending` proof obligations for a function's contract: one
/// function-scoped (B4) `Precondition` per `requires` clause, one
/// `Postcondition` per `ensures` clause and one `Termination` per
/// `decreases` measure (WS1.9), appended to `module.proof_obligations` with
/// fresh ids. Returns the minted ids, in clause order (requires, then
/// ensures, then decreases).
///
/// Mints nothing (and returns an empty vec) when `func` names no function in
/// the module, the function carries no summary, or the summary has no
/// clauses — a contract that does not exist imposes no obligations. Idempotence
/// is NOT provided: calling twice mints duplicate rows (the caller owns
/// when-to-mint, typically once at lowering time).
///
/// Each minted row carries its clause as `formula` (so it can back exactly
/// that clause of a `proved` summary) and a human rendering in `description`;
/// see the module docs for the ay-lane consequence.
///
/// # Errors
///
/// [`IdSpaceExhausted`] when the clauses need more obligation ids than remain
/// (a decoded table may already hold `u32::MAX`). All or nothing: on `Err`
/// the table is unchanged.
pub fn mint_summary_obligations(
    module: &mut Module,
    func: FuncId,
) -> Result<Vec<ProofId>, IdSpaceExhausted> {
    let Some(function) = module.function_by_id(func) else {
        return Ok(Vec::new());
    };
    let Some(summary) = &function.summary else {
        return Ok(Vec::new());
    };
    let name = function.name.clone();
    let mut minted = Vec::new();
    // Collect first so the shared borrow of `function`/`summary` ends before
    // the pushes below take `module` mutably.
    let mut rows: Vec<(ObligationKind, String, ProofFormula)> = Vec::new();
    for (i, clause) in summary.requires.iter().enumerate() {
        rows.push((
            ObligationKind::Precondition,
            format!("requires clause {i} of '{name}': {}", clause_text(clause)),
            clause.clone(),
        ));
    }
    for (i, clause) in summary.ensures.iter().enumerate() {
        rows.push((
            ObligationKind::Postcondition,
            format!("ensures clause {i} of '{name}': {}", clause_text(clause)),
            clause.clone(),
        ));
    }
    // WS1.9: a `decreases` measure is a clause like any other (v41), and the
    // per-clause `proved` rule matches it to a `Termination` row stating it.
    for (i, clause) in summary.decreases.iter().enumerate() {
        rows.push((
            ObligationKind::Termination,
            format!("decreases clause {i} of '{name}': {}", clause_text(clause)),
            clause.clone(),
        ));
    }
    // The core's one fresh-id rule (one past the highest existing id), taken
    // as ONE run before any row is pushed: all or nothing, never wrapped.
    let count = u32::try_from(rows.len()).map_err(|_| IdSpaceExhausted::of::<ProofId>())?;
    let mut ids = module.fresh_obligation_ids().take_run(count)?;
    for (kind, description, formula) in rows {
        let Some(id) = ids.take() else {
            // The run holds exactly one id per row.
            return Err(IdSpaceExhausted::of::<ProofId>());
        };
        module.proof_obligations.push(
            ProofObligation::new(id, kind, ProofStatus::Pending, description)
                .with_function(func)
                .with_formula(formula),
        );
        minted.push(id);
    }
    Ok(minted)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ModuleBuilder;
    use trust_ir::FunctionSummary;
    use trust_ir::ty::Ty;

    /// `fn bump(x: i64) -> i64` with an `ensures (= result (+ x 1))` /
    /// `requires (>= x 0)` contract.
    fn contract_module() -> Module {
        let mut mb = ModuleBuilder::new("contracts");
        let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("bump", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let one = fb.iconst(Ty::I64, 1);
        let r = fb.add(Ty::I64, x, one);
        fb.ret(vec![r]);
        fb.build();
        let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
        module.functions[0].summary = Some(
            FunctionSummary::new()
                .with_params(vec!["x".to_string()])
                .requiring(ProofFormula::smtlib2("(>= x 0)", "Bool"))
                .ensuring(ProofFormula::smtlib2("(= result (+ x 1))", "Bool")),
        );
        module
    }

    /// r11 item 6 (port of probe P7(b), evidence kind ii): a DECODED table
    /// holding `u32::MAX - 1` has ONE id left, and a two-clause contract needs
    /// two. Before r11 the first row was pushed and the second panicked
    /// (`expect` inside the push loop), leaving a partial table. Now the ids
    /// are taken as one run first: refused, typed, table unchanged. Mutation
    /// check: allocating inside the push loop pushes the first row.
    #[test]
    fn mint_summary_obligations_is_all_or_nothing() {
        let mut module = contract_module();
        let func = module.functions[0].id;
        module.proof_obligations.push(ProofObligation::new(
            ProofId::new(u32::MAX - 1),
            ObligationKind::PanicFreedom,
            ProofStatus::Pending,
            "decoded row",
        ));
        let before = module.proof_obligations.clone();
        assert_eq!(
            mint_summary_obligations(&mut module, func),
            Err(IdSpaceExhausted { space: "ProofId" })
        );
        assert_eq!(module.proof_obligations, before, "no row was pushed");

        // At u32::MAX no id is left at all.
        module.proof_obligations[0].id = ProofId::new(u32::MAX);
        assert!(mint_summary_obligations(&mut module, func).is_err());
        assert_eq!(module.proof_obligations.len(), 1);
    }

    #[test]
    fn mints_scoped_pending_obligations_per_clause() {
        let mut module = contract_module();
        let func = module.functions[0].id;
        let ids = mint_summary_obligations(&mut module, func).expect("fresh obligation ids");
        assert_eq!(ids.len(), 2);

        let pre = &module.proof_obligations[0];
        assert_eq!(pre.id, ids[0]);
        assert_eq!(pre.kind, ObligationKind::Precondition);
        assert_eq!(pre.status, ProofStatus::Pending);
        assert_eq!(pre.function, Some(func));
        assert!(pre.description.contains("requires clause 0 of 'bump'"));
        assert!(pre.description.contains("(>= x 0)"));

        let post = &module.proof_obligations[1];
        assert_eq!(post.id, ids[1]);
        assert_eq!(post.kind, ObligationKind::Postcondition);
        assert_eq!(post.status, ProofStatus::Pending);
        assert_eq!(post.function, Some(func));
        assert!(post.description.contains("ensures clause 0 of 'bump'"));
        assert!(post.description.contains("(= result (+ x 1))"));

        // WS1.3: each row states its clause EXACTLY (bindings and all), so it
        // can back that clause and no other.
        let summary = module.functions[0].summary.as_ref().unwrap();
        assert_eq!(pre.formula.as_ref(), Some(&summary.requires[0]));
        assert_eq!(post.formula.as_ref(), Some(&summary.ensures[0]));

        // The minted module stays well-formed.
        assert!(crate::validate_module(&module).is_empty());
    }

    /// `fn countdown(n: u64) -> u64 { if n == 0 { 0 } else { countdown(n - 1) } }`
    /// with `ensures (>= result 0)` and ONE `decreases n` measure (the WS1.9
    /// positive fixture; the archived `b2_countdown` shape).
    fn countdown_module() -> Module {
        use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};
        let mut mb = ModuleBuilder::new("countdown");
        let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let this = mb
            .peek_next_func_id()
            .expect("peek_next_func_id: test fixture");
        let mut fb = mb.function("countdown", ft);
        let entry = fb.create_block();
        let rec = fb.create_block();
        let done = fb.create_block();
        let n = fb.add_block_param(entry, Ty::U64);
        let out = fb.add_block_param(done, Ty::U64);
        fb.switch_to_block(entry);
        let zero = fb.uconst(Ty::U64, 0);
        let is0 = fb.icmp(trust_ir::ICmpOp::Eq, Ty::U64, n, zero);
        fb.condbr(is0, done, vec![zero], rec, vec![]);
        fb.switch_to_block(rec);
        let one = fb.uconst(Ty::U64, 1);
        let m = fb.sub(Ty::U64, n, one);
        let r = fb.call(this, vec![m]);
        fb.br(done, vec![r]);
        fb.switch_to_block(done);
        fb.ret(vec![out]);
        fb.build();
        let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
        let mut ensures = ProofFormula::smtlib2("(>= result 0)", "Bool");
        ensures.bindings = vec![(
            "result".to_string(),
            ClauseBinding {
                sort: ClauseSort::Int,
                place: ClausePlace::ResultSlot { index: 0 },
            },
        )];
        let mut measure = ProofFormula::smtlib2("n", "Int");
        measure.bindings = vec![(
            "n".to_string(),
            ClauseBinding {
                sort: ClauseSort::Int,
                place: ClausePlace::Param { index: 0 },
            },
        )];
        let mut summary = FunctionSummary::new()
            .with_params(vec!["n".to_string()])
            .ensuring(ensures);
        summary.decreases.push(measure);
        module.functions[0].summary = Some(summary);
        module
    }

    /// WS1.9 positive: one `decreases` measure mints exactly ONE `Termination`
    /// row, function-scoped, `Pending`, whose `formula` IS the measure (the
    /// archived GAP `b2.gap.mint_summary_obligations_skips_decreases` minted
    /// the ensures rows only).
    #[test]
    fn a_decreases_measure_mints_one_termination_row_stating_it() {
        let mut module = countdown_module();
        let func = module.functions[0].id;
        let ids = mint_summary_obligations(&mut module, func).expect("fresh obligation ids");
        assert_eq!(ids.len(), 2, "1 ensures + 1 decreases");
        let kinds: Vec<&ObligationKind> =
            module.proof_obligations.iter().map(|o| &o.kind).collect();
        assert_eq!(
            kinds,
            [&ObligationKind::Postcondition, &ObligationKind::Termination],
            "ensures first, then the decreases measure"
        );
        let summary = module.functions[0].summary.as_ref().unwrap();
        let termination = &module.proof_obligations[1];
        assert_eq!(termination.id, ids[1]);
        assert_eq!(termination.status, ProofStatus::Pending);
        assert_eq!(termination.function, Some(func));
        assert_eq!(
            termination.site, None,
            "a contract row is function-scoped, not sited"
        );
        assert_eq!(
            termination.formula.as_ref(),
            Some(&summary.decreases[0]),
            "the row states the measure EXACTLY (bindings included)"
        );
        assert!(
            termination
                .description
                .starts_with("decreases clause 0 of 'countdown': n"),
            "{}",
            termination.description
        );
        assert!(crate::validate_module(&module).is_empty());
    }

    /// WS1.9: the minted `Termination` row is the row the per-clause `proved`
    /// rule looks for. Pending it backs nothing (the decreases clause is
    /// refused BY NAME); Discharged under a replay capability it earns
    /// `proved`; and the negative twin — the same row re-filed as `Liveness`,
    /// where `decreases` used to be mis-filed — is refused with the same named
    /// reason, so the kind is load-bearing, not the formula alone.
    #[test]
    fn a_discharged_termination_row_earns_proved_for_its_decreases_clause() {
        use std::collections::BTreeSet;
        use trust_ir::proof::{
            ModuleProofAuthority, ProofCertificate, ProofCertificateRef, ProofEvidence,
        };
        /// TEST STAND-IN for a consumer-side replay capability: admits exactly
        /// the listed certificates, by lineage reference.
        struct AdmitSet(BTreeSet<ProofCertificateRef>);
        impl ModuleProofAuthority for AdmitSet {
            fn replays_authority(
                &self,
                _module: &Module,
                obligation: &ProofObligation,
                certificate: &ProofCertificate,
            ) -> bool {
                certificate.obligation == obligation.id
                    && self.0.contains(&certificate.lineage_ref())
            }
        }
        fn summary_details(errors: &[crate::ValidationError]) -> Vec<String> {
            errors
                .iter()
                .filter_map(|error| match error {
                    crate::ValidationError::InvalidFunctionSummary { detail, .. } => {
                        Some(detail.clone())
                    }
                    _ => None,
                })
                .collect()
        }
        let no_termination_row = "decreases clause 0 `n` has no Discharged/Certified Termination \
                                  row scoped to this function stating exactly this clause (rows \
                                  stating other clauses do not count)";

        let mut module = countdown_module();
        let func = module.functions[0].id;
        module.functions[0].summary = Some(module.functions[0].summary.take().unwrap().proved());
        let ids = mint_summary_obligations(&mut module, func).expect("fresh obligation ids");
        // Pending: the decreases clause is refused BY NAME.
        let details = summary_details(&crate::validate_module(&module));
        assert!(
            details.iter().any(|d| d == no_termination_row),
            "{details:?}"
        );

        // Discharge BOTH minted rows (the ensures row too, so that only the
        // decreases clause is in question) under the stand-in capability.
        for id in &ids {
            let row = module
                .proof_obligations
                .iter_mut()
                .find(|o| o.id == *id)
                .unwrap();
            row.status = ProofStatus::Discharged;
            module.proof_certificates.push(ProofCertificate {
                obligation: *id,
                prover: "trust-mc-stand-in".to_string(),
                evidence: ProofEvidence::SmtProof(b"(unsat)".to_vec()),
                assurance: None,
            });
        }
        let certificate_ref = |module: &Module, id: ProofId| -> ProofCertificateRef {
            module
                .proof_certificates
                .iter()
                .find(|c| c.obligation == id)
                .unwrap()
                .lineage_ref()
        };
        let admit_all = AdmitSet(ids.iter().map(|id| certificate_ref(&module, *id)).collect());
        let errors = crate::validate_module_with_authority(&module, &admit_all);
        assert!(errors.is_empty(), "proved earned: {errors:?}");

        // Negative twin: the SAME discharged row re-filed as `Liveness` (its
        // certificate still admitted) backs nothing for `decreases`.
        let mut twin = module.clone();
        let row = twin
            .proof_obligations
            .iter_mut()
            .find(|o| o.id == ids[1])
            .unwrap();
        assert_eq!(row.kind, ObligationKind::Termination);
        row.kind = ObligationKind::Liveness;
        let details = summary_details(&crate::validate_module_with_authority(&twin, &admit_all));
        assert_eq!(details, vec![no_termination_row.to_string()]);

        // Mutation control: the clause match reads the row's KIND and FORMULA,
        // not its authority (that is the separate certificate rule). With the
        // Termination row deleted outright the decreases clause is refused by
        // name again while the ensures clause stays backed.
        let mut without = module.clone();
        without.proof_obligations.retain(|o| o.id != ids[1]);
        without
            .proof_certificates
            .retain(|c| c.obligation != ids[1]);
        let details = summary_details(&crate::validate_module_with_authority(&without, &admit_all));
        assert_eq!(details, vec![no_termination_row.to_string()]);
    }

    #[test]
    fn ids_are_allocated_past_existing_obligations() {
        let mut module = contract_module();
        let func = module.functions[0].id;
        module.proof_obligations.push(ProofObligation::new(
            ProofId::new(7),
            ObligationKind::PanicFreedom,
            ProofStatus::Pending,
            "pre-existing row",
        ));
        let ids = mint_summary_obligations(&mut module, func).expect("fresh obligation ids");
        assert_eq!(ids, vec![ProofId::new(8), ProofId::new(9)]);
    }

    #[test]
    fn no_summary_or_unknown_function_mints_nothing() {
        let mut module = contract_module();
        let func = module.functions[0].id;
        module.functions[0].summary = None;
        assert!(
            mint_summary_obligations(&mut module, func)
                .expect("nothing to mint")
                .is_empty()
        );

        let mut module = contract_module();
        assert!(
            mint_summary_obligations(&mut module, FuncId::new(999))
                .expect("nothing to mint")
                .is_empty()
        );
        assert!(module.proof_obligations.is_empty());
    }

    #[test]
    fn proved_flag_is_not_trusted_minted_status_stays_pending() {
        let mut module = contract_module();
        let func = module.functions[0].id;
        module.functions[0].summary = Some(module.functions[0].summary.take().unwrap().proved());
        let ids = mint_summary_obligations(&mut module, func).expect("fresh obligation ids");
        assert_eq!(ids.len(), 2);
        for o in &module.proof_obligations {
            assert_eq!(
                o.status,
                ProofStatus::Pending,
                "a producer's `proved` claim must not pre-discharge minted obligations"
            );
        }
        // And a Pending row backs nothing: every clause is refused by name.
        let details: Vec<String> = crate::validate_module(&module)
            .into_iter()
            .filter_map(|error| match error {
                crate::ValidationError::InvalidFunctionSummary { detail, .. } => Some(detail),
                _ => None,
            })
            .collect();
        assert!(
            details.iter().any(|d| d.starts_with(
                "requires clause 0 `(>= x 0)` has no Discharged/Certified Precondition row"
            )),
            "{details:?}"
        );
        assert!(
            details.iter().any(|d| d.starts_with(
                "ensures clause 0 `(= result (+ x 1))` has no Discharged/Certified Postcondition row"
            )),
            "{details:?}"
        );
    }
}
