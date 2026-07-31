// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Contract → obligation minting (the WS3-M1 contracts-flow seed).
//!
//! A [`trust_ir::FunctionSummary`] carries a function's separate-compilation
//! contract (`requires`/`ensures` clauses). This module mints the module-level
//! [`ProofObligation`] rows that make the contract's verification state
//! *visible and gateable*: one `Precondition` obligation per `requires` clause
//! and one `Postcondition` obligation per `ensures` clause, each scoped to the
//! owning function (B4) and minted `Pending`.
//!
//! # Honest-seed boundaries
//!
//! * **Always `Pending`.** The summary's `proved` flag is a producer claim and
//!   is deliberately NOT trusted here — minting is bookkeeping, verification
//!   is the solver's job (the ay whole-function VC discharges or refutes; the
//!   `--forbid-failed` CLI gate aborts a build on refutation).
//! * **The clause rides in the DESCRIPTION, not as a `formula` payload.** The
//!   ay adapter's whole-function VC fails closed on formula-carrying
//!   obligations (it has no in-process SMT-LIB bridge), so a formula payload
//!   would make the minted obligation permanently `Unsupported`. This seed's
//!   discharge route is instead the in-body lowered check of the same clause
//!   (an `Inst::Assert` over the result — the checked-contract lowering);
//!   whether that assert faithfully mirrors the clause is the producer's
//!   responsibility, exactly like every claim-style annotation. Attaching the
//!   machine-readable `ProofFormula` is the post-SMT-LIB-bridge upgrade.

use trust_ir::Module;
use trust_ir::proof::{ObligationKind, ProofFormula, ProofObligation, ProofStatus};
use trust_ir::value::{FuncId, ProofId};

/// Render a contract clause for an obligation description: the SMT-LIB text
/// when the clause carries one, otherwise the schema-tagged opaque payload
/// (never silently empty).
fn clause_text(clause: &ProofFormula) -> String {
    match &clause.smtlib {
        Some(smtlib) => smtlib.clone(),
        None => format!("[{}] {}", clause.schema, clause.payload),
    }
}

/// Next free obligation id in `module` (max existing id + 1, or 0).
fn next_obligation_id(module: &Module) -> u32 {
    module
        .proof_obligations
        .iter()
        .map(|o| o.id.index() + 1)
        .max()
        .unwrap_or(0)
}

/// Mint the `Pending` proof obligations for a function's contract: one
/// function-scoped (B4) `Precondition` per `requires` clause and one
/// `Postcondition` per `ensures` clause, appended to
/// `module.proof_obligations` with fresh ids. Returns the minted ids, in
/// clause order (requires first).
///
/// Mints nothing (and returns an empty vec) when `func` names no function in
/// the module, the function carries no summary, or the summary has no
/// clauses — a contract that does not exist imposes no obligations. Idempotence
/// is NOT provided: calling twice mints duplicate rows (the caller owns
/// when-to-mint, typically once at lowering time).
///
/// See the module docs for why the minted obligations carry the clause in the
/// description rather than as a `formula` payload (honest-seed boundary).
pub fn mint_summary_obligations(module: &mut Module, func: FuncId) -> Vec<ProofId> {
    let Some(function) = module.function_by_id(func) else {
        return Vec::new();
    };
    let Some(summary) = &function.summary else {
        return Vec::new();
    };
    let name = function.name.clone();
    let mut minted = Vec::new();
    let mut next = next_obligation_id(module);
    // Collect first so the shared borrow of `function`/`summary` ends before
    // the pushes below take `module` mutably.
    let mut rows: Vec<(ObligationKind, String)> = Vec::new();
    for (i, clause) in summary.requires.iter().enumerate() {
        rows.push((
            ObligationKind::Precondition,
            format!("requires clause {i} of '{name}': {}", clause_text(clause)),
        ));
    }
    for (i, clause) in summary.ensures.iter().enumerate() {
        rows.push((
            ObligationKind::Postcondition,
            format!("ensures clause {i} of '{name}': {}", clause_text(clause)),
        ));
    }
    for (kind, description) in rows {
        let id = ProofId::new(next);
        next += 1;
        module.proof_obligations.push(
            ProofObligation::new(id, kind, ProofStatus::Pending, description).with_function(func),
        );
        minted.push(id);
    }
    minted
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
        let mut module = mb.build();
        module.functions[0].summary = Some(
            FunctionSummary::new()
                .with_params(vec!["x".to_string()])
                .requiring(ProofFormula::smtlib2("(>= x 0)", "Bool"))
                .ensuring(ProofFormula::smtlib2("(= result (+ x 1))", "Bool")),
        );
        module
    }

    #[test]
    fn mints_scoped_pending_obligations_per_clause() {
        let mut module = contract_module();
        let func = module.functions[0].id;
        let ids = mint_summary_obligations(&mut module, func);
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

        // Honest-seed boundary: no formula payload (the ay VC would fail
        // closed on one); the clause is carried in the description.
        assert!(pre.formula.is_none());
        assert!(post.formula.is_none());

        // The minted module stays well-formed.
        assert!(crate::validate_module(&module).is_empty());
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
        let ids = mint_summary_obligations(&mut module, func);
        assert_eq!(ids, vec![ProofId::new(8), ProofId::new(9)]);
    }

    #[test]
    fn no_summary_or_unknown_function_mints_nothing() {
        let mut module = contract_module();
        let func = module.functions[0].id;
        module.functions[0].summary = None;
        assert!(mint_summary_obligations(&mut module, func).is_empty());

        let mut module = contract_module();
        assert!(mint_summary_obligations(&mut module, FuncId::new(999)).is_empty());
        assert!(module.proof_obligations.is_empty());
    }

    #[test]
    fn proved_flag_is_not_trusted_minted_status_stays_pending() {
        let mut module = contract_module();
        let func = module.functions[0].id;
        module.functions[0].summary = Some(module.functions[0].summary.take().unwrap().proved());
        let ids = mint_summary_obligations(&mut module, func);
        assert_eq!(ids.len(), 2);
        for o in &module.proof_obligations {
            assert_eq!(
                o.status,
                ProofStatus::Pending,
                "a producer's `proved` claim must not pre-discharge minted obligations"
            );
        }
    }
}
