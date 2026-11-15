// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Roadmap WS1.13: user-theorem certification through an ISLAND ENVIRONMENT
//! (finding F-012), and the source check of a translation-validation
//! comparand (the check half of finding F-008). No CIC core enters trust-ir:
//! the island's declarations are opaque bytes decoded by the anchor's own
//! bounded decoder and judged by the Clean kernel.
//!
//! # The island
//!
//! A [`trust_ir::proof::IslandEnvironment`] rides inside a certificate's
//! [`trust_ir::proof::CertificateBinding`]. [`install`] turns it into kernel
//! declarations in a fixed order, refusing at the first failure:
//!
//! 1. the digest is recomputed from the bytes BEFORE anything is decoded
//!    (`trust_ir.clean_cic.island.v1`);
//! 2. the bytes are decoded by the canonical, resource-bounded island codec
//!    (whole slice, byte / node / depth / declaration ceilings, re-encoding);
//! 3. a declaration that REDECLARES a name the anchor environment already
//!    has, or one an earlier island declaration took, is refused by name
//!    (`island redeclares <name>`) — never left to whatever `add_decl` does
//!    on a duplicate — and so is one under a validator-owned theorem root
//!    ([`VALIDATOR_OWNED_THEOREM_ROOTS`]: `CleanTV`, `NNVerify`, …), so an
//!    island theorem can never take the name of a theorem the validator's own
//!    anchors establish;
//! 4. an `Axiom` (or an `Opaque`) is refused: an island adds definitions and
//!    theorems, never an assumption;
//! 5. every declaration is inserted with the kernel's CHECKED `add_decl`, so
//!    a body the kernel does not accept never enters the environment.
//!
//! The base environment is the `clean_backend_tv` anchor environment (the
//! ground prelude plus the Fragment-4 heap vocabulary and the S3 signed
//! carrier aliases), so an island may state its definitions in exactly the
//! vocabulary a translation-validation comparand uses, and one island
//! environment serves both anchors.
//!
//! # The two re-checks
//!
//! * [`recheck_theorem`] — the `clean_island` anchor: a `lean.theorem` row's
//!   cited island theorem passes the rooted audit (no axiom beyond the
//!   canonical foundations; the validator's axiom policy has no island row),
//!   and its type is DEFINITIONALLY EQUAL to the statement the pinned
//!   grounder derives from the row's own formula
//!   (`trust_ir::clean_expr_lowering::island`). The constants that statement
//!   cites are handed back for the SYMBOL BRIDGE, which the caller checks
//!   after every translation-validation certificate has been re-checked.
//! * [`check_comparand_is_source`] — the `clean_backend_tv` anchor with an
//!   island (F-008): the recorded comparand must be definitionally equal to
//!   the value of `binding.source.decl` in the island. The comparand is then
//!   the source definition, not a producer's choice.

use clean_kernel::env::{ConstantKind, Declaration, Environment};
use clean_kernel::{Expr, ExprKind, LocalContext, Name, TypeChecker};
use std::collections::BTreeSet;
use trust_ir::clean_expr_lowering::island::island_statement_goal;
use trust_ir::proof::{
    CleanCicKernelRecheck, IslandEnvironment, ObligationKind, ProofEvidence, ProofObligation,
    clean_cic_statement_digest, decode_clean_expr_v1, decode_island_declarations_v1,
    island_declarations_digest, kernel_environment_digest,
};

/// Every name the environment already binds: constants, inductive types,
/// constructors, recursors and quotient primitives.
fn bound_names(env: &Environment) -> BTreeSet<String> {
    let mut names: BTreeSet<String> = env.constants().map(|c| c.name.to_string()).collect();
    names.extend(env.inductives().map(|i| i.name.to_string()));
    names.extend(env.constructors().map(|c| c.name.to_string()));
    names.extend(env.recursors().map(|r| r.name.to_string()));
    names.extend(env.quotients().map(|q| q.name.to_string()));
    names
}

/// The ROOT namespaces of every theorem a validator-owned kernel anchor
/// establishes or cites: `CleanTV` (the translation-validation equation
/// `CleanTV.<fn>.denotes`, `clean_backend_tv`), `NNVerify` (the Farkas law
/// library), `RustSem` (the give-back law libraries), `TrustCg` (the
/// lowering-resolution theorem) and `Crownproof` (the SlackCertZ theorem).
///
/// An island may declare nothing under them (review of WS1.13). The kernel
/// witness `kernel_certified_theorems` — what a spec `ProofKind::CleanTheorem`
/// binding resolves against — is keyed by theorem NAME alone, and before the
/// island every name in it was the validator's: a fixed anchor's library
/// statement, or a TV equation the validator derived for that function. An
/// island names its own declarations, so without this rule a producer could
/// certify `CleanTV.f.denotes : 1 = 1` for a function `f` with NO translation
/// validation (or `NNVerify.farkas_combine_2_le_bound : 1 = 1`), and a spec
/// binding naming that theorem would resolve against the forgery.
pub(super) const VALIDATOR_OWNED_THEOREM_ROOTS: &[&str] =
    &["CleanTV", "Crownproof", "NNVerify", "RustSem", "TrustCg"];

/// The validator-owned root `name` lives under, if any (compared on the
/// display form, like every other island name check).
fn validator_owned_root(name: &str) -> Option<&'static str> {
    let root = name.split('.').next().unwrap_or(name);
    VALIDATOR_OWNED_THEOREM_ROOTS
        .iter()
        .copied()
        .find(|owned| *owned == root)
}

fn declaration_name(declaration: &Declaration) -> &Name {
    match declaration {
        Declaration::Definition { name, .. }
        | Declaration::Axiom { name, .. }
        | Declaration::Theorem { name, .. }
        | Declaration::Opaque { name, .. } => name,
    }
}

/// Install `island` into `env` (steps 1-5 of the module docs). Returns the
/// names the island declares, in insertion order. Every failure is a
/// refusal reason; nothing is inserted past it (the caller discards `env`).
pub(super) fn install(
    env: &mut Environment,
    island: &IslandEnvironment,
) -> Result<Vec<Name>, String> {
    let recomputed = island_declarations_digest(&island.declarations);
    if recomputed != island.digest {
        return Err(format!(
            "island digest mismatch: the certificate carries {}, the island's declaration bytes \
             digest to {recomputed} — REJECTED",
            island.digest
        ));
    }
    let declarations = decode_island_declarations_v1(&island.declarations)
        .map_err(|error| format!("island declarations do not decode ({error}) — REJECTED"))?;
    if declarations.is_empty() {
        return Err("island declares nothing — REJECTED".to_string());
    }
    let mut taken = bound_names(env);
    for declaration in &declarations {
        let name = declaration_name(declaration).to_string();
        if !taken.insert(name.clone()) {
            return Err(format!(
                "island redeclares {name}: the name is already bound in the anchor environment \
                 or earlier in the island — REJECTED"
            ));
        }
        if let Some(root) = validator_owned_root(&name) {
            return Err(format!(
                "island declares {name} in the validator-owned `{root}` namespace: theorems \
                 there are established only by the validator's own anchors (a TV equation, a \
                 fixed law library), and the kernel witness is keyed by name — REJECTED"
            ));
        }
        match declaration {
            Declaration::Definition { .. } | Declaration::Theorem { .. } => {}
            Declaration::Axiom { .. } => {
                return Err(format!(
                    "island declares axiom {name}: an island adds definitions and theorems, never \
                     an assumption — REJECTED"
                ));
            }
            Declaration::Opaque { .. } => {
                return Err(format!(
                    "island declares opaque constant {name}: slice 1 admits Definition and \
                     Theorem declarations only — REJECTED"
                ));
            }
        }
    }
    let mut names = Vec::with_capacity(declarations.len());
    for declaration in declarations {
        let name = declaration_name(&declaration).clone();
        env.add_decl(declaration).map_err(|error| {
            format!(
                "the Clean kernel REFUSED island declaration {name}: {error:?} — REJECTED \
                 (the island's bytes are untrusted; every declaration is re-checked on insertion)"
            )
        })?;
        names.push(name);
    }
    Ok(names)
}

/// Step 7 for a name the anchor declares AFTER installing the island (the
/// translation-validation equation theorem `CleanTV.<fn>.denotes`): the
/// island may not have taken it. Refused by name, never left to whatever
/// `add_decl` does on a duplicate. [`install`] already refuses the whole
/// `CleanTV` root; this exact-name guard stays so the clash is refused even if
/// that root list ever changes.
pub(super) fn refuse_island_name(island: &[Name], reserved: &str) -> Result<(), String> {
    if island.iter().any(|name| name.to_string() == reserved) {
        return Err(format!(
            "island redeclares {reserved}: the name is the certificate's own \
             translation-validation theorem, which the re-check declares after the island — \
             REJECTED"
        ));
    }
    Ok(())
}

/// F-008 (WS1.13): the translation-validation comparand must be the value of
/// the island's `decl`. `decl` must be declared BY the island (not by the
/// anchor environment), as a monomorphic `Definition`; the comparand must
/// have the declaration's type (FULL check), and be definitionally equal to
/// its value.
pub(super) fn check_comparand_is_source(
    env: &Environment,
    island: &[Name],
    decl: &str,
    comparand: &Expr,
) -> Result<(), String> {
    let Some(name) = island.iter().find(|name| name.to_string() == decl) else {
        return Err(format!(
            "the certificate's source declaration `{decl}` is not declared by its island — \
             REJECTED (F-008: the comparand must be the value of an island declaration)"
        ));
    };
    let info = env
        .get_const(name)
        .ok_or_else(|| format!("island declaration `{decl}` is not in the environment"))?;
    if info.kind != ConstantKind::Definition || !info.level_params.is_empty() {
        return Err(format!(
            "the certificate's source declaration `{decl}` is a {:?} with {} universe \
             parameter(s): the comparand is bound only to a monomorphic Definition — REJECTED",
            info.kind,
            info.level_params.len()
        ));
    }
    let value = info
        .value
        .clone()
        .ok_or_else(|| format!("island definition `{decl}` carries no value — REJECTED"))?;
    let tc = TypeChecker::with_context(env, LocalContext::new());
    tc.check_type(comparand, &info.type_).map_err(|error| {
        format!(
            "the TV comparand does not have the type of island declaration `{decl}` ({error:?}) \
             — REJECTED (F-008)"
        )
    })?;
    if !tc.is_def_eq(comparand, &value) {
        return Err(format!(
            "the TV comparand is not the value of island declaration `{decl}` in this environment \
             — REJECTED (F-008: a certificate re-minted over another comparand cannot claim this \
             source)"
        ));
    }
    Ok(())
}

/// The `clean_island` anchor re-check (roadmap WS1.13 steps 1-5). The symbol
/// bridge (step 6) needs every TV certificate's outcome and runs after the
/// per-obligation loop. Every failure is a refusal reason.
pub(super) fn recheck_theorem(
    oblig: &ProofObligation,
    evidence: &ProofEvidence,
    directive: &CleanCicKernelRecheck,
) -> Result<super::IslandTheoremOutcome, String> {
    let ObligationKind::Custom { name: theorem, .. } = &oblig.kind else {
        return Err("the clean_island anchor certifies only lean.theorem rows — REJECTED".into());
    };
    let ProofEvidence::CleanCic { term, context, .. } = evidence else {
        return Err("clean_island re-check reached with non-CleanCic evidence — REJECTED".into());
    };
    // (0) The directive names exactly the row's theorem and admits no axiom.
    if directive.theorems.as_slice() != std::slice::from_ref(theorem) {
        return Err(format!(
            "an island certificate must cite exactly the row's theorem ['{theorem}'], got {:?} — \
             REJECTED",
            directive.theorems
        ));
    }
    if !directive.allowed_axioms.is_empty() {
        return Err(format!(
            "an island certificate admits no axiom (the validator's axiom policy has no island \
             row), got allowed_axioms {:?} — REJECTED",
            directive.allowed_axioms
        ));
    }
    let binding = directive.binding.as_deref().ok_or_else(|| {
        "the clean_island anchor requires a bound certificate: the island it is checked in \
         travels in CertificateBinding.environment — REJECTED"
            .to_string()
    })?;
    let island = binding.environment.as_ref().ok_or_else(|| {
        "the clean_island anchor requires CertificateBinding.environment (the island the \
         theorem is checked in) — REJECTED"
            .to_string()
    })?;
    if binding.source.is_some() {
        return Err(
            "an island theorem certificate names no source declaration (a source reference binds \
             a translation-validation comparand) — REJECTED"
                .to_string(),
        );
    }
    // (0') `term` is exactly the reference to the cited theorem, and
    // `context` is empty: the statement is DERIVED here, never carried.
    let reference = decode_clean_expr_v1(term).map_err(|error| {
        format!("island certificate `term` does not decode to a kernel Expr ({error}) — REJECTED")
    })?;
    let references_theorem = matches!(
        reference.kind(),
        ExprKind::Const(name, levels) if levels.is_empty() && name.to_string() == *theorem
    );
    if !references_theorem {
        return Err(format!(
            "island certificate `term` must be the constant `{theorem}` (the island theorem the \
             kernel re-checks), got another term — REJECTED"
        ));
    }
    if !context.is_empty() {
        return Err(
            "island certificate `context` must be empty: the statement is derived from the \
             obligation's formula, never carried — REJECTED"
                .to_string(),
        );
    }
    // (1)-(3), (7) Build the anchor environment and install the island.
    let mut env = super::clean_backend_tv::anchor_environment()?;
    let names = install(&mut env, island)?;
    if !names.iter().any(|name| name.to_string() == *theorem) {
        return Err(format!(
            "the cited theorem `{theorem}` is not declared by the island — REJECTED (an island \
             certificate re-checks a theorem it carries)"
        ));
    }
    let environment_digest = kernel_environment_digest(&env)
        .map_err(|error| format!("the island environment has no digest ({error}) — REJECTED"))?;
    // (5) The statement the row's formula MEANS (pinned grounder).
    let statement = island_statement_goal(oblig, &env, &names)
        .map_err(|error| format!("{error} — REJECTED"))?;
    let statement_digest = clean_cic_statement_digest(&statement.goal)
        .map_err(|error| format!("the island statement has no digest ({error}) — REJECTED"))?;
    // (4) The strict rooted audit of the cited theorem.
    super::clean_cic_kernel::recheck_one_theorem(&env, theorem, &directive.allowed_axioms)?;
    // (5) Bind: the theorem proves exactly the grounded statement.
    let theorem_name = names
        .iter()
        .find(|name| name.to_string() == *theorem)
        .expect("checked above: the island declares the cited theorem");
    let info = env
        .get_const(theorem_name)
        .ok_or_else(|| format!("island theorem `{theorem}` is not in the environment"))?;
    let tc = TypeChecker::with_context(&env, LocalContext::new());
    if !tc.is_def_eq(&info.type_, &statement.goal) {
        return Err(format!(
            "the island theorem `{theorem}` does not state the obligation's formula: its type is \
             not definitionally equal to the grounded statement — REJECTED"
        ));
    }
    Ok(super::IslandTheoremOutcome {
        environment_digest,
        statement_digest,
        island_digest: island.digest,
        cited: statement.cited,
    })
}

#[cfg(test)]
mod tests {
    use super::validator_owned_root;

    /// Drift guard (review of WS1.13): every theorem name a validator-owned
    /// anchor cites — the names that reach `kernel_certified_theorems` — lives
    /// under a root the island may not declare into. A new anchor whose
    /// theorems live elsewhere must extend `VALIDATOR_OWNED_THEOREM_ROOTS`, or
    /// this fails.
    #[test]
    fn every_validator_anchor_theorem_lives_under_an_owned_root() {
        let anchor_theorems = [
            // clean_backend_tv: the equation the validator derives per function.
            super::super::clean_backend_tv::tv_theorem_name("addmul"),
            // trustcg_lowering_resolution.
            trust_ir::proof::satres::SATRES_CERT_UNSAT_THEOREM.to_string(),
            // nn_verify_farkas_constructive, rust_giveback_*, crownproof_slackcertz
            // (the names their directives cite in this crate's own tests).
            "NNVerify.farkas_combine_2_le_bound".to_string(),
            "RustSem.GiveBack.backId_roundTrips".to_string(),
            "Crownproof.SlackCertZ.checkSlackEntailmentZ_sound".to_string(),
        ];
        for name in &anchor_theorems {
            assert!(
                validator_owned_root(name).is_some(),
                "`{name}` is a validator anchor's theorem outside every owned root"
            );
        }
        // The rule is the ROOT component, byte-exact — never a substring or a
        // case-folded match, so user namespaces that merely resemble one stay
        // admitted.
        for user in [
            "Lib.fst3_eq",
            "CleanTVX.f.denotes",
            "cleanTV.f.denotes",
            "Clean.Island",
            "Lib.CleanTV.f",
            "NNVerifyLib.bound",
        ] {
            assert!(
                validator_owned_root(user).is_none(),
                "`{user}` is not under a validator-owned root"
            );
        }
        assert_eq!(validator_owned_root("CleanTV"), Some("CleanTV"));
    }
}
