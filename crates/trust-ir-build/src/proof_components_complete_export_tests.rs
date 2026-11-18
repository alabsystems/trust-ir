// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::proof_assembly::ProofLimits;
use crate::proof_components::{OwnedProofCapture, ProofComponents};
use crate::scoped_local::LocalScope;
use clean_kernel::{Environment, ExprKind, Level, Name, TypeChecker, expr::FVarId};
use std::sync::Arc;

fn c(name: &str) -> Expr {
    Expr::const_str(name)
}

fn environment() -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();
    env
}

fn fixture_with_claim() -> (ScopedProofComponentBundle, Expr) {
    let mut scope = LocalScope::new();
    let alpha = scope.try_local(Expr::type_()).unwrap();
    let x = scope.try_local(alpha.term().clone()).unwrap();
    let alias = scope.try_local(alpha.term().clone()).unwrap();
    let goal = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [alpha.term().clone(), alias.term().clone(), x.term().clone()],
    );
    let proof = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [alpha.term().clone(), x.term().clone()],
    );
    let mut parts = ProofComponents::new("complete.export", ProofLimits::default());
    parts
        .set_base(
            &scope,
            vec![
                OwnedProofCapture::Parameter(alpha.clone()),
                OwnedProofCapture::Parameter(x.clone()),
                OwnedProofCapture::Definition {
                    local: alias.clone(),
                    value: Arc::new(x.term().clone()),
                },
            ],
        )
        .unwrap();
    let _unused = parts
        .bind_scoped_owned(&mut scope, &[], c("Nat"), Expr::nat_lit(7))
        .unwrap();
    let root = alpha.lam(x.lam(alias.let_(x.term().clone(), proof)));
    let frozen = scope
        .close(&alpha.pi(x.pi(alias.let_(x.term().clone(), goal.clone()))))
        .unwrap();
    let bundle = parts
        .close_scoped(&scope, root, goal, TermScopeLimits::default())
        .unwrap();
    (bundle, frozen)
}

fn fixture() -> ScopedProofComponentBundle {
    fixture_with_claim().0
}

#[test]
fn complete_export_retains_mixed_telescope_unused_values_and_dag_transport() {
    let (original, frozen) = fixture_with_claim();
    let alias_name = original.declarations[2].name.clone();
    let unused_name = original.declarations[3].name.clone();
    let exported = original
        .into_closed_terms(TermScopeLimits::default())
        .unwrap();
    assert_eq!(exported.work.declarations, 4);
    assert_eq!(exported.work.construction_visits, 12);
    let ExprKind::Lam(_, _, x) = exported.root.kind() else {
        panic!("missing alpha");
    };
    let ExprKind::Lam(_, _, alias) = x.kind() else {
        panic!("missing x");
    };
    let ExprKind::Let(name, _, _, unused, _) = alias.kind() else {
        panic!("missing alias");
    };
    assert_eq!(name, &alias_name);
    let ExprKind::Let(name, _, value, _, _) = unused.kind() else {
        panic!("unused definition lost");
    };
    assert_eq!(name, &unused_name);
    assert_eq!(value.as_ref(), &Expr::nat_lit(7));
    let env = environment();
    TypeChecker::new(&env)
        .check_type(&exported.root, &frozen)
        .unwrap();
    let wire = trust_ir::proof::encode_clean_expr_dag_v2(&exported.root).unwrap();
    let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&wire).unwrap();
    assert_eq!(decoded, exported.root);
    TypeChecker::new(&env)
        .check_type(&decoded, &frozen)
        .unwrap();
}

#[test]
fn complete_export_does_not_hide_a_bad_unused_original_value_or_type() {
    let env = environment();
    for wrong_type in [false, true] {
        let (mut original, frozen) = fixture_with_claim();
        let unused = original.declarations.last_mut().unwrap();
        if wrong_type {
            unused.type_ = c("True");
        } else {
            unused.value = Some(c("True.intro"));
        }
        // Export is deliberately untrusted syntax construction, not replay.
        let exported = original
            .into_closed_terms(TermScopeLimits::default())
            .unwrap();
        let wire = trust_ir::proof::encode_clean_expr_dag_v2(&exported.root).unwrap();
        let decoded = trust_ir::proof::decode_clean_expr_dag_v2(&wire).unwrap();
        assert!(
            TypeChecker::new(&env)
                .check_type(&decoded, &frozen)
                .is_err()
        );
    }
}

#[test]
fn complete_export_refuses_foreign_forward_duplicate_and_reserved_names() {
    let mut foreign = fixture();
    foreign.declarations.last_mut().unwrap().value = Some(Expr::fvar(FVarId::new(9999)));
    assert!(
        foreign
            .into_closed_terms(TermScopeLimits::default())
            .is_err()
    );
    let mut forward = fixture();
    forward.declarations.swap(1, 2);
    assert!(
        forward
            .into_closed_terms(TermScopeLimits::default())
            .is_err()
    );
    let mut self_reference = fixture();
    let last = self_reference.declarations.last_mut().unwrap();
    last.value = Some(Expr::fvar(last.id));
    assert!(
        self_reference
            .into_closed_terms(TermScopeLimits::default())
            .is_err()
    );
    let mut duplicate = fixture();
    duplicate.declarations[3].id = duplicate.declarations[0].id;
    assert!(
        duplicate
            .into_closed_terms(TermScopeLimits::default())
            .is_err()
    );
    let mut reserved = fixture();
    reserved.declarations[3].id = FVarId::new(1 << 63);
    assert!(
        reserved
            .into_closed_terms(TermScopeLimits::default())
            .is_err()
    );
}

#[test]
fn complete_export_refuses_internal_assumptions_missing_prefix_and_loose_bvars() {
    let mut assumed = fixture();
    assumed.declarations.last_mut().unwrap().value = None;
    assert!(
        assumed
            .into_closed_terms(TermScopeLimits::default())
            .is_err()
    );
    let mut missing = fixture();
    missing.outer_count = missing.declarations.len() + 1;
    assert!(
        missing
            .into_closed_terms(TermScopeLimits::default())
            .is_err()
    );
    let mut loose = fixture();
    loose.root = Expr::bvar(0);
    assert!(loose.into_closed_terms(TermScopeLimits::default()).is_err());
    let mut loose_type = fixture();
    loose_type.declarations.last_mut().unwrap().type_ = Expr::bvar(0);
    assert!(
        loose_type
            .into_closed_terms(TermScopeLimits::default())
            .is_err()
    );
}

#[test]
fn complete_export_charges_one_budget_including_unused_value_closure() {
    let original = fixture();
    let exported = original
        .clone()
        .into_closed_terms(TermScopeLimits::default())
        .unwrap();
    let visits = exported.work.construction_visits + exported.work.closing.visits;
    original
        .clone()
        .into_closed_terms(TermScopeLimits {
            max_visits: visits,
            ..TermScopeLimits::default()
        })
        .unwrap();
    assert!(
        original
            .clone()
            .into_closed_terms(TermScopeLimits {
                max_visits: visits - 1,
                ..TermScopeLimits::default()
            })
            .is_err()
    );
    assert!(
        original
            .clone()
            .into_closed_terms(TermScopeLimits {
                max_depth: 2,
                ..TermScopeLimits::default()
            })
            .is_err()
    );
    let mut forged_work = original;
    forged_work.work.as_mut().unwrap().closing.visits = usize::MAX;
    assert!(
        forged_work
            .into_closed_terms(TermScopeLimits {
                max_visits: 1,
                ..TermScopeLimits::default()
            })
            .is_err()
    );
}
