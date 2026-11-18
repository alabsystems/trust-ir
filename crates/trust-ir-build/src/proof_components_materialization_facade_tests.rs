// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Consumer-shaped coverage of the fixed-inventory public facade.
use super::*;
use clean_kernel::{BinderInfo, Environment, ExprKind, Level, TypeChecker};
use std::sync::Arc;

fn nat() -> Expr {
    Expr::const_str("Nat")
}

fn successor_chain(mut term: Expr, count: usize) -> Expr {
    for _ in 0..count {
        term = Expr::app(Expr::const_str("Nat.succ"), term);
    }
    term
}

fn components(scope: &LocalScope, operations: usize) -> ProofComponents {
    let mut parts = ProofComponents::new(
        "materialization.facade",
        ProofLimits {
            operations,
            ..Default::default()
        },
    );
    parts.set_base(scope, vec![]).unwrap();
    parts
}

fn equality(type_: Expr, left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [type_, left, right],
    )
}

fn reflexivity(type_: Expr, value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [type_, value],
    )
}

fn application(function: &Arc<Expr>, argument: Expr) -> Expr {
    Expr::app_arc(function.clone(), Arc::new(argument))
}

fn application_parts(term: &Expr) -> (&Arc<Expr>, &Arc<Expr>) {
    let ExprKind::App(function, argument) = term.kind() else {
        panic!("expected the complete canonical-function application");
    };
    (function, argument)
}

#[test]
fn facade_reuses_inner_canonical_graph_after_reverse_data_substitution_and_rebuilt_endpoints() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(nat()).unwrap();
    let y = scope.try_local(nat()).unwrap();
    let mut parts = components(&scope, 100_000);
    parts
        .extend_base(OwnedProofCapture::Parameter(x.clone()))
        .unwrap();
    parts
        .extend_base(OwnedProofCapture::Parameter(y.clone()))
        .unwrap();
    let first = parts
        .bind_scoped_owned(&mut scope, &[], nat(), y.term().clone())
        .unwrap();
    let second = parts
        .bind_scoped_owned(&mut scope, &[], nat(), first.reference.clone())
        .unwrap();
    let canonical = Arc::new(Expr::lam(
        BinderInfo::Default,
        nat(),
        successor_chain(Expr::bvar(0), 128),
    ));
    let original_goal = equality(
        nat(),
        application(&canonical, second.reference.clone()),
        application(&canonical, y.term().clone()),
    );
    let external = [x, y.clone(), first.local.clone(), second.local.clone()];
    let context = parts
        .prepare_scoped_materialization_context(&scope, &external)
        .unwrap();
    // The first consumer forest keeps both exact data types/values and the
    // original goal, rather than supplying a pre-approved output receipt.
    let forest = parts
        .materialize_scoped_terms_in_context(
            &scope,
            &context,
            &[
                first.local.ty().clone(),
                y.term().clone(),
                second.local.ty().clone(),
                first.reference.clone(),
                original_goal,
            ],
        )
        .unwrap();
    assert_eq!(forest.len(), 5);
    let data = [
        (first.local, forest[1].clone()),
        (second.local, forest[3].clone()),
    ];
    let mut expanded = forest[4].clone();
    for (local, original_value) in data.iter().rev() {
        expanded = expanded
            .abstract_fvar(local.id())
            .instantiate(original_value);
    }
    let endpoints = expanded.get_app_args();
    assert_eq!(endpoints.len(), 3);
    let (left_function, left_argument) = application_parts(endpoints[1]);
    let (right_function, right_argument) = application_parts(endpoints[2]);
    assert!(Arc::ptr_eq(left_function, &canonical));
    assert!(Arc::ptr_eq(right_function, &canonical));
    assert_eq!(left_argument.as_ref(), y.term());
    assert_eq!(right_argument.as_ref(), y.term());
    // These Eq and App nodes are rebuilt after actual ordinary substitutions.
    // Only the exact unchanged inner canonical function graph is retained.
    let rebuilt = equality(
        nat(),
        application(left_function, left_argument.as_ref().clone()),
        application(right_function, right_argument.as_ref().clone()),
    );
    assert_eq!(rebuilt, expanded);
    let before = parts.counts().3;
    let warm = parts
        .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&rebuilt))
        .unwrap();
    let warm_work = parts.counts().3 - before;
    // A newly prepared context carries no completed facts from the old token.
    // Its construction is paid separately from the compared forest walks.
    let fresh = parts
        .prepare_scoped_materialization_context(&scope, &external)
        .unwrap();
    let before = parts.counts().3;
    let cold = parts
        .materialize_scoped_terms_in_context(&scope, &fresh, std::slice::from_ref(&rebuilt))
        .unwrap();
    let cold_work = parts.counts().3 - before;
    assert_eq!(warm, vec![rebuilt.clone()]);
    assert_eq!(cold, warm);
    assert!(warm_work > 0, "reuse and its guards still spend work");
    assert!(
        warm_work < cold_work,
        "rebuilt endpoints must reuse the exact large inner canonical graph: warm={warm_work}, fresh={cold_work}"
    );
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    let claim = scope
        .close(
            &external[..2]
                .iter()
                .rev()
                .fold(rebuilt.clone(), |g, p| p.pi(g)),
        )
        .unwrap();
    let proof = reflexivity(nat(), application(&canonical, y.term().clone()));
    let proof = external[..2].iter().rev().fold(proof, |h, p| p.lam(h));
    let bundle = parts
        .close_scoped(
            &scope,
            proof,
            rebuilt,
            crate::term_scope::TermScopeLimits::default(),
        )
        .unwrap();
    let wire = bundle.encode_with_claim(&claim).unwrap();
    let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&wire).unwrap();
    assert_eq!(transported, claim);
    assert_eq!(decoded.declarations.len(), 4, "both original values remain");
    decoded.replay(&env, &transported, 2_000_000).unwrap();
}

#[test]
fn facade_does_not_accept_a_raw_named_structural_lookalike_of_a_warm_ordinary_graph() {
    let mut scope = LocalScope::new();
    let external = scope.try_local(nat()).unwrap();
    let ordinary = successor_chain(
        Expr::let_named(
            Name::from_string("same"),
            nat(),
            Expr::nat_lit(0),
            Expr::nat_lit(0),
            false,
        ),
        40,
    );
    let mut parts = components(&scope, 100_000);
    let context = parts
        .prepare_scoped_materialization_context(&scope, std::slice::from_ref(&external))
        .unwrap();
    let before = parts.counts().3;
    assert_eq!(
        parts
            .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&ordinary))
            .unwrap(),
        vec![ordinary.clone()]
    );
    let cold_work = parts.counts().3 - before;
    // Register a fresh deferred body only after ordinary facts were published.
    // This does not revoke facts about their original exact source graph.
    let raw_named = successor_chain(
        external.let_named(
            Name::from_string("same"),
            Expr::nat_lit(0),
            Expr::nat_lit(0),
            false,
        ),
        40,
    );
    assert_eq!(ordinary, raw_named, "ordinary syntax is a lookalike");
    assert!(!raw_named.has_fvar_quick(), "the named binder is unused");
    let before = parts.counts().3;
    assert_eq!(
        parts
            .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&ordinary))
            .unwrap(),
        vec![ordinary.clone()]
    );
    assert!(parts.counts().3 - before < cold_work);
    let before = parts.counts().3;
    assert_eq!(
        parts
            .materialize_scoped_terms_in_context(&scope, &context, &[raw_named])
            .unwrap_err(),
        crate::term_scope::TermScopeError::ShadowedLocal(external.id()).to_string()
    );
    assert!(parts.counts().3 > before);
    assert!(
        parts
            .materialize_scoped_terms_in_context(&scope, &context, &[ordinary])
            .is_err(),
        "the same token cannot hide its enclosing failed attempt"
    );
}

#[test]
fn facade_context_cannot_transfer_component_scope_or_other_inventory_admission() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(nat()).unwrap();
    let y = scope.try_local(nat()).unwrap();
    let mut owner = components(&scope, 100_000);
    let context = owner
        .prepare_scoped_materialization_context(&scope, std::slice::from_ref(&x))
        .unwrap();
    let root = successor_chain(x.term().clone(), 40);
    owner
        .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&root))
        .unwrap();
    let mut peer = components(&scope, 100_000);
    assert!(
        peer.materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&root))
            .unwrap_err()
            .contains("another component or scope owner")
    );
    let peer_context = peer
        .prepare_scoped_materialization_context(&scope, std::slice::from_ref(&x))
        .unwrap();
    assert!(
        owner
            .materialize_scoped_terms_in_context(&scope, &peer_context, std::slice::from_ref(&root))
            .is_err()
    );
    let mut foreign = LocalScope::new();
    let same_id = foreign.try_local(nat()).unwrap();
    assert_eq!(same_id.id(), x.id());
    assert!(
        owner
            .materialize_scoped_terms_in_context(&foreign, &context, std::slice::from_ref(&root))
            .unwrap_err()
            .contains("another component or scope owner")
    );
    assert!(
        owner
            .prepare_scoped_materialization_context(&scope, &[same_id])
            .is_err()
    );
    assert!(
        owner
            .prepare_scoped_materialization_context(&scope, &[x.clone(), x.clone()])
            .is_err()
    );
    assert_eq!(
        owner
            .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&root))
            .unwrap(),
        vec![root],
        "foreign attempts must not poison the actual owner's valid token"
    );
    let wide = owner
        .prepare_scoped_materialization_context(&scope, &[x, y.clone()])
        .unwrap();
    let y_root = successor_chain(y.term().clone(), 40);
    owner
        .materialize_scoped_terms_in_context(&scope, &wide, std::slice::from_ref(&y_root))
        .unwrap();
    assert_eq!(
        owner
            .materialize_scoped_terms_in_context(&scope, &context, &[y_root])
            .unwrap_err(),
        crate::term_scope::TermScopeError::OutOfScope(y.id()).to_string(),
        "another token's wider inventory cannot authorize this missing input"
    );
}

#[test]
fn facade_inherits_sibling_prefix_generation_refusals_without_public_token_mutation() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(nat()).unwrap();
    let b = scope.try_local(nat()).unwrap();
    let c = scope.try_local(nat()).unwrap();
    let mut parts = components(&scope, 100_000);
    let mut context = parts
        .prepare_scoped_materialization_context(&scope, std::slice::from_ref(&a))
        .unwrap();
    let ancestor = successor_chain(a.term().clone(), 40);
    parts
        .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&ancestor))
        .unwrap();
    // Only this private test child can exercise the underlying mutation API.
    // Equal-length sibling inventories must never inherit each other's facts.
    let mark = context.context.checkpoint();
    parts
        .charged_extend_external_context(&scope, &mut context.context, std::slice::from_ref(&b))
        .unwrap();
    let sibling = successor_chain(b.term().clone(), 40);
    parts
        .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&sibling))
        .unwrap();
    let paid = parts.counts().3;
    context.context.restore(mark).unwrap();
    assert_eq!(parts.counts().3, paid, "restoration never refunds work");
    parts
        .charged_extend_external_context(&scope, &mut context.context, &[c])
        .unwrap();
    assert_eq!(
        parts
            .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&ancestor))
            .unwrap(),
        vec![ancestor]
    );
    assert_eq!(
        parts
            .materialize_scoped_terms_in_context(&scope, &context, &[sibling])
            .unwrap_err(),
        crate::term_scope::TermScopeError::OutOfScope(b.id()).to_string()
    );
}

#[test]
fn facade_descends_new_valid_and_missing_branches_in_rebuilt_normal_expressions() {
    let mut scope = LocalScope::new();
    let x = scope.try_local(nat()).unwrap();
    let absent = scope.try_local(nat()).unwrap();
    let mut parts = components(&scope, 100_000);
    let context = parts
        .prepare_scoped_materialization_context(&scope, std::slice::from_ref(&x))
        .unwrap();
    let shared = Arc::new(successor_chain(x.term().clone(), 40));
    let combine = |right| {
        Expr::app(
            Expr::app_arc(Arc::new(Expr::const_str("Nat.add")), shared.clone()),
            right,
        )
    };
    let original = combine(Expr::nat_lit(0));
    parts
        .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&original))
        .unwrap();
    let before = parts.counts().3;
    parts
        .materialize_scoped_terms_in_context(&scope, &context, &[original])
        .unwrap();
    let hit_work = parts.counts().3 - before;
    let changed = combine(successor_chain(Expr::nat_lit(1), 40));
    let before = parts.counts().3;
    assert_eq!(
        parts
            .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&changed))
            .unwrap(),
        vec![changed]
    );
    assert!(parts.counts().3 - before > hit_work);
    // A normal kernel reduction could erase the unused let value. Complete
    // materialization must inspect it before any such reduction is considered.
    let changed = combine(Expr::let_named(
        Name::from_string("unused"),
        nat(),
        absent.term().clone(),
        Expr::nat_lit(0),
        false,
    ));
    assert_eq!(
        parts
            .materialize_scoped_terms_in_context(&scope, &context, &[changed])
            .unwrap_err(),
        crate::term_scope::TermScopeError::OutOfScope(absent.id()).to_string()
    );
}

#[test]
fn facade_keeps_complete_depth_and_sticky_failed_attempt_work_under_the_owner_cap() {
    let scope = LocalScope::with_limits(crate::scoped_local::LocalScopeLimits {
        closing: crate::term_scope::TermScopeLimits {
            max_visits: 10_000,
            max_depth: 12,
        },
        ..Default::default()
    });
    let mut parts = components(&scope, 100_000);
    let context = parts
        .prepare_scoped_materialization_context(&scope, &[])
        .unwrap();
    let known = successor_chain(Expr::nat_lit(0), 8);
    parts
        .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&known))
        .unwrap();
    {
        let view = parts
            .external_ordinary_view(&scope, &context.context)
            .unwrap()
            .unwrap();
        assert!(
            view.envelope(&known).is_some(),
            "warm an actual complete fact"
        );
    }
    let before = parts.counts().3;
    assert!(
        parts
            .materialize_scoped_terms_in_context(
                &scope,
                &context,
                &[successor_chain(known.clone(), 4)]
            )
            .unwrap_err()
            .contains("depth limit")
    );
    let failed_work = parts.counts().3;
    assert!(failed_work > before && failed_work <= 100_000);
    assert!(
        parts
            .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&known))
            .is_err(),
        "an earlier valid graph cannot reset the failed token"
    );
    assert!(parts.counts().3 > failed_work);
    let paid = parts.counts().3;
    let fresh = parts
        .prepare_scoped_materialization_context(&scope, &[])
        .unwrap();
    assert!(parts.counts().3 > paid, "new preparation is charged");
    assert_eq!(
        parts
            .materialize_scoped_terms_in_context(&scope, &fresh, std::slice::from_ref(&known))
            .unwrap(),
        vec![known]
    );
}

#[test]
fn facade_preserves_ambient_bvars_without_publishing_them_as_closed_reusable_results() {
    let mut scope = LocalScope::new();
    let mut parts = components(&scope, 100_000);
    let context = parts
        .prepare_scoped_materialization_context(&scope, &[])
        .unwrap();
    let ambient = successor_chain(Expr::bvar(0), 40);
    assert!(ambient.has_loose_bvars());
    assert_eq!(
        parts
            .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&ambient))
            .unwrap(),
        vec![ambient.clone()],
        "the existing ambient ordinary binder context is preserved"
    );
    let ordinary = Expr::lam(BinderInfo::Default, nat(), ambient.clone());
    parts
        .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&ordinary))
        .unwrap();
    {
        let view = parts
            .external_ordinary_view(&scope, &context.context)
            .unwrap()
            .unwrap();
        assert!(view.envelope(&ordinary).is_some());
        assert!(view.envelope(&ambient).is_none());
    }
    let binder = scope.try_local(nat()).unwrap();
    let raw_named = binder.lam(ambient.clone());
    let expected = Expr::lam(
        BinderInfo::Default,
        nat(),
        successor_chain(Expr::bvar(1), 40),
    );
    let actual = parts
        .materialize_scoped_terms_in_context(&scope, &context, &[raw_named])
        .unwrap();
    assert_eq!(
        actual,
        vec![expected],
        "a named binder must shift, never capture, the ambient BVar"
    );
    let actual = actual.into_iter().next().unwrap();
    assert!(actual.has_loose_bvars());
    assert_eq!(
        parts
            .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&ambient))
            .unwrap(),
        vec![ambient.clone()]
    );
    let view = parts
        .external_ordinary_view(&scope, &context.context)
        .unwrap()
        .unwrap();
    assert!(view.envelope(&ambient).is_none());
    assert!(view.envelope(&actual).is_none());
}

#[test]
fn facade_inventory_and_aggregate_work_bounds_cannot_be_replaced_by_a_fresh_allowance() {
    let mut scope = LocalScope::new();
    let input = scope.try_local(nat()).unwrap();
    let mut no_inventory = ProofComponents::new(
        "materialization.facade.inventory",
        ProofLimits {
            operations: 100,
            contexts: 0,
            captures: 0,
        },
    );
    no_inventory.set_base(&scope, vec![]).unwrap();
    assert!(
        no_inventory
            .prepare_scoped_materialization_context(&scope, &[input])
            .err()
            .expect("inventory cap must refuse")
            .contains("inventory limit")
    );
    let mut charged_failure = false;
    for cap in [0, 1, 5, 6, 8, 16, 48] {
        let mut parts = components(&scope, cap);
        let context = match parts.prepare_scoped_materialization_context(&scope, &[]) {
            Ok(context) => context,
            Err(_) => {
                assert!(parts.counts().3 <= cap);
                continue;
            }
        };
        let before = parts.counts().3;
        assert!(
            parts
                .materialize_scoped_terms_in_context(
                    &scope,
                    &context,
                    &[successor_chain(Expr::nat_lit(0), 128)]
                )
                .is_err()
        );
        // Two units pay root setup; require work from the failed walk too.
        charged_failure |= parts.counts().3 - before > 2;
        let failed_work = parts.counts().3;
        assert!(failed_work >= before && failed_work <= cap);
        assert!(
            parts
                .materialize_scoped_terms_in_context(&scope, &context, &[Expr::nat_lit(0)])
                .is_err()
        );
        assert!(parts.counts().3 >= failed_work && parts.counts().3 <= cap);
        if parts.context_work_remaining().unwrap() < 6 {
            assert!(
                parts
                    .prepare_scoped_materialization_context(&scope, &[])
                    .is_err(),
                "another token has no independent work allowance"
            );
        }
    }
    assert!(
        charged_failure,
        "failed complete walks must spend more than root setup"
    );

    // Use the ordinary capture API to retain dependency words before preparing
    // the facade. Empty components would exercise only its visit counter.
    fn captured_parts(cap: usize) -> (LocalScope, ProofComponents) {
        let mut scope = LocalScope::new();
        let a = scope.try_local(nat()).unwrap();
        let b = scope.try_local(nat()).unwrap();
        let mut parts = components(&scope, cap);
        let _ = parts
            .bind_scoped(
                &mut scope,
                &[
                    OwnedProofCapture::Parameter(a.clone()),
                    OwnedProofCapture::Parameter(b.clone()),
                ],
                nat(),
                Expr::apps(
                    Expr::const_str("Nat.add"),
                    [a.term().clone(), b.term().clone()],
                ),
            )
            .unwrap();
        let (visits, words) = parts.context_work_totals();
        assert!(visits > 0 && words > 0);
        assert_eq!(parts.counts().3, visits + words);
        (scope, parts)
    }

    // Measure a genuinely warmed ordinary graph, then reconstruct the same
    // workload with exactly enough combined room for its paid lookup, or one
    // unit less. No private counter or limit is overwritten to arrange a hit.
    let known = successor_chain(Expr::nat_lit(0), 16);
    let (scope, mut measured) = captured_parts(100_000);
    let context = measured
        .prepare_scoped_materialization_context(&scope, &[])
        .unwrap();
    measured
        .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&known))
        .unwrap();
    let warmed_work = measured.counts().3;
    {
        let view = measured
            .external_ordinary_view(&scope, &context.context)
            .unwrap()
            .unwrap();
        assert!(view.envelope(&known).is_some());
    }
    measured
        .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&known))
        .unwrap();
    let lookup_work = measured.counts().3 - warmed_work;
    assert!(lookup_work > 2, "the graph lookup pays beyond root setup");
    for (allowance, should_succeed) in [(lookup_work - 1, false), (lookup_work, true)] {
        let cap = warmed_work.checked_add(allowance).unwrap();
        let (scope, mut parts) = captured_parts(cap);
        let context = parts
            .prepare_scoped_materialization_context(&scope, &[])
            .unwrap();
        parts
            .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&known))
            .unwrap();
        assert_eq!(parts.counts().3, warmed_work);
        let (visits_before, words_before) = parts.context_work_totals();
        assert!(visits_before > 0 && words_before > 0);
        let result = parts.materialize_scoped_terms_in_context(
            &scope,
            &context,
            std::slice::from_ref(&known),
        );
        if should_succeed {
            assert_eq!(result.unwrap(), vec![known.clone()]);
        } else {
            assert!(result.unwrap_err().contains("visit limit"));
        }
        let (visits_after, words_after) = parts.context_work_totals();
        assert!(
            visits_after - visits_before > 2,
            "the probe or refusal is charged"
        );
        assert_eq!(words_after, words_before, "retained work is never reset");
        assert_eq!(parts.counts().3, visits_after + words_after);
        assert_eq!(
            parts.counts().3,
            cap,
            "visits and words exhaust the same cap"
        );
        assert!(
            parts
                .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&known))
                .is_err()
        );
        assert!(
            parts
                .prepare_scoped_materialization_context(&scope, &[])
                .is_err()
        );
        assert_eq!(
            parts.counts().3,
            cap,
            "a retry or new token cannot reset work"
        );
        assert_eq!(parts.context_work_totals().1, words_before);
    }
}

#[test]
fn facade_candidates_still_require_complete_decoded_replay_of_unused_definitions() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    env.init_true_false().unwrap();
    for invalid in [false, true] {
        let mut scope = LocalScope::new();
        let input = scope.try_local(nat()).unwrap();
        let mut parts = components(&scope, 100_000);
        parts
            .extend_base(OwnedProofCapture::Parameter(input.clone()))
            .unwrap();
        let original_value = if invalid {
            Expr::const_str("True.intro")
        } else {
            Expr::nat_lit(7)
        };
        let unused = parts
            .bind_scoped_owned(&mut scope, &[], nat(), original_value.clone())
            .unwrap();
        let context = parts
            .prepare_scoped_materialization_context(&scope, std::slice::from_ref(&input))
            .unwrap();
        let value = successor_chain(input.term().clone(), 40);
        let goal = equality(nat(), value.clone(), value.clone());
        let first = parts
            .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&goal))
            .unwrap();
        assert_eq!(
            parts
                .materialize_scoped_terms_in_context(&scope, &context, std::slice::from_ref(&goal))
                .unwrap(),
            first,
            "materialization does not typecheck an unrelated retained value"
        );
        let proof = reflexivity(nat(), value);
        let claim = scope.close(&input.pi(goal.clone())).unwrap();
        let bundle = parts
            .close_scoped(
                &scope,
                input.lam(proof),
                goal,
                crate::term_scope::TermScopeLimits::default(),
            )
            .unwrap();
        let bytes = bundle.encode_with_claim(&claim).unwrap();
        let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
        assert_eq!(transported, claim);
        assert!(
            decoded.declarations.iter().any(|d| {
                d.id == unused.local.id()
                    && d.type_ == nat()
                    && d.value.as_ref() == Some(&original_value)
            }),
            "the exact unused original definition remains in the decoded inventory"
        );
        let replay = decoded.replay(&env, &transported, 2_000_000);
        let closed =
            decoded
                .declarations
                .iter()
                .rev()
                .fold(decoded.root.clone(), |body, declaration| {
                    let body = body.abstract_fvar(declaration.id);
                    if let Some(value) = &declaration.value {
                        Expr::let_named(
                            declaration.name.clone(),
                            declaration.type_.clone(),
                            value.clone(),
                            body,
                            declaration.non_dep,
                        )
                    } else {
                        Expr::lam(declaration.binder, declaration.type_.clone(), body)
                    }
                });
        let mut checker = TypeChecker::new(&env);
        checker.set_allow_unsafe(false);
        checker.set_allow_partial(false);
        checker.set_heartbeat_limit(1_000_000);
        checker.set_max_cache_entries(100_000);
        checker.check_type(&transported, &Expr::prop()).unwrap();
        let checked = checker.check_type(&closed, &transported);
        if invalid {
            let error = replay
                .err()
                .expect("the unused invalid original value must reach replay");
            assert!(error.contains("TypeMismatch"), "{error}");
            assert!(!error.contains("BudgetExhausted") && !error.contains("HeartbeatExceeded"));
            assert!(
                checked.is_err(),
                "the final closed proof retains the invalid let"
            );
            assert!(!checker.heartbeat_spent());
        } else {
            replay.unwrap();
            checked.unwrap();
        }
    }
}
