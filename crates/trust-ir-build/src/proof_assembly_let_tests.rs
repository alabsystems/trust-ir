// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Defining proof LETs retain values and ownership; aliases add no authority.

use super::*;
use crate::scoped_local::{LocalScopeError, LocalScopeLimits};
use crate::term_scope::{TermScopeError, TermScopeLimits};
use clean_kernel::BinderInfo;
use std::sync::Arc;

fn reflexive(logic: &mut ProofAssembly, n: u64) -> ScopedProofCandidate {
    logic
        .candidate(eq(c("Nat"), nat(n), nat(n)), refl(c("Nat"), nat(n)))
        .unwrap()
}

#[test]
fn let_facts_preserve_dependent_propositions_and_reuse_aliases_under_binders() {
    let mut scope = LocalScope::new();
    let mut logic = ProofAssembly::new(ProofLimits::default()).unwrap();
    let a = scope.try_local(Expr::type_()).unwrap();
    let x = scope.try_local(a.term().clone()).unwrap();
    let p = eq(a.term().clone(), x.term().clone(), x.term().clone());
    let fact = logic
        .candidate(p.clone(), refl(a.term().clone(), x.term().clone()))
        .unwrap();
    let function = logic
        .candidate(
            Expr::pi(
                BinderInfo::Default,
                c("Nat"),
                eq(c("Nat"), Expr::bvar(0), Expr::bvar(0)),
            ),
            Expr::lam(BinderInfo::Default, c("Nat"), refl(c("Nat"), Expr::bvar(0))),
        )
        .unwrap();
    let goal = Expr::pi(
        BinderInfo::Default,
        c("Nat"),
        Expr::pi(
            BinderInfo::Default,
            c("Nat"),
            app(
                "And",
                [p.clone(), eq(c("Nat"), Expr::bvar(1), Expr::bvar(1))],
            ),
        ),
    );
    let mut escaped = Vec::new();
    let result = logic
        .with_let_facts(
            &mut scope,
            &[fact.clone(), function.clone()],
            goal.clone(),
            |logic, scope, aliases| {
                assert_eq!(aliases[0].proposition(), fact.proposition());
                assert_eq!(aliases[1].proposition(), function.proposition());
                assert!(
                    aliases
                        .iter()
                        .all(|alias| matches!(alias.term().kind(), ExprKind::FVar(_)))
                );
                escaped = aliases.clone();
                logic.introduce_forall(scope, goal.clone(), |logic, scope, n, inner_goal| {
                    logic.introduce_forall(scope, inner_goal, |logic, _, _, instance| {
                        let applied = logic.apply(&aliases[1], n.term().clone())?;
                        logic.candidate(
                            instance,
                            app(
                                "And.intro",
                                [
                                    p.clone(),
                                    applied.proposition().clone(),
                                    aliases[0].term().clone(),
                                    applied.term().clone(),
                                ],
                            ),
                        )
                    })
                })
            },
        )
        .unwrap();
    assert_eq!(result.proposition(), &goal);
    for alias in escaped {
        assert!(logic.check_live(&alias).is_err());
    }
    logic.check_live(&fact).unwrap();
    logic.check_live(&result).unwrap();
    let parameters = [a, x];
    checked(
        &environment(),
        &scope
            .close(&lams(&parameters, result.term().clone()))
            .unwrap(),
        &scope.close(&forall(&parameters, goal)).unwrap(),
    );
}

#[test]
fn defining_let_order_and_values_are_required_even_if_unused() {
    let mut scope = LocalScope::new();
    let mut logic = ProofAssembly::new(ProofLimits::default()).unwrap();
    let first = reflexive(&mut logic, 0);
    let second = reflexive(&mut logic, 1);
    let mut raw_alias = None;
    let result = logic
        .with_let_facts(
            &mut scope,
            &[first.clone(), second.clone()],
            first.proposition().clone(),
            |_, _, aliases| {
                raw_alias = Some(aliases[0].term().clone());
                Ok(aliases[0].clone())
            },
        )
        .unwrap();
    let closed = scope.close(result.term()).unwrap();
    let ExprKind::Let(_, first_ty, first_value, rest, _) = closed.kind() else {
        panic!("first defining LET missing")
    };
    assert_eq!(first_ty.as_ref(), first.proposition());
    assert_eq!(first_value.as_ref(), first.term());
    let ExprKind::Let(_, second_ty, second_value, body, _) = rest.kind() else {
        panic!("second defining LET missing")
    };
    assert_eq!(second_ty.as_ref(), second.proposition());
    assert_eq!(second_value.as_ref(), second.term());
    assert_eq!(body.as_ref(), &Expr::bvar(1));
    checked(&environment(), &closed, first.proposition());
    assert!(matches!(
        scope.close(&raw_alias.unwrap()).unwrap_err(),
        LocalScopeError::Closure(TermScopeError::OutOfScope(_))
    ));
    assert!(matches!(
        TypeChecker::new(&environment()).check_type(body, first.proposition()),
        Err(KernelTypeError::UnboundVariable(1))
    ));
    let corrupt = Expr::let_named(
        clean_kernel::Name::anon(),
        first_ty.as_ref().clone(),
        c("True.intro"),
        rest.as_ref().clone(),
        false,
    );
    rejected(&environment(), &corrupt, first.proposition());

    let bad = logic
        .candidate(eq(c("Nat"), nat(0), nat(1)), refl(c("Nat"), nat(0)))
        .unwrap();
    let unused = logic
        .with_let_facts(&mut scope, &[bad], c("True"), |logic, _, _| {
            logic.candidate(c("True"), c("True.intro"))
        })
        .unwrap();
    rejected(
        &environment(),
        &scope.close(unused.term()).unwrap(),
        &c("True"),
    );
}

#[test]
fn all_input_handles_are_checked_before_caps_scopes_or_local_allocation() {
    let mut scope = LocalScope::new();
    let mut logic = ProofAssembly::new(ProofLimits {
        captures: 1,
        ..ProofLimits::default()
    })
    .unwrap();
    let own = reflexive(&mut logic, 0);
    let mut foreign = ProofAssembly::new(ProofLimits::default()).unwrap();
    let other = reflexive(&mut foreign, 0);
    let expired = logic.with_scope(|logic| Ok(reflexive(logic, 0))).unwrap();
    for bad in [other, expired] {
        let before = (logic.operations, logic.next_context, scope.allocated());
        let error = logic
            .with_let_facts(
                &mut scope,
                &[own.clone(), bad],
                own.proposition().clone(),
                |_, _, _| panic!("invalid inputs reached continuation"),
            )
            .err()
            .unwrap();
        assert_eq!(error, "foreign or expired proof assembly handle");
        assert_eq!(
            (logic.operations, logic.next_context, scope.allocated()),
            before
        );
    }
    let before = (logic.operations, logic.next_context, scope.allocated());
    assert_eq!(
        logic
            .with_let_facts(
                &mut scope,
                &[own.clone(), own.clone()],
                own.proposition().clone(),
                |_, _, _| panic!("oversize reached continuation")
            )
            .err()
            .unwrap(),
        "proof let binding limit"
    );
    assert_eq!(
        (logic.operations, logic.next_context, scope.allocated()),
        before
    );
}

#[test]
fn callback_result_must_be_live_and_have_the_exact_goal() {
    let mut scope = LocalScope::new();
    let mut logic = ProofAssembly::new(ProofLimits::default()).unwrap();
    let fact = reflexive(&mut logic, 0);
    let mut foreign = ProofAssembly::new(ProofLimits::default()).unwrap();
    let other = reflexive(&mut foreign, 0);
    let expired = logic.with_scope(|logic| Ok(reflexive(logic, 0))).unwrap();
    for wrong in [other, expired] {
        assert_eq!(
            logic
                .with_let_facts(
                    &mut scope,
                    std::slice::from_ref(&fact),
                    fact.proposition().clone(),
                    |_, _, _| Ok(wrong)
                )
                .err()
                .unwrap(),
            "foreign or expired proof assembly handle"
        );
        assert!(logic.in_root_context());
    }
    let wrong = logic
        .with_let_facts(
            &mut scope,
            std::slice::from_ref(&fact),
            fact.proposition().clone(),
            |logic, _, _| logic.candidate(c("True"), c("True.intro")),
        )
        .err()
        .unwrap();
    assert_eq!(wrong, "let continuation changed the goal");
    assert!(logic.in_root_context());
    let mut captured = None;
    let outer = logic
        .with_let_facts(
            &mut scope,
            std::slice::from_ref(&fact),
            fact.proposition().clone(),
            |_, _, aliases| {
                captured = Some(aliases[0].clone());
                Ok(fact.clone())
            },
        )
        .unwrap();
    let alias = captured.unwrap();
    assert!(logic.check_live(&alias).is_err());
    logic
        .with_scope(|logic| {
            assert!(logic.check_live(&alias).is_err());
            logic.check_live(&outer)
        })
        .unwrap();
    checked(
        &environment(),
        &scope.close(outer.term()).unwrap(),
        outer.proposition(),
    );
}

#[test]
fn continuation_error_and_panic_expire_aliases_without_refunding_work() {
    let mut scope = LocalScope::new();
    let mut logic = ProofAssembly::new(ProofLimits::default()).unwrap();
    let fact = reflexive(&mut logic, 0);
    let mut captured = None;
    let before = (logic.operations, logic.next_context, scope.allocated());
    let error = logic
        .with_let_facts(
            &mut scope,
            std::slice::from_ref(&fact),
            fact.proposition().clone(),
            |_, _, aliases| {
                captured = Some(aliases[0].clone());
                Err("deliberate LET continuation error".into())
            },
        )
        .err()
        .unwrap();
    assert_eq!(error, "deliberate LET continuation error");
    assert_eq!(
        (logic.operations, logic.next_context, scope.allocated()),
        (before.0 + 2, before.1 + 1, before.2 + 1)
    );
    assert!(logic.in_root_context() && logic.check_live(&captured.take().unwrap()).is_err());
    let before = (logic.operations, logic.next_context, scope.allocated());
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = logic.with_let_facts(
            &mut scope,
            std::slice::from_ref(&fact),
            fact.proposition().clone(),
            |_, _, aliases| {
                captured = Some(aliases[0].clone());
                panic!("deliberate LET continuation panic")
            },
        );
    }))
    .unwrap_err();
    assert_eq!(
        panic.downcast_ref::<&str>(),
        Some(&"deliberate LET continuation panic")
    );
    assert_eq!(
        (logic.operations, logic.next_context, scope.allocated()),
        (before.0 + 2, before.1 + 1, before.2 + 1)
    );
    assert!(logic.in_root_context() && logic.check_live(&captured.unwrap()).is_err());
    logic.check_live(&fact).unwrap();
}

#[test]
fn empty_nonempty_and_partial_failures_obey_existing_limits_and_costs() {
    let mut scope = LocalScope::with_limits(LocalScopeLimits {
        max_locals: 0,
        ..LocalScopeLimits::default()
    });
    let mut logic = ProofAssembly::new(ProofLimits {
        operations: 3,
        ..ProofLimits::default()
    })
    .unwrap();
    let fact = reflexive(&mut logic, 0);
    let result = logic
        .with_let_facts(
            &mut scope,
            &[],
            fact.proposition().clone(),
            |_, _, aliases| {
                assert!(aliases.is_empty());
                Ok(fact.clone())
            },
        )
        .unwrap();
    assert_eq!(logic.operations, 3);
    assert_eq!(scope.allocated(), 0);
    checked(&environment(), result.term(), result.proposition());
    for operations in [3, 4] {
        let mut scope = LocalScope::new();
        let mut logic = ProofAssembly::new(ProofLimits {
            operations,
            ..ProofLimits::default()
        })
        .unwrap();
        let fact = reflexive(&mut logic, 0);
        let result = logic.with_let_facts(
            &mut scope,
            std::slice::from_ref(&fact),
            fact.proposition().clone(),
            |_, _, aliases| Ok(aliases[0].clone()),
        );
        assert_eq!(result.is_ok(), operations == 4);
        assert_eq!(logic.operations, 4);
        assert_eq!(scope.allocated(), 1);
        assert!(logic.in_root_context());
    }
    for cap in [0, 1] {
        let mut scope = LocalScope::with_limits(LocalScopeLimits {
            max_locals: cap,
            ..LocalScopeLimits::default()
        });
        let mut logic = ProofAssembly::new(ProofLimits::default()).unwrap();
        let fact = reflexive(&mut logic, 0);
        let error = logic
            .with_let_facts(
                &mut scope,
                &[fact.clone(), fact.clone()],
                fact.proposition().clone(),
                |_, _, _| panic!("local cap bypassed"),
            )
            .err()
            .unwrap();
        assert_eq!(
            error,
            format!("named local allocation limit {cap} exceeded")
        );
        assert_eq!(scope.allocated(), cap);
        assert_eq!(logic.operations, 2 + cap);
        assert!(logic.in_root_context());
    }
    let mut scope = LocalScope::new();
    let mut logic = ProofAssembly::new(ProofLimits {
        contexts: 1,
        ..ProofLimits::default()
    })
    .unwrap();
    let fact = reflexive(&mut logic, 0);
    assert_eq!(
        logic
            .with_let_facts(
                &mut scope,
                &[],
                fact.proposition().clone(),
                |_, _, _| panic!("context cap bypassed")
            )
            .err()
            .unwrap(),
        "proof assembly context limit"
    );
    assert_eq!(
        (logic.operations, logic.next_context, scope.allocated()),
        (2, 1, 0)
    );
    for limits in [
        ProofLimits {
            operations: 0,
            ..ProofLimits::default()
        },
        ProofLimits {
            contexts: 0,
            ..ProofLimits::default()
        },
        ProofLimits {
            captures: 0,
            ..ProofLimits::default()
        },
    ] {
        assert!(ProofAssembly::new(limits).is_err());
    }
}

#[test]
#[cfg(feature = "clean-tv-anchor")]
fn original_execution_assembler_keeps_cumulative_operation_and_local_charges() {
    use crate::core_execution::{Assembler, Limits};
    for (max_operations, max_locals, expected) in [
        (2, 8, "execution construction operation budget exceeded"),
        (8, 2, "execution construction local budget exceeded"),
    ] {
        let mut scope = LocalScope::new();
        let mut assembler = Assembler::new(
            &mut scope,
            Limits {
                max_operations,
                max_locals,
                max_list_items: 16,
                max_lookup_candidates: 16,
                lookup_heartbeats: 1000,
                lookup_cache_entries: 16,
            },
        )
        .unwrap();
        assembler.local(c("Nat")).unwrap();
        let mut logic = ProofAssembly::new(ProofLimits::default()).unwrap();
        let fact = reflexive(&mut logic, 0);
        let mut same_allocator_seen = false;
        let proof = logic
            .with_let_facts(
                &mut assembler,
                std::slice::from_ref(&fact),
                fact.proposition().clone(),
                |_, allocator, aliases| {
                    assert_eq!(allocator.local_scope().allocated(), 2);
                    same_allocator_seen = true;
                    Ok(aliases[0].clone())
                },
            )
            .unwrap();
        assert!(same_allocator_seen);
        checked(
            &environment(),
            &assembler.local_scope().close(proof.term()).unwrap(),
            proof.proposition(),
        );
        assert_eq!(
            logic
                .with_let_facts(
                    &mut assembler,
                    std::slice::from_ref(&fact),
                    fact.proposition().clone(),
                    |_, _, _| panic!("assembler budget reset")
                )
                .err()
                .unwrap(),
            expected
        );
        assert_eq!(assembler.local_scope().allocated(), 2);
        assert!(logic.in_root_context());
    }
}

fn repeated_under_binders(depth: usize, proposition: &Expr, proof: &Expr) -> (Expr, Expr) {
    let mut goal = proposition.clone();
    let mut term = proof.clone();
    for _ in 0..depth {
        term = Expr::lam(
            BinderInfo::Default,
            c("Nat"),
            app(
                "And.intro",
                [proposition.clone(), goal.clone(), proof.clone(), term],
            ),
        );
        goal = Expr::pi(
            BinderInfo::Default,
            c("Nat"),
            app("And", [proposition.clone(), goal]),
        );
    }
    (goal, term)
}

#[test]
fn defining_value_is_shared_once_and_closure_work_drops_for_repeated_open_proofs() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(Expr::type_()).unwrap();
    let x = scope.try_local(a.term().clone()).unwrap();
    let proposition = eq(a.term().clone(), x.term().clone(), x.term().clone());
    let mut value = refl(a.term().clone(), x.term().clone());
    for _ in 0..12 {
        value = app(
            "And.left",
            [
                proposition.clone(),
                c("True"),
                app(
                    "And.intro",
                    [proposition.clone(), c("True"), value, c("True.intro")],
                ),
            ],
        );
    }
    let (goal, inline) = repeated_under_binders(8, &proposition, &value);
    let mut logic = ProofAssembly::new(ProofLimits::default()).unwrap();
    let fact = logic.candidate(proposition.clone(), value.clone()).unwrap();
    let result = logic
        .with_let_facts(&mut scope, &[fact], goal.clone(), |logic, _, aliases| {
            let (same_goal, proof) = repeated_under_binders(8, &proposition, aliases[0].term());
            assert_eq!(same_goal, goal);
            logic.candidate(same_goal, proof)
        })
        .unwrap();
    let ExprKind::Let(_, _, defining, _, _) = result.term().kind() else {
        panic!("missing defining value")
    };
    let (ExprKind::App(old_fn, old_arg), ExprKind::App(new_fn, new_arg)) =
        (value.kind(), defining.kind())
    else {
        panic!("proof application")
    };
    assert!(Arc::ptr_eq(old_fn, new_fn) && Arc::ptr_eq(old_arg, new_arg));
    let captures = [a, x];
    let shared = scope
        .close_with_limits(
            &lams(&captures, result.term().clone()),
            TermScopeLimits::default(),
        )
        .unwrap();
    let inline = scope
        .close_with_limits(&lams(&captures, inline), TermScopeLimits::default())
        .unwrap();
    assert!(
        shared.stats.visits < inline.stats.visits,
        "one defining value should reduce this fixture's closure work: shared={:?}, inline={:?}",
        shared.stats,
        inline.stats
    );
    let claim = scope.close(&forall(&captures, goal)).unwrap();
    checked(&environment(), &shared.term, &claim);
    checked(&environment(), &inline.term, &claim);
}
