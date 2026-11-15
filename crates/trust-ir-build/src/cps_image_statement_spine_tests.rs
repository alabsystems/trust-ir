// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;

#[test]
fn cps_image_replay_statement_spines_preserve_exact_argument_order_and_borrowed_graphs() {
    let expected = (0..8).map(Expr::nat_lit).collect::<Vec<_>>();
    let statement = Expr::apps(Expr::const_str("Eq"), expected[..3].iter().cloned());
    let (head, args) = exact_spine::<3>(&statement).unwrap();
    assert_eq!(head, &Expr::const_str("Eq"));
    assert_eq!(args, [&expected[0], &expected[1], &expected[2]]);
    let raw = Expr::apps(Expr::const_str(TO_CPS), expected.iter().cloned());
    let (head, args) = exact_spine::<8>(&raw).unwrap();
    assert_eq!(head, &Expr::const_str(TO_CPS));
    for (actual, original) in args.iter().zip(raw.get_app_args()) {
        assert!(std::ptr::eq(*actual, original));
    }
    assert_eq!(
        args.as_slice(),
        expected.iter().collect::<Vec<_>>().as_slice()
    );
}

#[test]
fn cps_image_replay_statement_spines_refuse_under_and_over_application() {
    for arity in 0..=32 {
        let source = Expr::apps(Expr::const_str("Eq"), (0..arity).map(Expr::nat_lit));
        assert_eq!(exact_spine::<3>(&source).is_some(), arity == 3);
        assert_eq!(exact_spine::<8>(&source).is_some(), arity == 8);
    }
}

#[test]
fn cps_image_replay_statement_spines_refuse_long_malformed_tails_and_leave_arguments_opaque() {
    let mut opaque = Expr::fvar(clean_kernel::FVarId::new(1234));
    for _ in 0..16_384 {
        opaque = Expr::app(Expr::const_str("Nat.succ"), opaque);
    }
    let source = Expr::apps(
        Expr::const_str("Eq"),
        [opaque.clone(), opaque.clone(), opaque],
    );
    let (_, args) = exact_spine::<3>(&source).unwrap();
    assert!(std::ptr::eq(args[0], source.get_app_args()[0]));
    let mut malformed = source;
    for _ in 0..16_384 {
        malformed = Expr::app(malformed, Expr::nat_lit(0));
    }
    assert!(exact_spine::<3>(&malformed).is_none());
    assert!(exact_spine::<8>(&malformed).is_none());
}

#[test]
fn cps_image_replay_statement_spines_refuse_malformed_actual_retained_equations() {
    use super::super::equation_tests::{environment, fixture, n};
    let env = environment();
    for malformed_equality in [true, false] {
        let (mut scope, mut parts, equation, original, _) = fixture(false, false, false);
        let state = scope.try_local(n()).unwrap();
        let callback = Expr::arrow(n(), Expr::arrow(n(), n()));
        let yes = scope.try_local(callback.clone()).unwrap();
        let no = scope.try_local(callback).unwrap();
        let args = [state.term().clone(), yes.term().clone(), no.term().clone()];
        let lhs = Expr::apps(equation.operator.term().clone(), args.clone());
        let actual_rhs = Expr::apps(original, args);
        let rhs = if malformed_equality {
            actual_rhs.clone()
        } else {
            Expr::apps(actual_rhs.clone(), (0..512).map(Expr::nat_lit))
        };
        let body = Expr::apps(
            constant("Eq", vec![Level::succ(Level::zero())]),
            [n(), lhs, rhs],
        );
        let body = if malformed_equality {
            Expr::apps(body, (0..512).map(Expr::nat_lit))
        } else {
            body
        };
        let statement = state.pi(yes.pi(no.pi(body)));
        let actual_value = state.lam(yes.lam(no.lam(Expr::apps(
            constant("Eq.refl", vec![Level::succ(Level::zero())]),
            [n(), actual_rhs],
        ))));
        let retained = parts
            .bind_scoped_owned(&mut scope, &[], statement, actual_value)
            .unwrap();
        let before = parts.counts().0;
        let error = replay_image_with_structured_call_equations(
            &env,
            &mut scope,
            &[
                equation.operator.clone(),
                equation.proof.local,
                retained.local.clone(),
            ],
            &[],
            ImageTypes {
                state: n(),
                error: n(),
                value: n(),
                answer: n(),
            },
            equation.operator.term().clone(),
            Level::zero(),
            Default::default(),
            &mut parts,
            &[OwnedCpsCallEquation {
                operator: equation.operator,
                proof: retained,
                arity: 3,
            }],
        )
        .err()
        .expect("malformed actual statement must refuse before producing a candidate");
        let expected = if malformed_equality {
            "unsupported endpoint"
        } else {
            "literal TO_CPS Run"
        };
        assert!(error.contains(expected), "{error}");
        assert!(!error.contains("BudgetExhausted"), "{error}");
        assert_eq!(
            parts.counts().0,
            before,
            "no candidate helper declaration is published"
        );
        // The actual original operator/value stay in the retained carrier;
        // this parser refusal is no type certificate for the bad declaration.
    }
}
