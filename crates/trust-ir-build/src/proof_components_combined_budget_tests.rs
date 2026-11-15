// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
use clean_kernel::{Environment, Level};
fn n() -> Expr {
    Expr::const_str("Nat")
}

#[test]
fn capture_visits_and_words_share_one_limit_at_every_refusal_prefix() {
    for limit in 0..=16 {
        let mut scope = LocalScope::new();
        let a = scope.try_local(n()).unwrap();
        let b = scope.try_local(n()).unwrap();
        let mut parts = ProofComponents::new(
            "capture.combined",
            ProofLimits {
                operations: limit,
                ..Default::default()
            },
        );
        parts.set_base(&scope, vec![]).unwrap();
        let value = Expr::apps(
            Expr::const_str("Nat.add"),
            [a.term().clone(), b.term().clone()],
        );
        let before = parts.counts();
        let result = parts.bind_scoped(
            &mut scope,
            &[
                OwnedProofCapture::Parameter(a),
                OwnedProofCapture::Parameter(b),
            ],
            n(),
            value,
        );
        assert!(parts.counts().3 <= limit);
        assert!(parts.counts().3 >= before.3);
        if result.is_err() {
            assert_eq!(
                parts.counts().0,
                before.0,
                "refused scans cannot publish declarations"
            );
        }
        if limit == 8 {
            assert!(
                result.is_err(),
                "eight visits plus one word cannot fit eight combined units"
            );
            assert_eq!(parts.counts().3, 8);
        }
        if limit == 9 {
            assert!(result.is_ok());
            assert_eq!(parts.counts().3, 9);
            assert!(parts.context_work_totals().1 > 0);
        }
    }
}

#[test]
fn exact_combined_capture_boundary_keeps_original_typed_decoded_replay() {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    let mut scope = LocalScope::new();
    let a = scope.try_local(n()).unwrap();
    let b = scope.try_local(n()).unwrap();
    let mut parts = ProofComponents::new(
        "capture.combined.typed",
        ProofLimits {
            operations: 9,
            ..Default::default()
        },
    );
    parts.set_base(&scope, vec![]).unwrap();
    let value = Expr::apps(
        Expr::const_str("Nat.add"),
        [a.term().clone(), b.term().clone()],
    );
    let actual = parts
        .bind_scoped(
            &mut scope,
            &[
                OwnedProofCapture::Parameter(a.clone()),
                OwnedProofCapture::Parameter(b.clone()),
            ],
            n(),
            value.clone(),
        )
        .unwrap();
    assert_eq!(parts.counts().3, 9);
    let equality = |left: Expr, right: Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [n(), left, right],
        )
    };
    let goal = a.pi(b.pi(equality(actual, value.clone())));
    let claim = scope
        .close(&a.pi(b.pi(equality(value.clone(), value.clone()))))
        .unwrap();
    let proof = a.lam(b.lam(Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [n(), value],
    )));
    let bundle = parts
        .close_scoped(
            &scope,
            proof,
            goal,
            crate::term_scope::TermScopeLimits::default(),
        )
        .unwrap();
    let bytes = bundle.encode_with_claim(&claim).unwrap();
    let (decoded, transported) = ScopedProofComponentBundle::decode_with_claim(&bytes).unwrap();
    assert_eq!(claim, transported);
    decoded.replay(&env, &transported, 2_000_000).unwrap();
}
