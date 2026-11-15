// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::proof_assembly::ProofLimits;
use crate::scoped_local::LocalScope;

fn parts(scope: &LocalScope, cap: usize) -> ProofComponents {
    let mut parts = ProofComponents::new(
        "frame.reached.index",
        ProofLimits {
            operations: cap,
            ..Default::default()
        },
    );
    parts.set_base(scope, vec![]).unwrap();
    parts
}

#[test]
fn cps_image_replay_frame_reached_index_every_payment_cutoff_is_atomic_and_restore_prepaid() {
    let mut scope = LocalScope::new();
    let local = scope.try_local(Expr::const_str("Nat")).unwrap();
    let proof = Expr::nat_lit(42);
    for cap in 0..=64 {
        let mut parts = parts(&scope, cap);
        let mut reached = ReachedRelations::default();
        let result = reached.push(&mut parts, &local, &proof);
        if cap < 12 {
            assert!(result.is_err());
            assert!(reached.entries.is_empty() && reached.latest.is_empty());
            assert_eq!(parts.counts().3, 0);
        } else {
            result.unwrap();
            assert_eq!(reached.len(), 1);
            let selected = reached.get(&mut parts, local.id());
            if cap < 15 {
                assert!(selected.is_err());
            } else {
                assert_eq!(selected.unwrap(), Some(proof.clone()));
            }
            let spent = parts.counts().3;
            reached.restore(0);
            assert!(reached.entries.is_empty() && reached.latest.is_empty());
            assert_eq!(
                parts.counts().3,
                spent,
                "restoration has no new charge or refund"
            );
        }
        assert!(parts.counts().3 <= cap);
        assert_eq!(
            parts.counts().0,
            0,
            "candidate index publishes no declaration"
        );
    }
}

#[test]
fn cps_image_replay_frame_reached_index_matches_independent_reverse_inventory_oracle() {
    let mut scope = LocalScope::new();
    let locals = (0..17)
        .map(|_| scope.try_local(Expr::const_str("Nat")).unwrap())
        .collect::<Vec<_>>();
    let absent = scope.try_local(Expr::const_str("Nat")).unwrap();
    let mut parts = parts(&scope, 1_000_000);
    let mut reached = ReachedRelations::default();
    let mut expected: Vec<(FVarId, Expr)> = Vec::new();
    let mut seed = 0x51b1_1a95_u64;
    for step in 0..4096 {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
        if seed & 3 == 0 || expected.len() == 64 {
            let checkpoint = (seed as usize >> 8) % (expected.len() + 1);
            reached.restore(checkpoint);
            expected.truncate(checkpoint);
        } else {
            let local = &locals[(seed as usize >> 8) % locals.len()];
            let proof = Expr::nat_lit(step);
            reached.push(&mut parts, local, &proof).unwrap();
            expected.push((local.id(), proof));
        }
        for local in locals.iter().chain(std::iter::once(&absent)) {
            let oracle = expected
                .iter()
                .rev()
                .find(|(id, _)| *id == local.id())
                .map(|(_, proof)| proof.clone());
            assert_eq!(reached.get(&mut parts, local.id()).unwrap(), oracle);
        }
        assert_eq!(
            reached.ids().collect::<Vec<_>>(),
            expected.iter().map(|(id, _)| *id).collect::<Vec<_>>()
        );
    }
}

#[test]
fn cps_image_replay_frame_reached_index_restores_duplicates_and_same_length_siblings() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(Expr::const_str("Nat")).unwrap();
    let b = scope.try_local(Expr::const_str("Nat")).unwrap();
    let c = scope.try_local(Expr::const_str("Nat")).unwrap();
    let mut parts = parts(&scope, 1000);
    let mut reached = ReachedRelations::default();
    reached.push(&mut parts, &a, &Expr::nat_lit(10)).unwrap();
    reached.push(&mut parts, &a, &Expr::nat_lit(20)).unwrap();
    reached.push(&mut parts, &b, &Expr::nat_lit(30)).unwrap();
    assert_eq!(
        reached.get(&mut parts, a.id()).unwrap(),
        Some(Expr::nat_lit(20))
    );
    reached.restore(1);
    reached.push(&mut parts, &c, &Expr::nat_lit(40)).unwrap();
    reached.push(&mut parts, &a, &Expr::nat_lit(50)).unwrap();
    assert_eq!(reached.len(), 3);
    assert_eq!(reached.get(&mut parts, b.id()).unwrap(), None);
    assert_eq!(
        reached.get(&mut parts, c.id()).unwrap(),
        Some(Expr::nat_lit(40))
    );
    reached.restore(1);
    assert_eq!(
        reached.get(&mut parts, a.id()).unwrap(),
        Some(Expr::nat_lit(10))
    );
    assert_eq!(reached.get(&mut parts, c.id()).unwrap(), None);
}

#[test]
fn cps_image_replay_frame_reached_index_failed_child_budget_still_restores_exact_prefix() {
    let mut scope = LocalScope::new();
    let a = scope.try_local(Expr::const_str("Nat")).unwrap();
    let b = scope.try_local(Expr::const_str("Nat")).unwrap();
    let mut parts = parts(&scope, 25);
    let mut reached = ReachedRelations::default();
    reached.push(&mut parts, &a, &Expr::nat_lit(10)).unwrap();
    reached.push(&mut parts, &b, &Expr::nat_lit(20)).unwrap();
    assert!(reached.get(&mut parts, b.id()).is_err());
    let before = parts.counts().3;
    reached.restore(1);
    assert_eq!(parts.counts().3, before);
    assert_eq!(reached.latest.len(), 1);
    assert_eq!(reached.latest.get(&a.id()), Some(&0));
    assert!(!reached.latest.contains_key(&b.id()));
    assert_eq!(reached.proof_at(0), &Expr::nat_lit(10));
}

#[test]
fn cps_image_replay_frame_reached_index_lookup_work_does_not_rescan_unrelated_entries() {
    let mut scope = LocalScope::new();
    let locals = (0..128)
        .map(|_| scope.try_local(Expr::const_str("Nat")).unwrap())
        .collect::<Vec<_>>();
    let mut parts = parts(&scope, 10_000);
    let mut reached = ReachedRelations::default();
    for (index, local) in locals.iter().enumerate().take(127) {
        reached
            .push(&mut parts, local, &Expr::nat_lit(index as u64))
            .unwrap();
    }
    let before = parts.counts().3;
    assert_eq!(
        reached.get(&mut parts, locals[0].id()).unwrap(),
        Some(Expr::nat_lit(0))
    );
    assert_eq!(parts.counts().3 - before, 3);
    let before = parts.counts().3;
    assert_eq!(reached.get(&mut parts, locals[127].id()).unwrap(), None);
    assert_eq!(parts.counts().3 - before, 3);
}
