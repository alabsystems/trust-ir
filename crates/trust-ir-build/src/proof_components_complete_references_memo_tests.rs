// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{proof_components::dependencies::NormalizationReferences, scoped_local::LocalScope};
use clean_kernel::{Level, Name};

fn nat() -> Expr {
    Expr::const_str("Nat")
}
fn add(left: Expr, right: Expr) -> Expr {
    Expr::apps(Expr::const_str("Nat.add"), [left, right])
}
fn eq(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), left, right],
    )
}

#[test]
fn complete_summaries_keep_ambient_ids_and_named_formals_without_sibling_pollution() {
    let mut scope = LocalScope::new();
    let ambient = scope.try_local(nat()).unwrap();
    let other = scope.try_local(nat()).unwrap();
    let formal = scope.try_local(nat()).unwrap();
    let roots = [
        other.term().clone(),
        formal.lam(add(formal.term().clone(), ambient.term().clone())),
        formal.pi(eq(formal.term().clone(), ambient.term().clone())),
        formal.let_(
            other.term().clone(),
            add(formal.term().clone(), ambient.term().clone()),
        ),
    ];
    let ids = [ambient.id(), other.id(), formal.id()];
    let mut cache = Cache::new(1024);
    let mut oracle = NormalizationReferences::new(100_000);
    let mut cold = Scan::new(&mut cache, 100_000).unwrap();
    for root in &roots {
        oracle.scan(root).unwrap();
        cold.scan(root).unwrap();
    }
    for id in ids {
        assert!(oracle.contains(id));
        assert!(cold.contains(id));
    }
    let cold_work = cold.work;
    drop(cold);
    let mut warm_work = 0;
    for (index, root) in roots.iter().enumerate() {
        let mut warm = Scan::new(&mut cache, 100_000).unwrap();
        warm.scan(root).unwrap();
        warm_work += warm.work;
        let expected = match index {
            0 => [false, true, false],
            1 | 2 => [true, false, true],
            _ => [true, true, true],
        };
        for (id, expected) in ids.into_iter().zip(expected) {
            assert_eq!(warm.contains(id), expected);
        }
    }
    assert!(warm_work > 0 && warm_work < cold_work);
}

#[test]
fn exact_changed_graph_references_never_reuse_a_different_body() {
    let mut scope = LocalScope::new();
    let first = scope.try_local(nat()).unwrap();
    let second = scope.try_local(nat()).unwrap();
    let original = Expr::app(Expr::const_str("Nat.succ"), first.term().clone());
    let changed = Expr::app(Expr::const_str("Nat.succ"), second.term().clone());
    let mut cache = Cache::new(128);
    Scan::new(&mut cache, 128).unwrap().scan(&original).unwrap();
    let mut changed_scan = Scan::new(&mut cache, 128).unwrap();
    changed_scan.scan(&changed).unwrap();
    assert!(!changed_scan.contains(first.id()));
    assert!(changed_scan.contains(second.id()));
}

#[test]
fn retained_entries_and_unique_word_storage_are_bounded_without_dropping_references() {
    let mut scope = LocalScope::new();
    let locals = (0..193)
        .map(|_| scope.try_local(nat()).unwrap())
        .collect::<Vec<_>>();
    let root = add(
        add(locals[0].term().clone(), locals[64].term().clone()),
        locals[192].term().clone(),
    );
    let mut cache = Cache::new(2);
    for _ in 0..3 {
        let mut scan = Scan::new(&mut cache, 1024).unwrap();
        scan.scan(&root).unwrap();
        for index in [0, 64, 192] {
            assert!(scan.contains(locals[index].id()));
        }
        assert!(!scan.contains(locals[1].id()));
    }
    assert!(cache.entries.len() <= 2);
    assert!(cache.retained_words <= 2);
    let unique = cache
        .entries
        .values()
        .map(|summary| (Arc::as_ptr(&summary.words) as usize, summary.words.len()))
        .collect::<HashMap<_, _>>();
    assert_eq!(cache.retained_words, unique.values().sum::<usize>());
}

#[test]
fn cached_height_cannot_hide_deeper_paths_and_failure_cannot_be_cleared() {
    let mut scope = LocalScope::new();
    let input = scope.try_local(nat()).unwrap();
    let mut shared = input.term().clone();
    for _ in 0..8 {
        shared = Expr::app(Expr::const_str("Nat.succ"), shared);
    }
    let mut cache = Cache::new(1024);
    let mut first = Scan::new(&mut cache, 1024).unwrap();
    first.max_depth = 16;
    first.scan(&shared).unwrap();
    drop(first);
    let mut deeper = shared;
    for _ in 0..8 {
        deeper = Expr::app(Expr::const_str("Nat.succ"), deeper);
    }
    let mut second = Scan::new(&mut cache, 1024).unwrap();
    second.max_depth = 16;
    assert!(second.scan(&deeper).unwrap_err().contains("depth limit"));
    drop(second);
    assert!(cache.failed);
    cache.clear_entries();
    assert!(
        Scan::new(&mut cache, 1024)
            .err()
            .unwrap()
            .contains("failed scan")
    );
}

#[test]
fn exhausted_hit_and_cold_work_are_charged_and_keep_failure_sticky() {
    let mut scope = LocalScope::new();
    let input = scope.try_local(nat()).unwrap();
    let mut cache = Cache::new(128);
    Scan::new(&mut cache, 128)
        .unwrap()
        .scan(input.term())
        .unwrap();
    let mut exhausted = Scan::new(&mut cache, 0).unwrap();
    assert!(
        exhausted
            .scan(input.term())
            .unwrap_err()
            .contains("visit limit")
    );
    drop(exhausted);
    assert!(Scan::new(&mut cache, 128).is_err());
    let mut cold = Cache::new(128);
    let mut scan = Scan::new(&mut cold, 2).unwrap();
    assert!(scan.scan(input.term()).unwrap_err().contains("visit limit"));
    assert_eq!(
        scan.work, 2,
        "pay the storage lookup before publication fails"
    );
    drop(scan);
    assert!(cold.failed);
    assert!(cold.entries.is_empty());
}
