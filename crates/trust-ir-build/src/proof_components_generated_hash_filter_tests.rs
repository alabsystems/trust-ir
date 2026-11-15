// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;

fn chain(mut root: Expr, count: usize) -> Expr {
    for _ in 0..count {
        root = Expr::app(Expr::const_str("Nat.succ"), root);
    }
    root
}

#[test]
fn bitmap_has_no_false_negative_for_any_registered_graph() {
    for bound in [0, 1, 31, 32, 80, 4096, usize::MAX] {
        let words = Memo::hash_filter_words(bound);
        assert!(words.is_power_of_two() && words <= 128);
        for hash in [0, 1, 63, 64, u32::MAX] {
            let (word, bit) = filter_slot(hash, words);
            assert!(word < words && bit.count_ones() == 1);
        }
    }
    let mut memo = Memo::shared_children_bitmap(100_000);
    let mut roots = Vec::new();
    for id in 0..1000 {
        let root = Expr::app(Expr::const_str("f"), Expr::fvar(FVarId::new(id)));
        memo.register(&root).unwrap();
        roots.push(root);
    }
    assert!(memo.hashes.is_empty());
    for root in roots {
        assert!(memo.may_have_hash(root.hash_cached()));
        assert!(memo.roots.contains_key(&DependencyKey(root)));
    }
}

#[test]
fn bitmap_keeps_empty_nested_hits_and_removes_only_the_hashset_probe() {
    let child = chain(Expr::nat_lit(0), 300);
    let root = Expr::app(Expr::const_str("wrapper"), child.clone());
    let mut old = Memo::shared_children(100_000);
    let mut bitmap = Memo::shared_children_bitmap(100_000);
    for memo in [&mut old, &mut bitmap] {
        memo.register(&child).unwrap();
        let summary = memo.scan(&child, 100_000).0.unwrap();
        memo.publish(&child, summary).unwrap();
        memo.register(&root).unwrap();
    }
    let (old_result, old_work) = old.scan(&root, 100_000);
    let (new_result, new_work) = bitmap.scan(&root, 100_000);
    let (old_result, new_result) = (old_result.unwrap(), new_result.unwrap());
    assert!(old_result.words.is_empty() && new_result.words.is_empty());
    assert_eq!(old_result.height, new_result.height);
    assert_eq!(new_result.height, 302);
    assert_eq!(old_work, new_work + 1);
    assert!(new_work < 20, "the completed deep child must remain a hit");
}

fn false_positive_fixture() -> (Memo, Expr) {
    let closed = chain(Expr::nat_lit(0), 300);
    let input = chain(Expr::fvar(FVarId::new(129)), 300);
    let retained_input = input.clone();
    let root = Expr::apps(Expr::const_str("wrapper"), [input, retained_input]);
    let mut memo = Memo::shared_children_bitmap(100_000);
    memo.register(&closed).unwrap();
    let summary = memo.scan(&closed, 100_000).0.unwrap();
    memo.publish(&closed, summary).unwrap();
    memo.register(&root).unwrap();
    memo.hash_bits.as_mut().unwrap().fill(u64::MAX);
    (memo, root)
}

#[test]
fn bitmap_false_positives_still_walk_actual_unknown_input_and_keep_full_height() {
    let (memo, root) = false_positive_fixture();
    let (result, work) = memo.scan(&root, 100_000);
    let result = result.unwrap();
    assert!(result.contains(FVarId::new(129)));
    assert_eq!(result.height, 303);
    assert!(work > 600, "a set bit must not certify an unknown child");
}

#[test]
fn bitmap_false_positive_query_cutoffs_never_publish_a_partial_root() {
    let (memo, root) = false_positive_fixture();
    let (_, exact_work) = memo.scan(&root, 100_000);
    for limit in 0..=exact_work {
        let (result, work) = memo.scan(&root, limit);
        assert!(work <= limit);
        assert_eq!(result.is_ok(), limit == exact_work, "cutoff {limit}");
        assert!(
            memo.roots
                .get(&DependencyKey(root.clone()))
                .unwrap()
                .is_none()
        );
    }
}
