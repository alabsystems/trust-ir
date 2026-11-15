// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
use super::*;
fn shared(entries: impl IntoIterator<Item = (u64, u64)>) -> Arc<Words> {
    Arc::new(entries.into_iter().collect())
}
fn identical(a: &Accumulator, b: &Arc<Words>) -> bool {
    matches!(&a.storage,Storage::Shared(value) if Arc::ptr_eq(value,b))
}

#[test]
fn exact_word_union_shares_surviving_inputs_without_copying_unchanged_words() {
    let small = shared((0..40).map(|word| (word, 3)));
    let large = shared((0..80).map(|word| (word, 7)));
    let subset = shared([(0, 1), (3, 2)]);
    let mut a = Accumulator::default();
    let mut work = 0;
    a.include(&small, &mut work, 100_000).unwrap();
    assert!(identical(&a, &small));
    a.word(0, 1, &mut work, 100_000).unwrap();
    assert!(identical(&a, &small));
    a.include(&subset, &mut work, 100_000).unwrap();
    assert!(identical(&a, &small));
    a.include(&large, &mut work, 100_000).unwrap();
    assert!(identical(&a, &large));
    assert_eq!(a.statistics().copied_words, 0);
    assert!(!a.requires_header());
    assert!(Arc::ptr_eq(&a.finish(), &large));
}
#[test]
fn exact_word_copy_all_cutoffs_prepay_before_mutating_any_shared_input() {
    let input = shared([(0, 1), (1, 2)]);
    let attempt = |available: usize| {
        let mut a = Accumulator::default();
        let mut work = 0;
        a.include(&input, &mut work, 100_000).unwrap();
        let before = work;
        let result = a.word(0, 2, &mut work, before + available);
        assert!(work <= before + available);
        assert_eq!(input.get(&0), Some(&1));
        assert_eq!(input.get(&1), Some(&2));
        if result.is_ok() {
            assert_eq!(a.get(&0), Some(&3));
            assert_eq!(a.get(&1), Some(&2));
        } else {
            assert_eq!(a.words(), input.as_ref());
        }
        (result.is_ok(), work - before)
    };
    let (ok, required) = attempt(100_000);
    assert!(ok);
    for available in 0..=required {
        assert_eq!(attempt(available).0, available == required);
    }
}
#[test]
fn exact_word_both_subset_probes_fail_closed_with_the_old_input_intact() {
    let left = shared([(0, 1)]);
    let right = shared([(0, 2)]);
    let mut a = Accumulator::default();
    let mut work = 0;
    a.include(&left, &mut work, 100).unwrap();
    let before = work;
    assert!(a.include(&right, &mut work, before + 2).is_err());
    assert!(identical(&a, &left));
    assert_eq!(a.words(), left.as_ref());
    assert_eq!(right.get(&0), Some(&2));
    assert_eq!(a.statistics().copied_words, 0);
}
#[test]
fn exact_word_union_cutoffs_never_overdraw_or_mutate_either_retained_set() {
    let left = shared([(0, 1), (1, 1)]);
    let right = shared([(0, 2), (2, 1)]);
    for limit in 0..64 {
        let mut a = Accumulator::default();
        let mut work = 0;
        if a.include(&left, &mut work, limit).is_ok() && a.include(&right, &mut work, limit).is_ok()
        {
            assert_eq!(
                a.words(),
                &[(0, 3), (1, 1), (2, 1)].into_iter().collect::<Words>()
            );
        }
        assert!(work <= limit);
        assert_eq!(
            left.as_ref(),
            &[(0, 1), (1, 1)].into_iter().collect::<Words>()
        );
        assert_eq!(
            right.as_ref(),
            &[(0, 2), (2, 1)].into_iter().collect::<Words>()
        );
    }
}
#[test]
fn exact_word_union_matches_an_independent_multiword_oracle_after_shared_and_owned_updates() {
    let mut seed = 0x5151a5_u64;
    for _ in 0..1000 {
        let mut a = Accumulator::default();
        let mut work = 0;
        let mut expected = std::collections::BTreeMap::new();
        for stage in 0..6 {
            let mut incoming = Words::new();
            for word in 0..20 {
                seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
                let bits = (seed >> 32) & 15;
                if bits != 0 {
                    incoming.insert(word, bits);
                    *expected.entry(word).or_insert(0) |= bits;
                }
            }
            a.include(&Arc::new(incoming), &mut work, 100_000).unwrap();
            a.word(100 + stage, 1, &mut work, 100_000).unwrap();
            expected.insert(100 + stage, 1);
            assert_eq!(
                a.iter()
                    .map(|(&word, &bits)| (word, bits))
                    .collect::<std::collections::BTreeMap<_, _>>(),
                expected
            );
        }
    }
}
