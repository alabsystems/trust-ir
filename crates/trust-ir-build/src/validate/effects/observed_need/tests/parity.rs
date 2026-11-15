// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn all_places_and_both_sides_keep_exact_first_reason_blocks_and_canonical_order() {
    let first = [Piece::Text("firstλ")];
    let later = [Piece::Text("later")];
    let mut ops = Vec::new();
    for side in [Side::Read, Side::Write] {
        for place in [g(u32::MAX), g(0), p(u32::MAX), p(0), g(2)] {
            ops.push(Op::Side(side, Some(place), u32::MAX, &first));
            ops.push(Op::Side(side, Some(place), 0, &later));
        }
    }
    trace(&ops);
}
#[test]
fn everything_and_named_places_remain_independent_in_both_insertion_orders() {
    let a = [Piece::Text("everything")];
    let b = [Piece::Text("place")];
    let c = [Piece::Text("ignored top")];
    for side in [Side::Read, Side::Write] {
        trace(&[
            Op::Side(side, None, 3, &a),
            Op::Side(side, Some(p(1)), 5, &b),
            Op::Side(side, None, 9, &c),
        ]);
        trace(&[
            Op::Side(side, Some(g(1)), 5, &b),
            Op::Side(side, None, 3, &a),
        ]);
    }
}
#[test]
fn all_four_flags_retain_only_their_independent_first_reason_and_block() {
    let a = [Piece::Text("first")];
    let b = [Piece::Text("second")];
    let mut ops = Vec::new();
    for flag in [Flag::Allocates, Flag::Frees, Flag::MayUnwind, Flag::Io] {
        ops.push(Op::Flag(flag, 17, &a));
        ops.push(Op::Flag(flag, 18, &b));
    }
    trace(&ops);
}
#[test]
fn exact_raw_text_unicode_nul_and_full_u32_decimal_are_never_normalized() {
    for value in [0, 1, 9, 10, 99, 100, 1_000_000_000, u32::MAX] {
        let pieces = [
            Piece::Text("λ\0'\n *param"),
            Piece::U32(value),
            Piece::Text(" TAIL"),
        ];
        trace(&[
            Op::Side(Side::Read, Some(p(value)), value, &pieces),
            Op::Flag(Flag::Io, value, &pieces),
        ]);
    }
}
#[test]
fn duplicate_reason_recipes_are_lazy_even_when_the_unused_text_is_large() {
    let a = [Piece::Text("original")];
    let huge = "unusedλ".repeat(20000);
    let b = [Piece::Text(&huge), Piece::U32(u32::MAX)];
    let empty = [];
    let read = |pieces: &[Piece<'_>]| {
        let mut n = ObservedNeed::default();
        n.reads.places.push((p(0), (1, "original".to_string())));
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        n.add_side_observed(Side::Read, Some(p(0)), 2, pieces, &mut s, site())
            .unwrap();
        assert_eq!(n.reads.places[0].1, (1, "original".to_string()));
        n.retire_observed(&mut s, site()).unwrap();
        drop(s);
        o.events
    };
    assert_eq!(read(&empty), read(&b));
    let top = |pieces: &[Piece<'_>]| {
        let mut n = ObservedNeed::default();
        n.writes.everything = Some((1, "original".to_string()));
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        n.add_side_observed(Side::Write, None, 2, pieces, &mut s, site())
            .unwrap();
        assert_eq!(n.writes.everything, Some((1, "original".to_string())));
        n.retire_observed(&mut s, site()).unwrap();
        drop(s);
        o.events
    };
    assert_eq!(top(&empty), top(&b));
    let flag = |pieces: &[Piece<'_>]| {
        let mut n = ObservedNeed::default();
        n.io = Some((1, "original".to_string()));
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        n.add_flag_observed(Flag::Io, 2, pieces, &mut s, site())
            .unwrap();
        assert_eq!(n.io, Some((1, "original".to_string())));
        n.retire_observed(&mut s, site()).unwrap();
        drop(s);
        o.events
    };
    assert_eq!(flag(&a), flag(&b));
}
#[test]
fn empty_reason_and_empty_recipe_are_preserved_as_real_first_records() {
    let pieces = [];
    let later = [Piece::Text("later")];
    trace(&[
        Op::Side(Side::Write, None, 8, &pieces),
        Op::Side(Side::Write, None, 9, &later),
        Op::Side(Side::Read, Some(g(0)), 7, &pieces),
        Op::Flag(Flag::Frees, 6, &pieces),
        Op::Flag(Flag::Frees, 5, &later),
    ]);
}
#[test]
fn multibyte_text_crossing_chunk_boundary_is_complete_and_matches_the_ordinary_reason() {
    let why = "a".repeat(1023) + &"λ😀".repeat(1000) + "\0TAIL";
    let pieces = [Piece::Text(&why)];
    trace(&[Op::Side(Side::Read, Some(g(0)), 1, &pieces)]);
}
#[test]
fn reverse_and_forward_physical_insertions_match_the_original_map_for_all_distinct_keys() {
    let pieces = [Piece::Text("key"), Piece::U32(u32::MAX)];
    for reverse in [false, true] {
        let mut places = (0..30).map(p).chain((0..30).map(g)).collect::<Vec<_>>();
        if reverse {
            places.reverse()
        }
        let ops = places
            .iter()
            .enumerate()
            .map(|(i, p)| Op::Side(Side::Write, Some(*p), i as u32, &pieces))
            .collect::<Vec<_>>();
        trace(&ops);
    }
}
