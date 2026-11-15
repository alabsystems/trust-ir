// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn drain(n: &mut ObservedNeed, s: &mut ObservedSession<'_, Observer>) {
    n.drain(&mut Work {
        session: s,
        site: site(),
    });
    assert!(empty(n));
}
#[test]
fn place_allocation_and_transport_refusals_keep_the_complete_rendered_reason() {
    let pieces = [Piece::Text("why")];
    let mut n = ObservedNeed::default();
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    n.add_side_observed(Side::Read, Some(p(0)), 1, &pieces, &mut s, site())
        .unwrap();
    n.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let cuts = base
        .events
        .windows(2)
        .enumerate()
        .filter(|(_, pair)| {
            pair[0].phase == ExecutionPhase::Validation
                && pair[0].work == 1
                && pair[0].copy_bytes == size_of::<PlaceReason>()
                && pair[1].phase == ExecutionPhase::Validation
                && pair[1].work == 2
                && pair[1].copy_bytes == size_of::<PlaceReason>() + size_of::<usize>()
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(cuts.len(), 1);
    for after_allocation in [false, true] {
        let stop = cuts[0] + usize::from(after_allocation);
        let mut n = ObservedNeed::default();
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            n.add_side_observed(Side::Read, Some(p(0)), 1, &pieces, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(n.detail, "why");
        assert!(n.reads.places.is_empty());
        assert_eq!(n.reads.places.capacity() > 0, after_allocation);
        drain(&mut n, &mut s);
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
    }
}
#[test]
fn interrupted_canonical_swap_retains_new_and_prior_owned_records_before_consuming_cleanup() {
    let seed = || ObservedNeed {
        reads: ObservedSide {
            everything: None,
            places: vec![
                (p(1), (1, "oneλ".to_string())),
                (g(9), (2, "twoλ".to_string())),
            ],
        },
        ..ObservedNeed::default()
    };
    let pieces = [Piece::Text("newλ")];
    let mut n = seed();
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    n.add_side_observed(Side::Read, Some(p(0)), 3, &pieces, &mut s, site())
        .unwrap();
    n.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let stop = base
        .events
        .iter()
        .position(|e| {
            e.phase == ExecutionPhase::Validation
                && e.work == 2
                && e.copy_bytes == 2 * size_of::<PlaceReason>() + size_of::<usize>()
        })
        .unwrap()
        + 1;
    let mut n = seed();
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        n.add_side_observed(Side::Read, Some(p(0)), 3, &pieces, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        n.reads.places,
        [
            (p(1), (1, "oneλ".to_string())),
            (g(9), (2, "twoλ".to_string())),
            (p(0), (3, "newλ".to_string()))
        ]
    );
    assert_eq!(n.detail.capacity(), 0);
    drain(&mut n, &mut s);
}
#[test]
fn actual_text_interior_stop_retains_the_complete_first_copied_chunk() {
    let why = "a".repeat(3000);
    let pieces = [Piece::Text(&why)];
    let mut n = ObservedNeed::default();
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    n.add_flag_observed(Flag::Io, 7, &pieces, &mut s, site())
        .unwrap();
    n.retire_observed(&mut s, site()).unwrap();
    drop(s);
    // A growth admission is followed by its copy, not the next loop header.
    // This consecutive pair selects the real completed first chunk instead.
    let stop = base
        .events
        .windows(2)
        .position(|pair| {
            pair[0].phase == ExecutionPhase::Validation
                && pair[0].work == 1024
                && pair[0].copy_bytes == 1024
                && pair[1].phase == ExecutionPhase::Validation
                && pair[1].work == 1
                && pair[1].copy_bytes == size_of::<usize>()
        })
        .unwrap()
        + 2;
    let mut n = ObservedNeed::default();
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        n.add_flag_observed(Flag::Io, 7, &pieces, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(n.detail, "a".repeat(1024));
    assert!(n.io.is_none());
    drain(&mut n, &mut s);
}
#[test]
fn rejected_final_mutation_publication_keeps_the_full_record_for_original_owner_cleanup() {
    let pieces = [Piece::Text("published only after this checkλ")];
    let mut n = ObservedNeed::default();
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    n.add_flag_observed(Flag::MayUnwind, 9, &pieces, &mut s, site())
        .unwrap();
    let stop = calls.get();
    n.retire_observed(&mut s, site()).unwrap();
    drop(s);
    assert_eq!(base.events[stop - 1].phase, ExecutionPhase::Publication);
    let mut n = ObservedNeed::default();
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        n.add_flag_observed(Flag::MayUnwind, 9, &pieces, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        n.may_unwind,
        Some((9, "published only after this checkλ".to_string()))
    );
    assert_eq!(n.detail.capacity(), 0);
    drain(&mut n, &mut s);
    assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
}
#[test]
fn cleanup_refusals_never_abandon_any_reason_tail_or_overwrite_the_first_cause() {
    let reason = || Some((u32::MAX, "full λ\0TAIL".repeat(1000)));
    let mut n = ObservedNeed {
        reads: ObservedSide {
            everything: reason(),
            places: vec![(p(0), reason().unwrap()), (g(1), reason().unwrap())],
        },
        writes: ObservedSide {
            everything: reason(),
            places: vec![(g(2), reason().unwrap())],
        },
        allocates: reason(),
        frees: reason(),
        may_unwind: reason(),
        io: reason(),
        detail: "partialλ".repeat(1000),
    };
    let mut o = Observer {
        stop: Some(1),
        cleanup: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        n.add_flag_observed(Flag::Io, 1, &[], &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = s.first_refusal().unwrap().progress;
    drain(&mut n, &mut s);
    assert_eq!(s.first_refusal().unwrap().cause, "original Need stop");
    assert_eq!(s.first_refusal().unwrap().progress, first);
    drop(s);
    assert!(
        o.events[1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn string_retirement_is_the_disclosed_flat_header_drop_contract_not_a_byte_walk() {
    let retire = |why: String| {
        let n = ObservedNeed {
            reads: ObservedSide {
                everything: Some((1, why)),
                places: Vec::new(),
            },
            ..ObservedNeed::default()
        };
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        n.retire_observed(&mut s, site()).unwrap();
        drop(s);
        o.events
    };
    assert_eq!(retire("x".into()), retire("λ".repeat(100000)));
}
