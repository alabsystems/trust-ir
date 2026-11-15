// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_constructor_and_actual_mutation_callback_refuses_then_drains_the_whole_need() {
    let pieces = [Piece::Text("firstλ"), Piece::U32(u32::MAX)];
    let ops = [
        Op::Side(Side::Read, Some(g(9)), 1, &pieces),
        Op::Side(Side::Read, Some(p(1)), 2, &pieces),
        Op::Side(Side::Write, None, 3, &pieces),
        Op::Flag(Flag::Io, 4, &pieces),
    ];
    let (base, bound) = trace(&ops);
    for stop in 1..=bound {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            execute(&ops, &mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
        drop(s);
        assert!(
            o.events[stop..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn work_and_copy_caps_accumulate_across_whole_needs_in_the_original_session() {
    let pieces = [Piece::Text("same owner")];
    let ops = [
        Op::Side(Side::Read, Some(p(0)), 1, &pieces),
        Op::Flag(Flag::Allocates, 2, &pieces),
    ];
    let (base, _) = trace(&ops);
    for copy in [false, true] {
        let mut o = Observer {
            cap: (!copy).then_some(base.work),
            byte_cap: copy.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        execute(&ops, &mut s).unwrap();
        assert_eq!(
            execute(&ops, &mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            execute(&ops, &mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
    }
}
#[test]
fn exact_instruction_site_and_zero_fuel_survive_constructor_mutations_and_consuming_retirement() {
    let exact = ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(3),
        block: BlockId::new(4),
        instruction_index: usize::MAX,
    });
    let mut o = Observer::default();
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let mut n = ObservedNeed::new_observed(&mut s, exact).unwrap();
    n.add_side_observed(
        Side::Read,
        Some(g(0)),
        1,
        &[Piece::Text("raw")],
        &mut s,
        exact,
    )
    .unwrap();
    n.add_flag_observed(Flag::Io, 2, &[Piece::U32(u32::MAX)], &mut s, exact)
        .unwrap();
    n.retire_observed(&mut s, exact).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|e| e.site == exact));
}
#[test]
fn first_header_refusal_cannot_be_renewed_by_mutation_or_consuming_cleanup() {
    let mut n = ObservedNeed::default();
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(matches!(
        ObservedNeed::new_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    ));
    let first = s.first_refusal().unwrap().progress;
    assert_eq!(
        n.add_flag_observed(Flag::Io, 1, &[Piece::Text("not created")], &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        n.retire_observed(&mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, first);
}
#[test]
fn a_partial_prior_reason_is_refused_before_a_second_operation_can_overwrite_it() {
    let mut n = ObservedNeed::default();
    n.detail = "retained fullλ".repeat(1000);
    let original = n.detail.clone();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        n.add_side_observed(Side::Write, None, 1, &[Piece::Text("new")], &mut s, site()),
        Err(ObservedValueError::InvalidRange)
    );
    assert_eq!(n.detail, original);
    assert!(n.writes.everything.is_none());
    n.retire_observed(&mut s, site()).unwrap();
    assert!(s.first_refusal().is_none());
}
