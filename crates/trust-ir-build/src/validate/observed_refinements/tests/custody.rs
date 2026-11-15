// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn sticky_cleanup_drains_every_owned_partial_field_seen_key_batch_and_borrowed_stack() {
    let m = module();
    let mut state = State::default();
    let text = "λ\0'".repeat(3000);
    state.location = text.clone();
    state.base_location = text.clone();
    state.detail = text.clone();
    state.actual = text.clone();
    state.required = text.clone();
    state.key = text.clone();
    state.seen_universes.push((text.clone(), 0));
    state.seen_preds.push((text.clone(), 0));
    state.type_stack.push(&m.types[0]);
    state.pred_stack.push(PredFrame::Visit(&m.predicates[0]));
    state.pred_path.push(&m.predicates[0]);
    state.inline_types.push(&m.types[0]);
    state.errors.push(ValidationError::RefinementNotImplied {
        location: text.clone(),
        actual: text.clone(),
        required: text.clone(),
    });
    state.scratch.push(ValidationError::RefinementContradicted {
        location: text.clone(),
        declared: text.clone(),
        derived: text.clone(),
    });
    state
        .refusals
        .push(ValidationError::PredicateTableMalformed {
            location: text.clone(),
            detail: text.clone(),
        });
    let mut o = Observer::default();
    o.stop.set(Some(1));
    let mut s = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    let mut work = Work {
        session: &mut s,
        site: site(),
    };
    assert!(work.admit(1, 1).is_err());
    let first = work.session.first_refusal().unwrap().progress;
    drain(&mut state, &mut work);
    assert!(empty(&state));
    assert_eq!(work.session.first_refusal().unwrap().progress, first);
    assert_eq!(work.session.remaining_fuel(), 0);
    drop(work);
    drop(s);
    let retired = o
        .events
        .iter()
        .filter(|e| e.phase == ExecutionPhase::ScratchRetirement)
        .map(|e| e.work)
        .sum::<usize>();
    // Eight flat Strings are byte-walked; eight diagnostic String fields
    // use the distinct generic header/drop contract. Three one-error child
    // drains add 6V+8S+3Q+797, including three 259-variant dispatches;
    // local/key headers and borrowed rows add20.
    let expected_retired = 8 * text.len()
        + 6 * size_of::<ValidationError>()
        + 8 * size_of::<String>()
        + 3 * size_of::<Vec<ValidationError>>()
        + 3 * 259
        + 40;
    assert_eq!(retired, expected_retired);
    assert!(
        o.events[1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement && e.site == site())
    );
}
#[test]
fn actual_complete_value_map_and_successor_child_stay_owned_across_the_next_refused_fee() {
    let mut m = small();
    let instruction = Inst::Switch {
        value: v(0),
        default: b(3),
        default_args: vec![v(0), v(1)],
        cases: vec![
            SwitchCase {
                value: Constant::Int(7),
                target: b(1),
                args: vec![v(2)],
            },
            SwitchCase {
                value: Constant::Int(9),
                target: b(2),
                args: vec![v(3), v(4), v(5)],
            },
        ],
        exhaustive_enum_unreachable: false,
    };
    m.functions[0].blocks[0]
        .body
        .push(node(instruction.clone(), &[]));
    let mut direct = Observer::default();
    let direct_calls = direct.calls.clone();
    let mut ds = ObservedSession::new(InterpretOptions::default(), &mut direct);
    let mut edge_child = instruction
        .successor_edges_observed(&mut ds, site())
        .unwrap();
    let direct_end = direct_calls.get();
    {
        let mut w = Work {
            session: &mut ds,
            site: site(),
        };
        w.retire_vec(&mut edge_child);
    }
    drop(ds);
    let mut o = Observer::default();
    let stop = o.stop.clone();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut flow = graph::Flow::default();
    flow.values =
        Some(build_module_value_types_observed(&m.functions[0], &m, w.session, w.site).unwrap());
    assert_eq!(flow.value(v(0), &mut w).unwrap(), Some(&Ty::I32));
    let begin = calls.get();
    flow.edges(&instruction, &mut w).unwrap();
    assert_eq!(flow.edges.len(), 3);
    assert_eq!(flow.edges[0].target, b(3));
    assert_eq!(flow.edges[0].args.len(), 2);
    assert_eq!(flow.edges[2].args.len(), 3);
    stop.set(Some(calls.get() + 1));
    assert!(w.admit(1, 99).is_err());
    assert!(flow.values.is_some());
    assert_eq!(flow.edges.len(), 3);
    let first = w.session.first_refusal().unwrap().progress;
    flow.retire(&mut w);
    assert!(flow.values.is_none());
    assert_eq!(flow.edges.capacity(), 0);
    assert_eq!(w.session.first_refusal().unwrap().progress, first);
    drop(w);
    drop(s);
    assert_eq!(
        &o.events[begin + 1..begin + 1 + direct_end],
        &direct.events[..direct_end]
    );
}
#[test]
fn every_actual_union_callback_retires_partial_requested_scalar_payload_and_outer_arena() {
    let mut m = module();
    m.predicates
        .push(Pred::FiniteSet(vec![Constant::Int(2), Constant::Int(4)]));
    let mut baseline = Observer::default();
    let count = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut facts = Facts::default();
    let result = facts
        .join(
            &m,
            Fact::Table(PredId::new(5)),
            Fact::Table(PredId::new(10)),
            &mut w,
        )
        .unwrap();
    assert!(matches!(result, Fact::Set(0)));
    assert_eq!(facts.sets[0], vec![(0, 1), (0, 2), (0, 3), (0, 4)]);
    let end = count.get();
    facts.retire(&mut w);
    drop(w);
    drop(s);
    let mut saw_partial = false;
    for cut in 1..=end {
        let mut o = Observer::default();
        o.stop.set(Some(cut));
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let mut facts = Facts::default();
        assert!(
            facts
                .join(
                    &m,
                    Fact::Table(PredId::new(5)),
                    Fact::Table(PredId::new(10)),
                    &mut w
                )
                .is_err()
        );
        saw_partial |= facts.pending.capacity() > 0;
        let first = w.session.first_refusal().unwrap().progress;
        facts.retire(&mut w);
        assert_eq!(facts.pending.capacity(), 0);
        assert_eq!(facts.sets.capacity(), 0);
        assert_eq!(w.session.first_refusal().unwrap().progress, first);
    }
    assert!(saw_partial);
}
#[test]
fn replaced_derived_tokens_retire_their_record_while_the_whole_shared_payload_owner_survives() {
    let mut m = module();
    m.predicates
        .push(Pred::FiniteSet(vec![Constant::Int(2), Constant::Int(4)]));
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut flow = graph::Flow::default();
    let fact = flow
        .facts
        .join(
            &m,
            Fact::Table(PredId::new(5)),
            Fact::Table(PredId::new(10)),
            &mut w,
        )
        .unwrap();
    flow.set(7, fact, &mut w).unwrap();
    flow.set(8, fact, &mut w).unwrap();
    let begin = calls.get();
    flow.set(7, Fact::Interval(99, 99), &mut w).unwrap();
    let end = calls.get();
    assert_eq!(flow.fact(7, &mut w).unwrap(), Fact::Interval(99, 99));
    assert_eq!(flow.fact(8, &mut w).unwrap(), fact);
    assert_eq!(flow.facts.sets[0], vec![(0, 1), (0, 2), (0, 3), (0, 4)]);
    flow.retire(&mut w);
    assert_eq!(flow.derived.capacity(), 0);
    assert_eq!(flow.facts.sets.capacity(), 0);
    drop(w);
    drop(s);
    assert!(
        o.events[begin..end]
            .iter()
            .any(|e| e.phase == ExecutionPhase::ScratchRetirement && e.work == size_of::<Fact>())
    );
}
#[test]
fn actual_enum_later_implication_consumes_all_provisional_named_error_fields() {
    let m = {
        let mut m = module();
        m.enums.push(enumeration(vec![r(2), r(1)]));
        m
    };
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let mut state = State::default();
    let facts = Facts::default();
    state.base_location = "actual enum write λ".into();
    state
        .consumption(&m, &r(5), &r(2), None, &facts, Sink::Scratch, &mut w)
        .unwrap();
    assert!(
        matches!(state.scratch.as_slice(),[ValidationError::RefinementNotImplied{actual,required,..}]if actual.contains("in{1, 3}")&&required.contains("in[5, 9]"))
    );
    w.errors(&mut state.scratch);
    let begin = calls.get();
    state
        .enum_consumption(
            &m,
            &Ty::Enum(EnumId::new(17)),
            1,
            &r(5),
            None,
            &facts,
            consumption::Direction::Write,
            &mut w,
        )
        .unwrap();
    let end = calls.get();
    assert!(state.errors.is_empty());
    assert_eq!(state.refusals.capacity(), 0);
    assert_eq!(state.scratch.capacity(), 0);
    drain(&mut state, &mut w);
    assert!(empty(&state));
    drop(w);
    drop(s);
    assert!(
        o.events[begin..end]
            .iter()
            .any(|e| e.phase == ExecutionPhase::ScratchRetirement && e.work > 0)
    );
}
#[test]
fn failed_final_publication_retires_the_entire_real_error_payload_without_partial_output() {
    let m = small();
    let (expected, baseline, end) = run(&m);
    assert!(!expected.is_empty());
    let mut o = Observer::default();
    o.stop.set(Some(end));
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_module_refinements_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().progress,
        baseline.events[end - 1]
    );
    drop(s);
    assert_eq!(&o.events[..end], &baseline.events[..end]);
    assert!(
        o.events[end..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement && e.site == site())
    );

    // Independently consume the complete ordinary error batch after refusing
    // the identical publication. The helper's finish admission is suppressed
    // by this sticky session, while every real retirement callback survives.
    let mut retirement = Observer::default();
    retirement.stop.set(Some(1));
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut retirement);
    assert!(session.admit(baseline.events[end - 1]).is_err());
    assert_eq!(
        session.first_refusal().unwrap().progress,
        baseline.events[end - 1]
    );
    assert_eq!(
        retire_validation_errors_observed(expected, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        session.first_refusal().unwrap().progress,
        baseline.events[end - 1]
    );
    assert_eq!(
        session.first_refusal().unwrap().cause,
        "original refinement stop"
    );
    drop(session);
    assert!(retirement.events.len() > 1);
    assert_eq!(&o.events[end..], &retirement.events[1..]);
}
#[test]
fn successful_caller_retirement_has_nonempty_cleanup_prefix_and_exact_terminal_receipt() {
    let m = small();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let out = validate_module_refinements_observed(&m, &mut s, site()).unwrap();
    assert_eq!(out, ordinary(&m));
    let begin = calls.get();
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    let end = calls.get();
    assert!(s.first_refusal().is_none());
    drop(s);
    let tail = &o.events[begin..end];
    assert!(tail.len() > 1);
    assert!(
        tail[..tail.len() - 1]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement && e.site == site())
    );
    assert_eq!(
        *tail.last().unwrap(),
        ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site: site(),
            work: 0,
            copy_bytes: 0
        }
    );
}

#[test]
fn allocated_empty_string_reference_and_scalar_buffers_are_consumed_after_initial_refusal() {
    let mut state = State::default();
    state.key = String::with_capacity(4096);
    state.inline_types = Vec::with_capacity(64);
    state.type_stack = Vec::with_capacity(64);
    state.pred_stack = Vec::with_capacity(64);
    state.pred_path = Vec::with_capacity(64);
    let mut facts = Facts::default();
    facts.pending = Vec::with_capacity(64);
    facts.sets = Vec::with_capacity(8);
    assert!(state.key.capacity() >= 4096);
    assert!(facts.pending.capacity() > 0);
    let mut o = Observer::default();
    o.stop.set(Some(1));
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert!(w.admit(1, 1).is_err());
    let first = w.session.first_refusal().unwrap().progress;
    drain(&mut state, &mut w);
    facts.retire(&mut w);
    assert!(empty(&state));
    assert_eq!(facts.pending.capacity(), 0);
    assert_eq!(facts.sets.capacity(), 0);
    assert_eq!(w.session.first_refusal().unwrap().progress, first);
}
