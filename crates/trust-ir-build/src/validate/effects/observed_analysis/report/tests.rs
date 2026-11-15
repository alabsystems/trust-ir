// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Six authored UNRUN private Report controls. Fixtures/oracles are test-only.
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::super::tests::{Observer, site};
use super::*;
use trust_ir::interpret::InterpretOptions;
use trust_ir::value::GlobalId;

fn p(index: u32) -> EffectPlace {
    EffectPlace::ParamPointee { index }
}
fn g(index: u32) -> EffectPlace {
    EffectPlace::Global(GlobalId::new(index))
}
fn error(function: &str, effect: &'static str, block: u32, inst: &str) -> ValidationError {
    ValidationError::EffectSummaryViolated {
        function: function.into(),
        effect,
        block,
        inst: inst.into(),
    }
}
fn need() -> ObservedNeed {
    let mut n = ObservedNeed::default();
    n.reads.everything = Some((11, "read everything λ\0".into()));
    n.reads.places = vec![(p(0), (12, "suppressed read".into()))];
    n.writes.everything = Some((21, "write everything 尾".into()));
    n.writes.places = vec![
        (p(1), (22, "write param".into())),
        (g(2), (23, "write global".into())),
    ];
    n.allocates = Some((31, "allocation".into()));
    n.frees = Some((32, "free".into()));
    n.may_unwind = Some((33, "unwind".into()));
    n.io = Some((34, "io".into()));
    n.detail = "unfinished detail λ\0尾".into();
    n
}
fn check_need(n: &ObservedNeed) {
    assert_eq!(
        n.reads.everything.as_ref(),
        Some(&(11, "read everything λ\0".into()))
    );
    assert_eq!(n.reads.places, vec![(p(0), (12, "suppressed read".into()))]);
    assert_eq!(
        n.writes.everything.as_ref(),
        Some(&(21, "write everything 尾".into()))
    );
    assert_eq!(
        n.writes.places,
        vec![
            (p(1), (22, "write param".into())),
            (g(2), (23, "write global".into()))
        ]
    );
    assert_eq!(n.allocates.as_ref(), Some(&(31, "allocation".into())));
    assert_eq!(n.frees.as_ref(), Some(&(32, "free".into())));
    assert_eq!(n.may_unwind.as_ref(), Some(&(33, "unwind".into())));
    assert_eq!(n.io.as_ref(), Some(&(34, "io".into())));
    assert_eq!(n.detail, "unfinished detail λ\0尾");
}
fn tail() -> Vec<PlaceReason> {
    vec![
        (p(8), (81, "tail param λ".into())),
        (g(9), (91, "tail global 尾".into())),
    ]
}
fn state(slot: Slot) -> Report {
    let mut r = Report {
        need: Some(need()),
        batch: Some(tail().into_iter()),
        errors: vec![error("prior name λ", "io", 71, "prior full detail 尾")],
        ..Report::default()
    };
    match slot {
        Slot::Reason => r.reason = Some((41, "pending reason λ\0尾".into())),
        Slot::Place => r.place = Some((p(4), (42, "pending place λ\0尾".into()))),
    }
    r
}
fn check_pending(r: &Report, slot: Slot) {
    check_need(r.need.as_ref().unwrap());
    assert_eq!(r.batch.as_ref().unwrap().as_slice(), tail());
    assert_eq!(
        r.errors,
        vec![error("prior name λ", "io", 71, "prior full detail 尾")]
    );
    match slot {
        Slot::Reason => {
            assert_eq!(
                r.reason.as_ref(),
                Some(&(41, "pending reason λ\0尾".into()))
            );
            assert!(r.place.is_none());
        }
        Slot::Place => {
            assert_eq!(
                r.place.as_ref(),
                Some(&(p(4), (42, "pending place λ\0尾".into())))
            );
            assert!(r.reason.is_none());
        }
    }
}
fn drained(r: &Report) {
    assert!(r.need.is_none());
    assert!(r.reason.is_none());
    assert!(r.place.is_none());
    assert!(r.batch.is_none());
    assert_eq!(r.name.capacity(), 0);
    assert_eq!(r.errors.capacity(), 0);
}
fn emit_trace(slot: Slot, name: &str) -> (Observer, usize, usize) {
    let mut r = state(slot);
    // The actual starting capacity determines the real old/new reserve charge.
    assert_eq!(r.errors.len(), r.errors.capacity());
    let images = r.errors.len() * 2 + 1 + r.errors.capacity();
    let mut o = Observer::default();
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    r.emit("reads", slot, name, &mut w).unwrap();
    let bound = calls.get(); // Before finish or caller-owned disposal.
    let output = r.finish(Ok(()), &mut w).unwrap();
    assert_eq!(output.len(), 2);
    drained(&r);
    retire_validation_errors_observed(output, w.session, w.site).unwrap();
    assert!(w.session.first_refusal().is_none());
    drop(w);
    drop(s);
    (o, bound, images)
}
fn full_state() -> Report {
    let mut r = state(Slot::Reason);
    r.place = Some((g(44), (45, "additional owned place 尾".into())));
    r.name = "partially copied function λ".into();
    r.errors.push(error(
        "second prior name",
        "frees",
        72,
        "second prior detail λ",
    ));
    r
}

#[test]
fn complete_need_is_owned_before_the_first_report_callback() {
    let mut r = Report {
        need: Some(need()),
        ..Report::default()
    };
    let mut o = Observer {
        stop: Some(1),
        cleanup: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    // Identical private run prefix: capture, first header, then finish.
    let result = w.admit(1, size_of::<Report>());
    assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
    check_need(r.need.as_ref().unwrap());
    assert_eq!(
        r.finish(result, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    drained(&r);
    assert_eq!(
        w.session.first_refusal().unwrap().cause,
        "original effects stop"
    );
    assert_eq!(w.session.remaining_fuel(), InterpretOptions::default().fuel);
    drop(w);
    drop(s);
    assert!(
        o.events[1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    // Actual run must take exactly that ownership/cleanup path at the same cut.
    let mut actual = Observer {
        stop: Some(1),
        cleanup: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut actual);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        run(need(), "function", &EffectSummary::pure(), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    drop(w);
    drop(s);
    assert_eq!(actual.events, o.events);
    assert!(actual.events.iter().all(|e| e.site == site()));
}

#[test]
fn emit_text_reserve_and_transport_stops_retain_slot_tail_and_prefix() {
    let name = "function λ";
    for slot in [Slot::Reason, Slot::Place] {
        let (base, bound, images) = emit_trace(slot, name);
        let prefix = &base.events[..bound];
        let copies: Vec<_> = prefix
            .iter()
            .enumerate()
            .filter(|(_, e)| {
                e.phase == ExecutionPhase::Validation
                    && e.work == name.len()
                    && e.copy_bytes == name.len()
            })
            .map(|(i, _)| i + 1)
            .collect();
        let reserves: Vec<_> = prefix
            .iter()
            .enumerate()
            .filter(|(_, e)| {
                e.phase == ExecutionPhase::Validation
                    && e.work == images
                    && e.copy_bytes == images * size_of::<ValidationError>()
            })
            .map(|(i, _)| i + 1)
            .collect();
        assert_eq!(copies.len(), 2); // Name growth, then actual name copy.
        assert_eq!(copies[1], copies[0] + 1);
        assert_eq!(reserves.len(), 1);
        let reserve = reserves[0];
        assert_eq!(
            (prefix[reserve - 2].work, prefix[reserve - 2].copy_bytes),
            (1, 0)
        );
        assert_eq!(
            (prefix[reserve].work, prefix[reserve].copy_bytes),
            (
                3,
                size_of::<ValidationError>()
                    + size_of::<Option<PlaceReason>>()
                    + size_of::<Option<Reason>>()
                    + size_of::<String>()
            )
        );
        for stop in [copies[1], reserve, reserve + 1] {
            let mut r = state(slot);
            let mut o = Observer {
                stop: Some(stop),
                cleanup: true,
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let mut w = Work {
                session: &mut s,
                site: site(),
            };
            let result = r.emit("reads", slot, name, &mut w);
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
            check_pending(&r, slot);
            assert_eq!(r.name, if stop == copies[1] { "" } else { name });
            assert_eq!(
                w.session.first_refusal().unwrap().progress,
                prefix[stop - 1]
            );
            assert_eq!(
                r.finish(result, &mut w),
                Err(ObservedValueError::AdmissionRefused)
            );
            drained(&r);
            assert_eq!(
                w.session.first_refusal().unwrap().cause,
                "original effects stop"
            );
            drop(w);
            drop(s);
            assert_eq!(&o.events[..stop], &prefix[..stop]);
            assert!(
                o.events[stop..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}

#[test]
fn copied_function_name_prefix_stays_owned_at_interior_and_cumulative_stops() {
    let name = "é".repeat(1600);
    let (base, bound, _) = emit_trace(Slot::Place, &name);
    let prefix = &base.events[..bound];
    // First growth+copy are consecutive; the next callback begins chunk two.
    let windows: Vec<_> = prefix
        .windows(3)
        .enumerate()
        .filter(|(_, es)| {
            es[0].phase == ExecutionPhase::Validation
                && es[0].work == 1024
                && es[0].copy_bytes == 1024
                && es[1] == es[0]
                && es[2].work == 1
                && es[2].copy_bytes == size_of::<usize>()
        })
        .map(|(i, _)| i)
        .collect();
    assert_eq!(windows.len(), 1);
    let stop = windows[0] + 3;
    // The second actual copy has a growth event with a distinct, larger charge.
    let copies: Vec<_> = prefix
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 1024
        })
        .map(|(i, _)| i + 1)
        .collect();
    assert_eq!(copies.len(), 4); // First growth, then three complete 1024-byte copies.
    let second_copy = copies[2];
    let cap = prefix[..second_copy - 1]
        .iter()
        .map(|e| e.copy_bytes)
        .sum::<usize>()
        + 512;
    for cumulative in [false, true] {
        let mut r = state(Slot::Place);
        let mut o = if cumulative {
            Observer {
                byte_cap: Some(cap),
                ..Observer::default()
            }
        } else {
            Observer {
                stop: Some(stop),
                ..Observer::default()
            }
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let result = r.emit("writes", Slot::Place, &name, &mut w);
        assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
        check_pending(&r, Slot::Place);
        assert_eq!(r.name, &name[..1024]);
        let expected = if cumulative { second_copy } else { stop };
        assert_eq!(
            w.session.first_refusal().unwrap().progress,
            prefix[expected - 1]
        );
        assert_eq!(
            w.session.first_refusal().unwrap().cause,
            if cumulative {
                "copy"
            } else {
                "original effects stop"
            }
        );
        assert_eq!(
            r.finish(result, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        drained(&r);
    }
}

// The ordinary reporting block, applied to borrowed test fixtures. Its clones,
// formatting and singleton construction are oracle work, never implementation.
fn ordinary(n: &ObservedNeed, function: &str, declared: &EffectSummary) -> Vec<ValidationError> {
    let mut out = Vec::new();
    for (effect, side, set) in [
        ("reads", &n.reads, &declared.reads),
        ("writes", &n.writes, &declared.writes),
    ] {
        if let Some((block, why)) = &side.everything {
            if *set != EffectSet::Everything {
                out.push(error(
                    function,
                    effect,
                    *block,
                    &format!("{why}, which needs {effect}: Everything"),
                ));
            }
            continue;
        }
        for (place, (block, why)) in &side.places {
            if !set.covers(&EffectSet::Places(vec![*place])) {
                out.push(error(function, effect, *block, why));
            }
        }
    }
    for (effect, needed, allowed) in [
        ("allocates", &n.allocates, declared.allocates),
        ("frees", &n.frees, declared.frees),
        ("may_unwind", &n.may_unwind, declared.may_unwind),
        ("io", &n.io, declared.io),
    ] {
        if let Some((block, why)) = needed
            && !allowed
        {
            out.push(error(function, effect, *block, why));
        }
    }
    out
}

#[test]
fn ordinary_order_everything_suppression_and_singleton_membership_match() {
    let mut mixed = EffectSummary::pure();
    mixed.writes = EffectSet::Places(vec![g(2), p(7), g(2)]);
    mixed.frees = true;
    mixed.io = true;
    for (case, declared) in [EffectSummary::pure(), EffectSummary::top(), mixed]
        .into_iter()
        .enumerate()
    {
        let mut n = need();
        n.writes.everything = None;
        n.writes
            .places
            .insert(1, (p(7), (24, "second parameter".into())));
        let expected = ordinary(&n, "nameλ\0尾", &declared);
        let diagnostic = |effect, block, inst| error("nameλ\0尾", effect, block, inst);
        assert_eq!(
            expected,
            match case {
                0 => vec![
                    diagnostic(
                        "reads",
                        11,
                        "read everything λ\0, which needs reads: Everything"
                    ),
                    diagnostic("writes", 22, "write param"),
                    diagnostic("writes", 24, "second parameter"),
                    diagnostic("writes", 23, "write global"),
                    diagnostic("allocates", 31, "allocation"),
                    diagnostic("frees", 32, "free"),
                    diagnostic("may_unwind", 33, "unwind"),
                    diagnostic("io", 34, "io"),
                ],
                1 => vec![],
                2 => vec![
                    diagnostic(
                        "reads",
                        11,
                        "read everything λ\0, which needs reads: Everything"
                    ),
                    diagnostic("writes", 22, "write param"),
                    diagnostic("allocates", 31, "allocation"),
                    diagnostic("may_unwind", 33, "unwind"),
                ],
                _ => unreachable!("three explicit test cases"),
            }
        );
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        let actual = run(n, "nameλ\0尾", &declared, &mut w).unwrap();
        assert_eq!(actual, expected);
        assert!(!actual.iter().any(|e| matches!(e, ValidationError::EffectSummaryViolated { inst, .. } if inst == "suppressed read")));
        retire_validation_errors_observed(actual, w.session, w.site).unwrap();
        assert!(w.session.first_refusal().is_none());
    }
    for set in [
        EffectSet::Nothing,
        EffectSet::Everything,
        EffectSet::Places(vec![]),
        EffectSet::Places(vec![g(u32::MAX), p(7), p(7), g(0)]),
    ] {
        for place in [p(0), p(7), p(u32::MAX), g(0), g(u32::MAX)] {
            let expected = set.covers(&EffectSet::Places(vec![place]));
            let mut o = Observer::default();
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            let mut w = Work {
                session: &mut s,
                site: site(),
            };
            assert_eq!(covers_place(&set, place, &mut w).unwrap(), expected);
            assert!(w.session.first_refusal().is_none());
        }
    }
}

#[test]
fn sticky_cleanup_consumes_need_both_pending_slots_tail_name_and_prior_errors() {
    let mut r = full_state();
    check_need(r.need.as_ref().unwrap());
    assert_eq!(r.batch.as_ref().unwrap().len(), 2);
    assert_eq!(r.errors.len(), 2);
    let mut o = Observer {
        stop: Some(1),
        cleanup: true,
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let result = w.admit(1, 0);
    let first = w.session.first_refusal().unwrap().progress;
    assert_eq!(
        r.finish(result, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    drained(&r);
    assert_eq!(w.session.first_refusal().unwrap().progress, first);
    assert_eq!(
        w.session.first_refusal().unwrap().cause,
        "original effects stop"
    );
    drop(w);
    drop(s);
    assert!(o.events.len() > 50);
    assert!(
        o.events[1..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
    assert!(o.events[1..].iter().any(|e| e.work > 0));
    assert!(o.events[1..].iter().any(|e| e.work == 0));
    // Flat String retirement intentionally prices its header/drop, not a byte
    // walk. Empty retained fields plus the real complete cleanup path are tested.
}

#[test]
fn every_finish_callback_and_final_publication_refusal_drain_the_whole_state() {
    let mut r = full_state();
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let errors = r.finish(Ok(()), &mut w).unwrap();
    let bound = calls.get(); // Latched before caller-owned error disposal.
    drained(&r);
    assert_eq!(
        errors,
        vec![
            error("prior name λ", "io", 71, "prior full detail 尾"),
            error("second prior name", "frees", 72, "second prior detail λ")
        ]
    );
    retire_validation_errors_observed(errors, w.session, w.site).unwrap();
    drop(w);
    drop(s);
    let prefix = &base.events[..bound];
    assert_eq!(
        (
            prefix[bound - 1].phase,
            prefix[bound - 1].work,
            prefix[bound - 1].copy_bytes
        ),
        (
            ExecutionPhase::Publication,
            1,
            size_of::<Vec<ValidationError>>()
        )
    );
    for stop in 1..=bound {
        let mut r = full_state();
        let mut o = Observer {
            stop: Some(stop),
            cleanup: true,
            cleanup_after: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(
            r.finish(Ok(()), &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        drained(&r);
        assert_eq!(
            w.session.first_refusal().unwrap().progress,
            prefix[stop - 1]
        );
        assert_eq!(
            w.session.first_refusal().unwrap().cause,
            "original effects stop"
        );
        drop(w);
        drop(s);
        assert_eq!(&o.events[..stop], &prefix[..stop]);
        assert!(
            o.events[stop..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
    // Cumulative original work also refuses that actual outer publication,
    // rather than selecting a same-sized inner publication by global ordinal.
    let cap = prefix.iter().map(|e| e.work).sum::<usize>() - 1;
    let mut r = full_state();
    let mut o = Observer {
        cap: Some(cap),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert_eq!(
        r.finish(Ok(()), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    drained(&r);
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        prefix[bound - 1]
    );
    assert_eq!(w.session.first_refusal().unwrap().cause, "work");
}
