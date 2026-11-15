// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn prepared<'m, 'f>(
    m: &'m Module,
    f: &'f Function,
    s: &mut ObservedSession<'_, Observer>,
) -> Analysis<'m, 'f> {
    Analysis {
        module: m,
        policy: ImportPolicy::Structural,
        body: Some(ObservedBody::new_observed(f, s, site()).unwrap()),
        need: Some(ObservedNeed::new_observed(s, site()).unwrap()),
        roots: None,
    }
}
fn finish(a: &mut Analysis<'_, '_>, s: &mut ObservedSession<'_, Observer>) {
    let mut w = Work {
        session: s,
        site: site(),
    };
    a.retire_roots(&mut w);
    a.retire_body(&mut w);
    a.retire_need(&mut w);
    assert!(a.roots.is_none() && a.body.is_none() && a.need.is_none());
}
#[test]
fn first_reader_stop_after_the_real_roots_return_retires_the_complete_child_set() {
    let select = |a, b| Inst::Select {
        ty: Ty::Ptr,
        cond: v(2),
        then_val: v(a),
        else_val: v(b),
    };
    let (m, f) = fixture(vec![
        node(alloca(), &[3]),
        node(
            Inst::GlobalAddr {
                global: GlobalId::new(9),
            },
            &[4],
        ),
        node(select(1, 3), &[5]),
        node(select(4, 5), &[6]),
        node(select(6, 99), &[7]),
    ]);
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut a = prepared(&m, &f, &mut s);
    let begin = calls.get();
    a.access(
        Side::Read,
        v(7),
        0,
        What::Instruction("load"),
        &mut Work {
            session: &mut s,
            site: site(),
        },
    )
    .unwrap();
    finish(&mut a, &mut s);
    drop(s);
    let cuts = base.events[begin..]
        .windows(2)
        .enumerate()
        .filter(|(_, pair)| {
            pair[0].phase == ExecutionPhase::Publication
                && pair[0].work == 1
                && pair[0].copy_bytes == size_of::<ObservedRoots>()
                && pair[1].phase == ExecutionPhase::Validation
                && pair[1].work == 1
                && pair[1].copy_bytes == size_of::<Option<Root>>()
        })
        .map(|(i, _)| begin + i + 2)
        .collect::<Vec<_>>();
    assert_eq!(cuts.len(), 1);
    let stop = cuts[0];
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let calls = o.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut a = prepared(&m, &f, &mut s);
    assert_eq!(
        a.access(
            Side::Read,
            v(7),
            0,
            What::Instruction("load"),
            &mut Work {
                session: &mut s,
                site: site()
            }
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    let end = calls.get();
    assert!(a.roots.is_none());
    assert!(a.body.is_some() && a.need.is_some());
    assert!(a.need.as_ref().unwrap().reads.places.is_empty());
    finish(&mut a, &mut s);
    assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
    drop(s);
    let count = super::super::super::Body::new(&f).roots(v(7)).len();
    assert_eq!(count, 4);
    let expected = size_of::<Option<ObservedRoots>>()
        + 1
        + (count + 1) * (size_of::<Option<Root>>() + 1)
        + count * (size_of::<Root>() + 1)
        + size_of::<Vec<Root>>()
        + 1;
    assert_eq!(
        o.events[stop..end].iter().map(|e| e.work).sum::<usize>(),
        expected
    );
    assert!(
        o.events[stop..end]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
#[test]
fn refusal_starting_a_later_access_keeps_the_prior_complete_need_reason_until_cleanup() {
    let (m, f) = fixture(vec![]);
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut a = prepared(&m, &f, &mut s);
    a.access(
        Side::Read,
        v(1),
        7,
        What::Instruction("load"),
        &mut Work {
            session: &mut s,
            site: site(),
        },
    )
    .unwrap();
    let stop = calls.get() + 1;
    a.access(
        Side::Read,
        v(99),
        8,
        What::Instruction("load"),
        &mut Work {
            session: &mut s,
            site: site(),
        },
    )
    .unwrap();
    finish(&mut a, &mut s);
    drop(s);
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut a = prepared(&m, &f, &mut s);
    a.access(
        Side::Read,
        v(1),
        7,
        What::Instruction("load"),
        &mut Work {
            session: &mut s,
            site: site(),
        },
    )
    .unwrap();
    assert_eq!(
        a.access(
            Side::Read,
            v(99),
            8,
            What::Instruction("load"),
            &mut Work {
                session: &mut s,
                site: site()
            }
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        a.need.as_ref().unwrap().reads.places,
        [(p(0), (7, "load through *param0".to_string()))]
    );
    assert!(a.roots.is_none());
    finish(&mut a, &mut s);
}
#[test]
fn refused_last_top_publication_retains_all_six_full_owned_first_reasons() {
    let (m, f) = fixture(vec![]);
    let pieces = [Piece::Text("fullwhyλ\0TAIL")];
    let mut base = Observer::default();
    let calls = base.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut a = prepared(&m, &f, &mut s);
    a.top(
        u32::MAX,
        &pieces,
        &mut Work {
            session: &mut s,
            site: site(),
        },
    )
    .unwrap();
    let stop = calls.get();
    finish(&mut a, &mut s);
    drop(s);
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut a = prepared(&m, &f, &mut s);
    assert_eq!(
        a.top(
            u32::MAX,
            &pieces,
            &mut Work {
                session: &mut s,
                site: site()
            }
        ),
        Err(ObservedValueError::AdmissionRefused)
    );
    let n = a.need.as_ref().unwrap();
    for reason in [
        &n.reads.everything,
        &n.writes.everything,
        &n.allocates,
        &n.frees,
        &n.may_unwind,
        &n.io,
    ] {
        assert_eq!(
            reason.as_ref(),
            Some(&(u32::MAX, "fullwhyλ\0TAIL".to_string()))
        );
    }
    finish(&mut a, &mut s);
    assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
}
#[test]
fn long_raw_function_global_and_callee_text_reaches_whole_diagnostics_without_truncation() {
    let (mut m, mut f) = fixture(vec![
        node(
            Inst::GlobalAddr {
                global: GlobalId::new(0),
            },
            &[9],
        ),
        node(load(9), &[]),
        node(
            Inst::Call {
                callee: FuncId::new(7),
                args: vec![],
            },
            &[],
        ),
    ]);
    f.name = "functionλ\0".repeat(2000) + "FUNCTIONTAIL";
    m.functions[0] = f.clone();
    m.globals.push(trust_ir::Global {
        name: "globalλ\0".repeat(2000) + "GLOBALTAIL",
        ty: Ty::U8,
        mutable: false,
        initializer: None,
        linkage: trust_ir::Linkage::External,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    });
    callee(&mut m, 7, EffectSummary::pure(), true);
    m.functions[1].name = "calleeλ\0".repeat(2000) + "CALLEETAIL";
    let mut only_global = f.clone();
    only_global.blocks[0].body.pop();
    let global_out = run(&m, &only_global, ImportPolicy::Structural).0;
    assert_eq!(global_out.len(), 1);
    assert!(
        matches!(&global_out[0],ValidationError::EffectSummaryViolated {function,inst,..} if function==&f.name && inst==&(String::from("load through @")+&m.globals[0].name))
    );
    let out = run(&m, &f, ImportPolicy::Structural).0;
    assert_eq!(out.len(), 6);
    assert!(out.iter().all(
        |e| matches!(e,ValidationError::EffectSummaryViolated {function,..} if function==&f.name)
    ));
    assert!(
        matches!(&out[5],ValidationError::EffectSummaryViolated {inst,..} if inst.contains("CALLEETAIL, which has no admissible effect summary (havoc)"))
    );
}
