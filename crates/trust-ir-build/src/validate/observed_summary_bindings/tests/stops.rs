// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_public_callback_refuses_without_publishing_partial_binding_diagnostics() {
    let (m, f, s) = bad();
    let (_, base) = run(&m, &f, &s);
    for stop in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_function_summary_bindings_observed(&m, &f, &s, &mut owner, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            owner.first_refusal().unwrap().progress,
            base.events[stop - 1]
        );
        assert_eq!(
            owner.first_refusal().unwrap().cause,
            "original binding stop"
        );
        assert!(
            o.events
                .iter()
                .skip(stop)
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn work_and_logical_copy_caps_cumulate_without_regrant_or_fuel_reset() {
    let (m, f, s) = bad();
    let (_, base) = run(&m, &f, &s);
    for bytes in [false, true] {
        let mut o = Observer {
            work_cap: (!bytes).then_some(base.work),
            byte_cap: bytes.then_some(base.bytes),
            ..Observer::default()
        };
        let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
        validate_function_summary_bindings_observed(&m, &f, &s, &mut owner, site()).unwrap();
        assert_eq!(
            validate_function_summary_bindings_observed(&m, &f, &s, &mut owner, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = owner.first_refusal().unwrap().progress;
        assert_eq!(
            validate_function_summary_bindings_observed(&m, &f, &s, &mut owner, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(owner.first_refusal().unwrap().progress, first);
        assert_eq!(owner.remaining_fuel(), InterpretOptions::default().fuel);
    }
}
#[test]
fn actual_defined_value_scan_stops_interior_after_an_early_found_definition() {
    let (m, mut f, mut s) = fixture();
    for id in 100..1200 {
        f.blocks[0].params.push((v(id), Ty::U32));
    }
    s.requires
        .push(clause(ClauseSort::Int, ClausePlace::Value(v(4))));
    let base = raw_trace(&m, &f, &s);
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<Option<&(ValueId, Ty)>>()
        })
        .nth(200)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut owner,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.walk(&m, &f, &s, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.values.is_none());
    assert!(state.errors.is_empty());
    assert_eq!(
        state.finish(Err(ObservedValueError::AdmissionRefused), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
#[test]
fn repeated_raw_name_lookup_can_stop_inside_a_long_actual_duplicate_comparison() {
    let (m, f, mut s) = fixture();
    let mut c = clause(ClauseSort::Bool, ClausePlace::WorldPre);
    c.bindings[0].0 = "λ".repeat(2000) + "TAIL";
    c.bindings.push(c.bindings[0].clone());
    s.requires.push(c);
    let base = raw_trace(&m, &f, &s);
    let stop = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation && e.work == 1024 && e.copy_bytes == 0
        })
        .nth(1)
        .unwrap()
        .0
        + 1;
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut owner,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.walk(&m, &f, &s, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.errors.is_empty());
    assert_eq!(state.detail.capacity(), 0);
    assert_eq!(
        state.finish(Err(ObservedValueError::AdmissionRefused), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
}
#[test]
fn complete_returned_ssa_map_is_held_before_the_first_fallible_post_return_lookup() {
    let (m, f, mut s) = fixture();
    s.requires
        .push(clause(ClauseSort::Int, ClausePlace::Value(v(4))));
    // The required borrow-result child also publishes a Vec-sized result.
    // Track the LAST matching publication only DURING this identical private
    // walk, then latch the seam before finish can publish the outer Vec.
    struct WalkObserver<'a> {
        inner: Observer,
        last_map_sized_publication: &'a Cell<usize>,
    }
    impl ExecutionObserver for WalkObserver<'_> {
        type Refusal = &'static str;
        fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
            let result = self.inner.admit(event);
            if event.phase == ExecutionPhase::Publication
                && event.copy_bytes == size_of::<ObservedValueTypes>()
            {
                self.last_map_sized_publication.set(self.inner.events.len());
            }
            result
        }
    }
    let last = Cell::new(0);
    let mut baseline = WalkObserver {
        inner: Observer::default(),
        last_map_sized_publication: &last,
    };
    let mut original = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let mut baseline_work = Work {
        session: &mut original,
        site: site(),
    };
    let mut held = State::default();
    held.walk(&m, &f, &s, &mut baseline_work).unwrap();
    assert!(held.values.is_some() && held.errors.is_empty());
    // For this successful Int/Value fixture there is no diagnostic String;
    // get_observed publishes Option<&Ty>, then the scalar check publishes bool.
    // Thus the final map-sized publication WITHIN walk is the actual whole map.
    assert!(last.get() > 0);
    let stop = last.get() + 1;
    held.finish(Ok(()), &mut baseline_work).unwrap();
    assert!(empty(&held));
    drop(baseline_work);
    drop(original);
    let base = baseline.inner;
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut owner,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.walk(&m, &f, &s, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(state.values.is_some());
    assert!(state.errors.is_empty());
    assert_eq!(
        state.finish(Err(ObservedValueError::AdmissionRefused), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    assert_eq!(
        w.session.first_refusal().unwrap().progress,
        base.events[stop - 1]
    );
}
#[test]
fn complete_sort_debug_string_is_held_before_its_first_diagnostic_copy_can_refuse() {
    let (m, f, mut s) = fixture();
    let sort = ClauseSort::Datatype {
        name: "λ".repeat(1500) + "TAIL",
        constructors: vec![],
    };
    s.requires
        .push(clause(sort.clone(), ClausePlace::Param { index: 0 }));
    let base = raw_trace(&m, &f, &s);
    let published = base
        .events
        .iter()
        .position(|e| e.phase == ExecutionPhase::Publication && e.copy_bytes == size_of::<String>())
        .unwrap();
    let stop = published + 2;
    let mut o = Observer {
        stop: Some(stop),
        ..Observer::default()
    };
    let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut owner,
        site: site(),
    };
    let mut state = State::default();
    assert_eq!(
        state.walk(&m, &f, &s, &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(state.render.as_deref(), Some(format!("{sort:?}").as_str()));
    assert_eq!(state.detail, "requires clause 0 binding 'x' has sort ");
    assert!(state.errors.is_empty());
    assert_eq!(
        state.finish(Err(ObservedValueError::AdmissionRefused), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
}
#[test]
fn complete_detail_is_retained_at_distinct_output_reserve_and_header_admissions() {
    let (m, f, s) = bad();
    let base = raw_trace(&m, &f, &s);
    let cuts = base
        .events
        .iter()
        .enumerate()
        .filter(|(_, e)| {
            e.phase == ExecutionPhase::Validation
                && e.work == 1
                && e.copy_bytes == size_of::<ValidationError>()
        })
        .map(|(i, _)| i + 1)
        .collect::<Vec<_>>();
    assert_eq!(cuts.len(), 2);
    for (index, stop) in cuts.into_iter().enumerate() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut owner,
            site: site(),
        };
        let mut state = State::default();
        assert_eq!(
            state.walk(&m, &f, &s, &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        let expected = oracle::oracle(&m, &f, &s);
        assert!(
            matches!(&expected[0],ValidationError::InvalidFunctionSummary {detail,..} if *detail==state.detail)
        );
        assert!(state.render.is_none());
        assert_eq!(state.errors.capacity() == 0, index == 0);
        assert_eq!(
            state.finish(Err(ObservedValueError::AdmissionRefused), &mut w),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert!(empty(&state));
    }
}
#[test]
fn sticky_cleanup_drains_real_map_pending_render_detail_and_prior_output() {
    let (m, f, mut s) = fixture();
    s.requires
        .push(clause(ClauseSort::Bool, ClausePlace::Value(v(4))));
    let arm = Rc::new(Cell::new(false));
    let mut o = Observer {
        cleanup: Some(arm.clone()),
        ..Observer::default()
    };
    let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut owner,
        site: site(),
    };
    let mut state = State::default();
    state.walk(&m, &f, &s, &mut w).unwrap();
    assert!(state.values.is_some());
    assert_eq!(state.errors.len(), 1);
    state.detail = "partial".repeat(1000);
    state.render = Some("render".repeat(1000));
    arm.set(true);
    assert_eq!(
        state.finish(Ok(()), &mut w),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert!(empty(&state));
    assert_eq!(w.session.first_refusal().unwrap().cause, "cleanup");
}
#[test]
fn first_header_refusal_and_exact_instruction_site_keep_zero_original_fuel() {
    let (m, f, s) = bad();
    let mut o = Observer {
        byte_cap: Some(0),
        ..Observer::default()
    };
    let mut owner = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_function_summary_bindings_observed(&m, &f, &s, &mut owner, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(o.events.len(), 1);
    let exact = ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(7),
        block: BlockId::new(8),
        instruction_index: usize::MAX,
    });
    let mut o = Observer::default();
    let mut owner = ObservedSession::new(
        InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        },
        &mut o,
    );
    assert_eq!(
        validate_function_summary_bindings_observed(&m, &f, &s, &mut owner, exact).unwrap(),
        oracle::oracle(&m, &f, &s)
    );
    assert_eq!(owner.remaining_fuel(), 0);
    assert!(o.events.iter().all(|e| e.site == exact));
}
