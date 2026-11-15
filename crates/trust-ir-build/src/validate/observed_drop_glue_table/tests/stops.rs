// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_original_public_callback_refuses_without_partial_row_diagnostics() {
    for m in [Module::new("empty"), multi()] {
        let (_, base, bound) = run(&m);
        for stop in 1..=bound {
            let mut o = Observer {
                stop: Some(stop),
                cleanup_after: Some(stop),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                validate_module_drop_glue_table_observed(&m, &mut s, site()),
                Err(ObservedValueError::AdmissionRefused)
            );
            assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
            assert_eq!(s.first_refusal().unwrap().cause, "original glue-table stop");
            drop(s);
            assert_eq!(&o.events[..stop], &base.events[..stop]);
            assert!(
                o.events[stop..]
                    .iter()
                    .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn original_work_and_copy_caps_stay_spent_after_whole_table_and_output_retirement() {
    let m = multi();
    let (_, base, _) = run(&m);
    for copy in [false, true] {
        let mut o = Observer {
            work_cap: (!copy).then_some(base.work),
            byte_cap: copy.then_some(base.bytes),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = validate_module_drop_glue_table_observed(&m, &mut s, site()).unwrap();
        retire_validation_errors_observed(out, &mut s, site()).unwrap();
        assert_eq!(
            validate_module_drop_glue_table_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        let first = s.first_refusal().unwrap().progress;
        assert_eq!(
            validate_module_drop_glue_table_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, first);
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
    }
}
#[test]
fn original_instruction_site_and_zero_fuel_cover_all_checks_and_cleanup() {
    let m = multi();
    let exact = ExecutionSite::Instruction(InstructionSite {
        function: FuncId::new(4),
        block: BlockId::new(5),
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
    let out = validate_module_drop_glue_table_observed(&m, &mut s, exact).unwrap();
    assert_eq!(out, oracle(&m));
    retire_validation_errors_observed(out, &mut s, exact).unwrap();
    assert_eq!(s.remaining_fuel(), 0);
    assert!(s.first_refusal().is_none());
    drop(s);
    assert!(o.events.iter().all(|e| e.site == exact));
}
#[test]
fn actual_final_outer_publication_refuses_both_empty_and_nonempty_results() {
    for m in [valid(), multi()] {
        let (_, base, bound) = run(&m);
        let mut o = Observer {
            stop: Some(bound),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_drop_glue_table_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[bound - 1]);
        assert_eq!(
            s.first_refusal().unwrap().progress.phase,
            ExecutionPhase::Publication
        );
    }
}
#[test]
fn every_actual_unique_lookup_callback_refuses_instead_of_accepting_missing_or_first_match() {
    let mut m = module();
    m.functions = (0..28)
        .map(|i| function(100 + i, "unrelated", true))
        .collect();
    m.functions.push(function(7, "last physical", true));
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    let found = w.unique(&m, FuncId::new(7)).unwrap().unwrap();
    assert!(std::ptr::eq(found, m.functions.last().unwrap()));
    drop(w);
    drop(s);
    for stop in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert!(matches!(
            w.unique(&m, FuncId::new(7)),
            Err(ObservedValueError::AdmissionRefused)
        ));
        assert_eq!(
            w.session.first_refusal().unwrap().progress,
            base.events[stop - 1]
        );
    }
    m.functions
        .insert(0, function(7, "earlier duplicate", true));
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert!(w.unique(&m, FuncId::new(7)).unwrap().is_none());
}
#[test]
fn deep_actual_type_key_comparison_stops_never_become_a_smaller_valid_table() {
    let mut m = module();
    let stem = "λ".repeat(96);
    for (id, tail) in [(7, "TAIL"), (8, "FAIL")] {
        m.functions.push(function(id, "glue", true));
        add(&mut m, id, Ty::handle(&(stem.clone() + tail), "runtime"));
    }
    let (out, base, bound) = run(&m);
    assert!(out.is_empty());
    // Every callback in this exact real two-key pass includes the actual
    // structural comparison interior, without guessing an ABI-sized event.
    for stop in 1..=bound {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_module_drop_glue_table_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().progress, base.events[stop - 1]);
    }
}
#[test]
fn every_real_pinned_symbol_byte_comparison_callback_can_refuse_without_false_membership() {
    let symbol = TRUSTED_RC_RUNTIMES[0].entry_points[0].symbol;
    assert!(symbol.len() > 2);
    let mut base = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut base);
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    assert!(w.pinned(symbol).unwrap());
    drop(w);
    drop(s);
    // Narrow identical pinned() entry sweeps each actual byte header/read,
    // increment and publication; no global same-size selector is involved.
    for stop in 1..=base.events.len() {
        let mut o = Observer {
            stop: Some(stop),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let mut w = Work {
            session: &mut s,
            site: site(),
        };
        assert_eq!(w.pinned(symbol), Err(ObservedValueError::AdmissionRefused));
        assert_eq!(
            w.session.first_refusal().unwrap().progress,
            base.events[stop - 1]
        );
        assert_eq!(
            w.session.first_refusal().unwrap().cause,
            "original glue-table stop"
        );
    }
}
