#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn every_actual_public_callback_refuses_outer_result_and_keeps_original_fields() {
    let m = fixture();
    let c = ModuleFunctionCatalog::new(&m);
    for mode in [Mode::Unbound, Mode::Source] {
        let (good, end) = run(&m, mode);
        for cut in 1..=end {
            let mut o = Observer {
                stop: Some(cut),
                ..Observer::default()
            };
            let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
            assert_eq!(
                call(&m, &c, mode, &mut s),
                Err(ObservedValueError::AdmissionRefused)
            );
            let first = s.first_refusal().unwrap();
            assert_eq!(
                (first.progress, first.cause),
                (good.events[cut - 1], "unbound stop")
            );
            drop(s);
            assert!(
                o.events[cut..]
                    .iter()
                    .all(|p| p.phase == ExecutionPhase::ScratchRetirement)
            );
        }
    }
}
#[test]
fn exact_full_work_and_one_less_use_cumulative_not_individual_receipt_limits() {
    let m = fixture();
    let c = ModuleFunctionCatalog::new(&m);
    let (good, end) = run(&m, Mode::Source);
    let cap: usize = good.events[..end].iter().map(|p| p.work).sum();
    for limit in [cap, cap - 1] {
        let mut o = Observer {
            work_cap: Some(limit),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let result = call(&m, &c, Mode::Source, &mut s);
        if limit == cap {
            let out = result.unwrap();
            retire_validation_errors_observed(out, &mut s, site()).unwrap_err();
        } else {
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
            assert!(s.first_refusal().is_some());
        }
    }
}
#[test]
fn exact_full_copy_and_one_less_withhold_the_whole_diagnostic_batch() {
    let m = fixture();
    let c = ModuleFunctionCatalog::new(&m);
    let (good, end) = run(&m, Mode::Source);
    let cap: usize = good.events[..end].iter().map(|p| p.copy_bytes).sum();
    for limit in [cap, cap - 1] {
        let mut o = Observer {
            copy_cap: Some(limit),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let result = call(&m, &c, Mode::Source, &mut s);
        if limit == cap {
            let out = result.unwrap();
            let _ = retire_validation_errors_observed(out, &mut s, site());
        } else {
            assert_eq!(result, Err(ObservedValueError::AdmissionRefused));
            assert!(s.first_refusal().is_some());
        }
    }
}
#[test]
fn actual_prior_debit_and_retry_keep_one_session_without_restoring_spend() {
    let m = fixture();
    let c = ModuleFunctionCatalog::new(&m);
    let (good, end) = run(&m, Mode::Source);
    let work = good.events[..end].iter().map(|p| p.work).sum::<usize>();
    let copy = good.events[..end]
        .iter()
        .map(|p| p.copy_bytes)
        .sum::<usize>();
    let mut o = Observer {
        work_cap: Some(work + 11),
        copy_cap: Some(copy + 17),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    s.admit(ExecutionProgress {
        phase: ExecutionPhase::Validation,
        site: site(),
        work: 11,
        copy_bytes: 17,
    })
    .unwrap();
    let out = call(&m, &c, Mode::Source, &mut s).unwrap();
    assert_eq!(
        call(&m, &c, Mode::Source, &mut s),
        Err(ObservedValueError::AdmissionRefused)
    );
    let first = s.first_refusal().unwrap();
    let saved = (first.progress, first.cause);
    let _ = retire_validation_errors_observed(out, &mut s, site());
    assert_eq!(
        (
            s.first_refusal().unwrap().progress,
            s.first_refusal().unwrap().cause
        ),
        saved
    );
}
#[test]
fn zero_caps_stop_before_the_child_while_instruction_fuel_is_never_renewed() {
    let m = fixture();
    let c = ModuleFunctionCatalog::new(&m);
    for copy in [false, true] {
        let mut o = Observer {
            work_cap: if copy { None } else { Some(0) },
            copy_cap: if copy { Some(0) } else { None },
            ..Observer::default()
        };
        let mut s = ObservedSession::new(
            InterpretOptions {
                fuel: 0,
                ..InterpretOptions::default()
            },
            &mut o,
        );
        assert_eq!(
            call(&m, &c, Mode::Source, &mut s),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.remaining_fuel(), 0);
        drop(s);
        assert_eq!(o.events.len(), 1);
    }
}
#[test]
fn first_original_cause_and_progress_survive_a_later_leaf_attempt() {
    let m = fixture();
    let c = ModuleFunctionCatalog::new(&m);
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let p = ExecutionProgress {
        phase: ExecutionPhase::AbiScan,
        site: ExecutionSite::Entry(FuncId::new(999)),
        work: 7,
        copy_bytes: 11,
    };
    assert!(s.admit(p).is_err());
    assert_eq!(
        call(&m, &c, Mode::Source, &mut s),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().progress, p);
    drop(s);
    assert_eq!(o.events, vec![p]);
}
