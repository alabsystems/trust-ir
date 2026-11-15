// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn every(m: &Module) {
    let (_, baseline, end) = run(m);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_closure_purity_observed(m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original closure-purity stop"
        );
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn every_actual_proof_signature_capture_type_string_and_publication_callback_refuses() {
    every(&fixture());
    every(&rich());
}
#[test]
fn actual_result_reader_refuses_every_lookup_row_reserve_plan_retirement_and_publication() {
    let m = fixture();
    let n = node(
        Inst::Call {
            callee: FuncId::new(9),
            args: vec![],
        },
        &[10],
    );
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let out = module_closure_results_observed(&m, &n, &mut s, site()).unwrap();
    let end = calls.get();
    Work {
        session: &mut s,
        site: site(),
    }
    .rows(out);
    drop(s);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            module_closure_results_observed(&m, &n, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original closure-purity stop"
        );
        drop(s);
        assert_eq!(&o.events[..cut], &baseline.events[..cut]);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn repeated_module_walks_preserve_both_original_cumulative_work_and_copy_caps() {
    let m = fixture();
    let (_, baseline, end) = run(&m);
    for copy in [false, true] {
        let cap = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer::default();
        if copy {
            o.byte_cap = Some(cap)
        } else {
            o.work_cap = Some(cap)
        }
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = validate_closure_purity_observed(&m, &mut s, site()).unwrap();
        assert_eq!(
            validate_closure_purity_observed(&m, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            if copy { "copy" } else { "work" }
        );
        let _ = retire_validation_errors_observed(out, &mut s, site());
    }
}
#[test]
fn zero_instruction_fuel_and_preexisting_stop_keep_original_owner_and_request_site() {
    let m = fixture();
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let out = validate_closure_purity_observed(&m, &mut s, site()).unwrap();
    assert_eq!(out, validate_closure_purity(&m));
    assert_eq!(s.remaining_fuel(), 0);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    drop(s);
    let mut o = Observer {
        stop: Some(1),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Validation,
            site: site(),
            work: 1,
            copy_bytes: 0
        })
        .is_err()
    );
    assert_eq!(
        validate_closure_purity_observed(&m, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original closure-purity stop"
    );
}
#[test]
fn late_actual_function_fallback_and_capture_proof_rows_are_observed() {
    let mut m = fixture();
    let target = m.functions.pop().unwrap();
    for i in 100..116 {
        m.functions.push(Function::new(
            FuncId::new(i),
            "unused",
            FuncTyId::new(0),
            BlockId::new(0),
        ));
    }
    m.functions.push(target);
    m.functions[0].proofs = vec![ProofAnnotation::Terminates; 19];
    m.functions[0].proofs.push(ProofAnnotation::Pure);
    m.closure_types[1].captures = vec![Ty::Bool; 23];
    m.closure_types[1].captures.push(Ty::Rc(Box::new(Ty::Bool)));
    m.functions[0].blocks[0].body[0] = node(
        Inst::Call {
            callee: FuncId::new(9),
            args: vec![],
        },
        &[],
    );
    every(&m);
}
#[test]
fn unrelated_deep_result_payloads_are_not_cloned_or_credited_as_observed_type_validation() {
    let mut traces = Vec::new();
    for ty in [
        Ty::Bool,
        Ty::Tuple(vec![Ty::handle("unread", "rt::unread"); 500]),
    ] {
        let mut m = fixture();
        m.functions[0].proofs.clear();
        m.functions[0].blocks[0].body[0] = node(Inst::Undef { ty }, &[]);
        let (e, o, end) = run(&m);
        assert!(e.is_empty());
        traces.push(o.events[..end].to_vec());
    }
    assert_eq!(traces[0], traces[1]);
}
