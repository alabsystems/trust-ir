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
    let catalog = ModuleFunctionCatalog::new(m);
    for cut in 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        assert_eq!(
            validate_weak_declaration_uses_observed(&catalog, &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original weak-use stop");
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
fn every_origin_signature_direct_switch_transport_and_publication_callback_refuses() {
    every(&fixture());
}
#[test]
fn every_last_name_lookup_and_late_unicode_comparison_callback_refuses() {
    let mut m = fixture();
    let name = "é🦀".repeat(200);
    m.functions[1].name = name.clone();
    m.functions[0].blocks[0].body = vec![
        definition(1, symbol(&name)),
        call(0, 1, 0, CallingConv::Rust),
    ];
    m.functions.push(weak(19, &name, 0));
    every(&m);
}
#[test]
fn every_deep_reverse_child_frame_and_nested_literal_callback_refuses() {
    let mut m = fixture();
    let mut c = symbol("weak");
    for _ in 0..8 {
        c = Constant::Record(vec![("field".into(), Constant::Array(vec![c]))]);
    }
    m.functions[0].blocks[0].body = vec![switch(vec![c])];
    every(&m);
}
#[test]
fn repeated_whole_passes_share_original_cumulative_work_and_copy_caps() {
    let m = fixture();
    let (_, base, end) = run(&m);
    let catalog = ModuleFunctionCatalog::new(&m);
    for copy in [false, true] {
        let cap = base.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer {
            work_cap: (!copy).then_some(cap),
            byte_cap: copy.then_some(cap),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out = validate_weak_declaration_uses_observed(&catalog, &mut s, site()).unwrap();
        assert_eq!(
            validate_weak_declaration_uses_observed(&catalog, &mut s, site()),
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
fn zero_instruction_fuel_does_not_renew_grant_or_replace_original_request_site() {
    let m = fixture();
    let catalog = ModuleFunctionCatalog::new(&m);
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let out = validate_weak_declaration_uses_observed(&catalog, &mut s, site()).unwrap();
    assert_eq!(out, original(&m));
    assert_eq!(s.remaining_fuel(), 0);
    retire_validation_errors_observed(out, &mut s, site()).unwrap();
    drop(s);
    assert!(o.events.iter().all(|e| e.site == site()));
}
#[test]
fn preexisting_refusal_stays_sticky_and_cannot_become_empty_success() {
    let m = fixture();
    let catalog = ModuleFunctionCatalog::new(&m);
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
        validate_weak_declaration_uses_observed(&catalog, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(s.first_refusal().unwrap().cause, "original weak-use stop");
}
