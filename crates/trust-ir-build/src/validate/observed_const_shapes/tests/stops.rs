// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    clippy::field_reassign_with_default,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
fn every(m: &Module, nominal: bool) {
    let (_, baseline, begin, end) = run(m, nominal);
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(m);
    for cut in begin + 1..=end {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let summary = setup(m, nominal, &mut s);
        assert_eq!(
            validate_const_shapes_observed(&layouts, &functions, summary.as_ref(), &mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(
            s.first_refusal().unwrap().cause,
            "original const-shapes stop"
        );
        if let Some(summary) = summary {
            let _ = summary.retire_observed(&mut s, site());
        }
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
fn every_original_context_canonical_typed_child_merge_and_publication_callback_refuses() {
    every(&fixture(), false);
}
#[test]
fn every_nominal_storage_handle_before_dialect_query_and_diagnostic_callback_refuses() {
    let mut m = Module::new("");
    m.globals = vec![
        global("H", Ty::handle("H", "rt::H"), None),
        global(
            "D",
            Ty::Dialect(Box::new(trust_ir::DialectTy::new("d", "T", 1))),
            None,
        ),
    ];
    every(&m, true);
}
#[test]
fn every_lazy_selector_map_catalog_refinement_and_case_callback_refuses() {
    let mut m = fixture();
    m.globals.clear();
    m.functions[0].blocks[0].params.clear();
    m.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::Call {
            callee: FuncId::new(900),
            args: vec![],
        })
        .with_result(v(1)),
        switch(v(1), vec![Constant::Int(300)]),
    ];
    every(&m, false);
}
#[test]
fn repeated_whole_passes_share_original_cumulative_work_and_copy_caps() {
    let m = fixture();
    let (_, baseline, _, end) = run(&m, false);
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(&m);
    for copy in [false, true] {
        let cap = baseline.events[..end]
            .iter()
            .map(|e| if copy { e.copy_bytes } else { e.work })
            .sum();
        let mut o = Observer {
            work_cap: (!copy).then_some(cap),
            byte_cap: copy.then_some(cap),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let out =
            validate_const_shapes_observed(&layouts, &functions, None, &mut s, site()).unwrap();
        assert_eq!(
            validate_const_shapes_observed(&layouts, &functions, None, &mut s, site()),
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
fn zero_instruction_fuel_and_existing_stop_keep_original_grant_and_site() {
    let m = fixture();
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(&m);
    let mut o = Observer::default();
    let mut options = InterpretOptions::default();
    options.fuel = 0;
    let mut s = ObservedSession::new(options, &mut o);
    let out = validate_const_shapes_observed(&layouts, &functions, None, &mut s, site()).unwrap();
    assert_eq!(out, original(&m, false));
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
        validate_const_shapes_observed(&layouts, &functions, None, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original const-shapes stop"
    );
}
#[test]
fn long_complete_diagnostic_transports_remain_interruption_points() {
    let mut m = fixture();
    m.functions.clear();
    m.globals[0].name = "é🦀".repeat(300);
    let (_, o, begin, end) = run(&m, false);
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(&m);
    let late = o.events[begin..end]
        .iter()
        .enumerate()
        .filter(|(_, e)| e.phase == ExecutionPhase::Validation && e.work >= 1024)
        .map(|(n, _)| begin + n + 1)
        .next_back()
        .unwrap();
    let mut o = Observer {
        stop: Some(late),
        ..Observer::default()
    };
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert_eq!(
        validate_const_shapes_observed(&layouts, &functions, None, &mut s, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(
        s.first_refusal().unwrap().cause,
        "original const-shapes stop"
    );
}
