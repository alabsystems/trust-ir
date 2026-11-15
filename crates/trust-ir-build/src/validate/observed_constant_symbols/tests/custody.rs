// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
#![allow(
    clippy::drop_non_drop,
    reason = "observed-r23 lane code landed unwired (2026-10-19, Track L); docs/DECISIONS.md, observed-r23 landing"
)]
use super::*;
#[test]
fn byte_equal_foreign_layout_catalog_sources_are_rejected_before_publication() {
    let a = fixture();
    let b = a.clone();
    let layouts = a.layout_table();
    let functions = ModuleFunctionCatalog::new(&b);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    assert!(matches!(
        ObservedConstantSymbols::new_observed(&layouts, &functions, &mut s, site()),
        Err(ObservedValueError::InvalidRange)
    ));
    assert!(s.first_refusal().is_none());
    drop(s);
    assert_eq!(o.events.len(), 1);
    assert_eq!(o.events[0].phase, ExecutionPhase::Validation);
}
#[test]
fn context_and_returned_global_borrow_the_exact_original_source() {
    let m = fixture();
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(&m);
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let ctx = ObservedConstantSymbols::new_observed(&layouts, &functions, &mut s, site()).unwrap();
    assert!(core::ptr::eq(ctx.module(), &m));
    assert!(core::ptr::eq(ctx.layouts(), &layouts));
    assert!(core::ptr::eq(ctx.functions(), &functions));
    let global = ctx
        .target_global_observed("target", &mut s, site())
        .unwrap()
        .unwrap();
    assert!(core::ptr::eq(global, &m.globals[1]));
    ctx.retire_observed(&mut s, site()).unwrap();
    assert!(core::ptr::eq(global, &m.globals[1]));
    assert_eq!(global.name, "target");
}
#[test]
fn context_retirement_keeps_first_refusal_and_healthy_terminal_receipt() {
    let m = fixture();
    let layouts = m.layout_table();
    let functions = ModuleFunctionCatalog::new(&m);
    let mut baseline = Observer::default();
    let calls = baseline.calls.clone();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut baseline);
    let ctx = ObservedConstantSymbols::new_observed(&layouts, &functions, &mut s, site()).unwrap();
    let before = calls.get();
    ctx.retire_observed(&mut s, site()).unwrap();
    drop(s);
    let last = baseline.events.last().unwrap();
    assert_eq!(
        (last.phase, last.work, last.copy_bytes),
        (ExecutionPhase::Publication, 0, 0)
    );
    for cut in before + 1..=baseline.events.len() {
        let mut o = Observer {
            stop: Some(cut),
            ..Observer::default()
        };
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let ctx =
            ObservedConstantSymbols::new_observed(&layouts, &functions, &mut s, site()).unwrap();
        assert_eq!(
            ctx.retire_observed(&mut s, site()),
            Err(ObservedValueError::AdmissionRefused)
        );
        assert_eq!(s.first_refusal().unwrap().cause, "original symbol stop");
        drop(s);
        assert!(
            o.events[cut..]
                .iter()
                .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
        );
    }
}
#[test]
fn symbol_queries_do_not_claim_to_validate_or_clone_unread_initializer_bodies() {
    let a = fixture();
    let mut b = a.clone();
    b.globals[1].initializer = Some(Constant::Array(vec![
        Constant::SymbolAddr {
            symbol: "unread".repeat(500),
            addend: -7
        };
        100
    ]));
    let target = |m: &Module| {
        let layouts = m.layout_table();
        let functions = ModuleFunctionCatalog::new(m);
        let mut o = Observer::default();
        let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
        let ctx =
            ObservedConstantSymbols::new_observed(&layouts, &functions, &mut s, site()).unwrap();
        let g = ctx
            .target_global_observed("target", &mut s, site())
            .unwrap()
            .unwrap();
        assert!(core::ptr::eq(g, &m.globals[1]));
        ctx.retire_observed(&mut s, site()).unwrap();
        drop(s);
        o.events
    };
    assert_eq!(target(&a), target(&b));
}
