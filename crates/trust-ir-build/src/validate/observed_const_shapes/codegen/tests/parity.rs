// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn real_public_front_checks_only_actual_cases_not_global_or_const_literals() {
    let m = fixture();
    let (out, _, _) = run(&m);
    assert!(!out.is_empty());
    assert!(out.iter().all(|e|matches!(e,ValidationError::ConstTypeMismatch{location,..}if location.contains("switch case"))));
    assert!(
        crate::codegen_switch_case_literal_errors(&m).len()
            < super::super::super::super::validate_const_shapes(
                &m.layout_table(),
                &ModuleFunctionCatalog::new(&m),
                None
            )
            .len()
    );
}
#[test]
fn sparse_unique_direct_results_and_duplicate_id_skips_match_original_catalog() {
    for duplicate in [false, true] {
        let mut m = fixture();
        m.functions[0].blocks[0].params.clear();
        m.functions[0].blocks[0].body = vec![
            InstrNode::new(Inst::Call {
                callee: FuncId::new(900),
                args: vec![],
            })
            .with_result(v(2)),
            switch(v(2), vec![Constant::Int(300)]),
        ];
        if duplicate {
            let f = m.functions[1].clone();
            m.functions.push(f);
        }
        let (out, _, _) = run(&m);
        assert_eq!(out.len(), usize::from(!duplicate));
    }
}
#[test]
fn exactly_one_refine_unwrap_and_missing_noninteger_selectors_keep_local_skip() {
    for ty in [
        Ty::Refine(TyId::new(0), PredId::new(0)),
        Ty::Refine(TyId::new(1), PredId::new(0)),
        Ty::Refine(TyId::new(999), PredId::new(0)),
        Ty::Bool,
    ] {
        let mut m = fixture();
        m.types.push(Ty::Refine(TyId::new(0), PredId::new(0)));
        m.functions[0].blocks[0].params = vec![(v(0), ty.clone())];
        m.functions[0].blocks[0].body = vec![
            switch(v(0), vec![Constant::Int(300)]),
            switch(v(99), vec![Constant::U128(1)]),
        ];
        let (out, _, _) = run(&m);
        assert_eq!(
            out.len(),
            usize::from(ty == Ty::Refine(TyId::new(0), PredId::new(0)))
        );
    }
}
#[test]
fn all_integer_and_char_carriers_keep_canonical_before_typed_case_errors() {
    for ty in [
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::Isize,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::U128,
        Ty::Usize,
        Ty::Char,
    ] {
        let mut m = fixture();
        m.functions[0].blocks[0].params = vec![(v(0), ty)];
        m.functions[0].blocks[0].body = vec![switch(v(0), vec![Constant::U128(1)])];
        let (out, _, _) = run(&m);
        assert!(
            matches!(&out[0],ValidationError::ConstTypeMismatch{expected,..}if expected.starts_with("canonical integer spelling"))
        );
    }
}
#[test]
fn lazy_maps_are_function_scoped_and_case_locations_preserve_full_unicode_order() {
    let mut m = fixture();
    m.functions[0].name = "é🦀".repeat(200);
    let mut second = m.functions[0].clone();
    second.id = FuncId::new(100);
    second.name = "second".into();
    second.blocks[0].params = vec![(v(0), Ty::Bool)];
    second.blocks[0].body = vec![switch(v(0), vec![Constant::U128(1)])];
    m.functions.push(second);
    let (out, _, _) = run(&m);
    assert!(out.iter().all(|e|matches!(e,ValidationError::ConstTypeMismatch{location,..}if location.starts_with(&format!("function '{}' bb7",m.functions[0].name)))));
}
#[test]
fn no_switch_still_builds_actual_catalog_once_and_returns_only_empty_diagnostics() {
    let mut m = fixture();
    m.functions[0].blocks[0].body.truncate(1);
    let (out, o, end) = run(&m);
    assert!(out.is_empty());
    let visits: Vec<_> = o.events[..end]
        .iter()
        .filter(|e| e.phase == ExecutionPhase::ModuleLookup && e.site != site())
        .map(|e| e.site)
        .collect();
    assert_eq!(
        visits,
        m.functions
            .iter()
            .map(|f| ExecutionSite::Entry(f.id))
            .collect::<Vec<_>>()
    );
}
