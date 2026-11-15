// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn exact_original_scope_order_ids_handle_diagnostics_and_structural_refuse_policies() {
    let (m, r) = fixture();
    let a = run(&m, &r, ImportPolicy::Structural).0;
    assert_eq!(a, run(&m, &r, ImportPolicy::Refuse).0);
    assert_eq!(a.len(), 2);
    assert!(
        matches!(&a[0], ValidationError::HandleForeignDeclaration { function:u32::MAX,name,handle,detail } if name==&m.functions[0].name && handle.contains("Second") && detail.contains("backed_by: ExternRef") && detail.contains("\\0"))
    );
    assert!(
        matches!(&a[1], ValidationError::HandleForeignDeclaration { function:7,detail,.. } if detail.contains("4294967295"))
    );
}
#[test]
fn missing_backing_refuses_even_in_authenticated_lane_and_missing_sealed_outcome_refuses() {
    let (m, r) = fixture();
    let auth = crate::linked::AuthenticatedImports::default();
    let out = run(&m, &r, ImportPolicy::Authenticated(&auth)).0;
    assert_eq!(out.len(), 2);
    assert!(
        matches!(&out[0],ValidationError::HandleForeignDeclaration {detail,..} if detail.starts_with("no `backed_by`"))
    );
    assert!(
        matches!(&out[1],ValidationError::HandleForeignDeclaration {detail,..} if detail=="its `backed_by` was not examined by the linked validator")
    );
}
#[test]
fn exact_debug_quoting_full_unicode_nul_apostrophes_and_long_names_are_preserved() {
    let (mut m, r) = fixture();
    m.functions.truncate(1);
    m.functions[0].name = "λ'\"\\\n\r\t\0\u{1}\u{7f}\u{301}尾".repeat(2049) + "TAIL";
    let out = run(&m, &r, ImportPolicy::Refuse).0;
    assert!(
        matches!(&out[..],[ValidationError::HandleForeignDeclaration {name,detail,..}] if name==&m.functions[0].name && detail.contains("TAIL") && detail.contains("λ'"))
    );
}
#[test]
fn actual_table_cycles_and_return_only_handles_keep_the_complete_closure() {
    let (mut m, r) = fixture();
    m.functions.truncate(1);
    m.types = vec![
        Ty::Array(TyId::new(1), 0),
        Ty::Tuple(vec![
            Ty::Array(TyId::new(0), 0),
            Ty::handle("Late", "rt::Late"),
        ]),
    ];
    m.func_types[0] = FuncTy::unrecorded(vec![Ty::Bool], vec![Ty::Array(TyId::new(0), 0)], false);
    let out = run(&m, &r, ImportPolicy::Refuse).0;
    assert!(
        matches!(&out[..],[ValidationError::HandleForeignDeclaration {handle,..}] if handle.contains("Late"))
    );
}
#[test]
fn defined_pinned_dangling_and_scalar_only_signatures_are_skipped_without_diagnostics() {
    let (mut m, r) = fixture();
    m.functions.drain(0..2);
    assert!(run(&m, &r, ImportPolicy::Refuse).0.is_empty());
    let empty = Module::new("");
    assert!(run(&empty, &r, ImportPolicy::Refuse).0.is_empty());
}
#[test]
fn structural_policy_ignores_unread_import_symbol_obligation_summary_and_entry_contract_payloads() {
    let (mut m, mut r) = fixture();
    let (_, before, begin, end) = run(&m, &r, ImportPolicy::Structural);
    m.functions[1]
        .summary
        .as_mut()
        .unwrap()
        .backed_by
        .as_mut()
        .unwrap()
        .symbol = "unread λ\0".repeat(5000);
    m.functions[1].summary.as_mut().unwrap().proved = true;
    r.pins[0].name = Box::leak("unread pin".repeat(4000).into_boxed_str());
    r.pins[0].runtime = "unread runtime";
    let (_, after, a, b) = run(&m, &r, ImportPolicy::Structural);
    assert_eq!(&before.events[begin..end], &after.events[a..b]);
}
