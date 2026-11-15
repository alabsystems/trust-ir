// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn all_original_error_reasons_and_physical_attribute_order_are_retained() {
    let out = run(&fixture()).0;
    let reasons = out
        .iter()
        .map(|e| match e {
            ValidationError::ParamAbiAttrInvalid { reason, .. } => *reason,
            _ => panic!("wrong variant"),
        })
        .collect::<Vec<_>>();
    assert_eq!(
        reasons,
        vec![
            "byval and sret are mutually exclusive on one parameter",
            "byval/sret require a pointer-typed parameter",
            "sret marks the return slot, so the signature must return no values",
            "at most one parameter may be sret",
            "sret marks the return slot, so the signature must return no values",
            "attribute is positioned past the signature's parameters"
        ]
    );
}
#[test]
fn exact_five_pointer_spellings_are_accepted_without_peeling_refinements() {
    let mut m = fixture();
    m.func_types[0].returns.clear();
    m.functions[0].attrs.params = vec![attrs(true, false)];
    for ty in [
        Ty::Ptr,
        Ty::PtrConst(Box::new(Ty::U8)),
        Ty::PtrMut(Box::new(Ty::U8)),
        Ty::Ref(Box::new(Ty::U8)),
        Ty::RefMut(Box::new(Ty::U8)),
    ] {
        m.func_types[0].params = vec![ty];
        assert!(run(&m).0.is_empty());
    }
    m.types = vec![Ty::Ptr];
    m.func_types[0].params = vec![Ty::Refine(TyId::new(0), PredId::new(0))];
    assert_eq!(run(&m).0.len(), 1);
}
#[test]
fn every_flag_pair_preserves_exclusive_pointer_and_return_rules() {
    let mut m = fixture();
    for byval in [false, true] {
        for sret in [false, true] {
            m.functions[0].attrs.params = vec![attrs(byval, sret)];
            for pointer in [false, true] {
                m.func_types[0].params = vec![if pointer { Ty::Ptr } else { Ty::U8 }];
                run(&m);
            }
        }
    }
}
#[test]
fn missing_signature_skips_the_function_and_out_of_range_flags_emit_only_position_error() {
    let mut m = fixture();
    m.func_types.clear();
    assert!(run(&m).0.is_empty());
    m.func_types
        .push(trust_ir::FuncTy::unrecorded(vec![], vec![Ty::U8], false));
    let out = run(&m).0;
    assert_eq!(out.len(), 3);
    assert!(out.iter().all(|e|matches!(e,ValidationError::ParamAbiAttrInvalid {reason,..} if *reason=="attribute is positioned past the signature's parameters")));
}
#[test]
fn sret_seen_is_reset_per_physical_function_and_duplicate_ids_do_not_skip_rows() {
    let mut m = fixture();
    m.func_types[0] = trust_ir::FuncTy::unrecorded(vec![Ty::Ptr], vec![], false);
    m.functions[0].attrs.params = vec![attrs(false, true)];
    m.functions.push(m.functions[0].clone());
    assert!(run(&m).0.is_empty());
    m.functions[1].attrs.params.push(attrs(false, true));
    assert_eq!(run(&m).0.len(), 1);
}
#[test]
fn unflagged_long_attribute_tail_does_not_request_missing_signature_slots() {
    let mut m = fixture();
    m.functions[0].attrs.params = vec![attrs(false, false); 1000];
    assert!(run(&m).0.is_empty());
    m.functions[0].attrs.params[999].byval = true;
    let out = run(&m).0;
    assert!(matches!(
        out.as_slice(),
        [ValidationError::ParamAbiAttrInvalid {
            param_index: 999,
            ..
        }]
    ));
}
#[test]
fn full_raw_names_are_copied_unchanged_in_every_diagnostic() {
    let mut m = fixture();
    m.functions[0].name = "λ\n'\"".repeat(3000) + "TAIL";
    let out = run(&m).0;
    assert!(out.iter().all(|e|matches!(e,ValidationError::ParamAbiAttrInvalid {func_name,..} if func_name==&m.functions[0].name)));
}
#[test]
fn unrelated_attribute_payloads_and_nested_pointer_contents_are_not_newly_walked() {
    let mut m = fixture();
    m.func_types[0].params = vec![Ty::PtrConst(Box::new(Ty::Unit))];
    m.func_types[0].returns.clear();
    m.functions[0].attrs.params = vec![attrs(true, false)];
    let (_, before) = run(&m);
    m.func_types[0].params[0] = Ty::PtrConst(Box::new(Ty::Tuple(vec![Ty::Error; 10000])));
    m.functions[0].attrs.params[0].align = Some(u64::MAX);
    m.functions[0].attrs.params[0].dereferenceable = Some(u64::MAX);
    let (_, after) = run(&m);
    assert_eq!(before.events, after.events);
}
