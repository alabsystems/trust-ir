// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn exact_pinned_scalar_triple_and_non_effect_codegen_hints_stay_accepted_without_handle_census() {
    let mut m = fixture();
    for f in &mut m.functions {
        f.attrs.cold = true;
        f.attrs.inlinehint = true;
        f.visibility = trust_ir::Visibility::Protected;
        f.section = Some("not-an-RC-rule".into());
    }
    assert!(m.func_types.iter().all(|s| s.params == vec![Ty::Ptr]));
    assert!(run(&m).0.is_empty());
}
#[test]
fn all_original_mismatches_keep_exact_order_and_local_definition_adds_second_error() {
    let out = run(&bad_fixture()).0;
    assert_eq!(out.len(), 2);
    assert!(
        matches!(&out[0],ValidationError::RcEntryPointSignatureMismatch {expected,actual,..}
        if expected=="ccc (ptr) -> () (display path \"clean_inc\" or unrecorded)"
        && actual.starts_with("signature (ptr) -> (ptr) (variadic), calling convention fastcc, naked, readnone, readonly, parameter attributes, a `Pure` annotation, display path "))
    );
    assert!(matches!(
        out[1],
        ValidationError::RcEntryPointDefinedLocally { .. }
    ));
}
#[test]
fn every_nonempty_parameter_attribute_is_refused_including_presence_only_cast() {
    let mut attrs = vec![ParamAttrs::default(); 9];
    attrs[0].dereferenceable = Some(0);
    attrs[1].nonnull = true;
    attrs[2].align = Some(0);
    attrs[3].noalias = true;
    attrs[4].readonly = true;
    attrs[5].byval = true;
    attrs[6].sret = true;
    attrs[7].ext = ArgExt::ZeroExt;
    attrs[8].pass = Some(PassMode::Cast { pieces: vec![] });
    for param in attrs {
        let mut m = fixture();
        m.functions[0].attrs.params = vec![ParamAttrs::default(), param];
        assert!(
            matches!(&run(&m).0[..],[ValidationError::RcEntryPointSignatureMismatch{actual,..}] if actual=="parameter attributes")
        );
    }
}
#[test]
fn absent_correct_and_raw_display_paths_dangling_type_and_all_calling_conventions_match() {
    let mut m = fixture();
    m.functions[0].display_path = Some("clean_inc".into());
    assert!(run(&m).0.is_empty());
    m.functions[0].display_path = Some("λ'\"\n\0".into());
    run(&m);
    m.functions[0].ty = FuncTyId::new(u32::MAX);
    assert!(
        matches!(&run(&m).0[0],ValidationError::RcEntryPointSignatureMismatch{actual,..}if actual.starts_with("dangling signature functy.4294967295"))
    );
    for cc in CallingConv::ALL {
        let mut m = fixture();
        m.functions[0].calling_conv = cc;
        run(&m);
    }
}
#[test]
fn actual_present_abi_is_unequal_without_reading_or_erasing_its_unrelated_payload() {
    let mut a = fixture();
    a.func_types[0].abi = Some(abi());
    let mut b = a.clone();
    b.func_types[0].abi.as_mut().unwrap().target.target_spec = "x".repeat(1_000_000);
    let (ea, oa, enda) = run(&a);
    let (eb, ob, endb) = run(&b);
    assert!(!ea.is_empty());
    assert_eq!(ea, eb);
    assert_eq!(enda, endb);
    assert_eq!(oa.events, ob.events);
}
#[test]
fn parameter_and_proof_search_short_circuits_ignore_later_payloads_and_cast_lanes() {
    let mut a = fixture();
    a.functions[0].attrs.params = vec![ParamAttrs {
        pass: Some(PassMode::Cast { pieces: vec![] }),
        ..ParamAttrs::default()
    }];
    a.functions[0].proofs = vec![
        ProofAnnotation::Pure,
        ProofAnnotation::BranchWeights(vec![]),
    ];
    let mut b = a.clone();
    if let Some(PassMode::Cast { pieces }) = &mut b.functions[0].attrs.params[0].pass {
        *pieces = vec![Ty::Ptr; 100_000];
    }
    b.functions[0].attrs.params.push(ParamAttrs::default());
    b.functions[0].proofs[1] = ProofAnnotation::BranchWeights(vec![1; 100_000]);
    let (ea, oa, enda) = run(&a);
    let (eb, ob, endb) = run(&b);
    assert_eq!(ea, eb);
    assert_eq!(enda, endb);
    assert_eq!(oa.events, ob.events);
}
