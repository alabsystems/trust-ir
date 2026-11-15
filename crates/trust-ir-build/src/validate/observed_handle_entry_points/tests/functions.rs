// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_trusted_entrypoint_accepts_only_its_original_default_visible_external_contract() {
    let r = HandleRegistry {
        pins: TRUSTED_HANDLE_RUNTIMES.to_vec(),
    };
    let mut m = Module::new("");
    for p in r.pins() {
        for e in p.entry_points {
            let id = m.func_types.len() as u32;
            m.func_types.push(p.func_ty(e));
            let mut f = Function::new(
                FuncId::new(id),
                e.symbol,
                FuncTyId::new(id),
                BlockId::new(0),
            );
            f.calling_conv = p.calling_conv;
            m.functions.push(f);
        }
    }
    assert!(run(&m, &r).0.is_empty());
}
#[test]
fn scalar_only_symbol_forgery_is_refused_even_when_no_handle_occurs_in_the_module() {
    let (mut m, r) = fixture();
    m.func_types[0] = FuncTy::unrecorded(vec![Ty::Ptr, Ty::Ptr], vec![Ty::Ptr], false);
    assert!(
        !m.nominal_type_reachability()
            .contains_handle(&Ty::Func(FuncTyId::new(0)))
    );
    assert!(matches!(
        &run(&m, &r).0[..],
        [ValidationError::HandleEntryPointSignatureMismatch { .. }]
    ));
}
#[test]
fn all_mismatches_preserve_exact_original_order_and_local_definition_adds_second_error() {
    let (m, r) = bad_fixture();
    let out = run(&m, &r).0;
    assert_eq!(out.len(), 2);
    assert!(
        matches!(&out[0],ValidationError::HandleEntryPointSignatureMismatch{function:u32::MAX,actual,..} if actual.starts_with("signature (ptr) -> (ptr) (variadic), calling convention fastcc, naked, visibility protected, section ")&&actual.contains(", display path "))
    );
    assert!(matches!(
        &out[1],
        ValidationError::HandleEntryPointDefinedLocally {
            function: u32::MAX,
            ..
        }
    ));
}
#[test]
fn unsigned_dangling_signature_and_every_calling_convention_visibility_keep_original_diagnostics() {
    let (mut m, r) = fixture();
    m.functions[0].ty = FuncTyId::new(u32::MAX);
    assert!(
        matches!(&run(&m,&r).0[..],[ValidationError::HandleEntryPointSignatureMismatch{actual,..}] if actual=="dangling signature functy.4294967295")
    );
    for cc in CallingConv::ALL {
        m.functions[0].ty = FuncTyId::new(0);
        m.functions[0].calling_conv = cc;
        run(&m, &r);
    }
    for visibility in [
        trust_ir::Visibility::Default,
        trust_ir::Visibility::Hidden,
        trust_ir::Visibility::Protected,
    ] {
        m.functions[0].calling_conv = CallingConv::C;
        m.functions[0].visibility = visibility;
        run(&m, &r);
    }
}
#[test]
fn optional_correct_display_path_is_accepted_but_empty_section_and_wrong_path_are_exact_refusals() {
    let (mut m, r) = fixture();
    assert!(run(&m, &r).0.is_empty());
    m.functions[0].display_path = Some("actual::Path".into());
    assert!(run(&m, &r).0.is_empty());
    m.functions[0].section = Some(String::new());
    m.functions[0].display_path = Some(String::new());
    assert!(
        matches!(&run(&m,&r).0[..],[ValidationError::HandleEntryPointSignatureMismatch{actual,..}] if actual=="section \"\", display path \"\"")
    );
}
#[test]
fn first_physical_pin_and_entry_choose_expected_contract_without_union_or_last_match() {
    let (m, mut r) = fixture();
    let mut wrong = r.pins[0].clone();
    wrong.calling_conv = CallingConv::Rust;
    wrong.entry_points = Box::leak(
        vec![entry("pinned", vec![PinnedTy::Scalar(Ty::Ptr)], vec![])].into_boxed_slice(),
    );
    r.pins.push(wrong.clone());
    assert!(run(&m, &r).0.is_empty());
    r.pins.swap(0, 1);
    assert!(!run(&m, &r).0.is_empty());
}
#[test]
fn deep_scalar_identity_and_present_abi_are_not_normalized_erased_or_confused_with_handle_layout() {
    let mut ty = Ty::Tuple(vec![Ty::Char, Ty::U32, Ty::handle("raw λ'\0", "rt::尾")]);
    for _ in 0..32 {
        ty = Ty::Ref(Box::new(ty));
    }
    let p = pin(vec![entry("pinned", vec![PinnedTy::Scalar(ty)], vec![])]);
    let mut m = Module::new("");
    m.func_types = vec![p.func_ty(&p.entry_points[0])];
    m.functions = vec![Function::new(
        FuncId::new(0),
        "pinned",
        FuncTyId::new(0),
        BlockId::new(0),
    )];
    let r = HandleRegistry { pins: vec![p] };
    assert!(run(&m, &r).0.is_empty());
    m.func_types[0].abi = Some(abi());
    assert!(
        matches!(&run(&m,&r).0[..],[ValidationError::HandleEntryPointSignatureMismatch{actual,..}] if actual.starts_with("signature "))
    );
    let (_, before, bound) = run(&m, &r);
    let descriptor = m.func_types[0].abi.as_mut().unwrap();
    descriptor.frontend.name = "unread frontend λ\0".repeat(4096);
    descriptor.target.features = vec!["unread target feature".repeat(1000); 64];
    descriptor.arguments = vec![descriptor.result.clone(); 4096];
    let (_, after, end) = run(&m, &r);
    assert_eq!(&before.events[..bound], &after.events[..end]);
    m.func_types[0].abi = None;
    m.func_types[0].params = vec![Ty::Ptr];
    assert!(!run(&m, &r).0.is_empty());
}
#[test]
fn full_raw_debug_fields_and_unrelated_metadata_keep_original_text_and_unread_contracts() {
    let (mut m, r) = bad_fixture();
    m.functions[0].section = Some("λ'\"\\\n\0\u{301}尾".repeat(1025) + "TAIL");
    m.functions[0].display_path = Some("λ'\"\n\0".repeat(1025) + "END");
    let (_, before, bound) = run(&m, &r);
    m.functions[0].value_names = Some(
        (0..4096)
            .map(|i| (ValueId::new(i), "ignored λ\0".repeat(10)))
            .collect(),
    );
    m.functions[0].retained = true;
    m.globals.clear();
    let (_, after, end) = run(&m, &r);
    assert_eq!(&before.events[..bound], &after.events[..end]);
}
