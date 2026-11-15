// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_and_single_well_spelled_table_have_no_diagnostics() {
    assert!(run(&Module::new("empty")).0.is_empty());
    assert!(run(&valid()).0.is_empty());
}
#[test]
fn absent_and_duplicate_physical_function_ids_are_not_resolved_by_a_first_match() {
    let mut m = valid();
    m.functions.clear();
    assert_eq!(
        run(&m).0,
        vec![error(
            0,
            7,
            "the glue names no function of this module (or a duplicated id)"
        )]
    );
    m.functions.push(function(99, "wrong slot", true));
    m.functions.push(function(7, "later unique", true));
    assert!(run(&m).0.is_empty());
    let mut duplicate = function(7, TRUSTED_RC_RUNTIMES[0].entry_points[0].symbol, false);
    duplicate.ty = FuncTyId::new(u32::MAX);
    duplicate.linkage = Linkage::ExternalWeak;
    m.functions.insert(0, duplicate);
    assert_eq!(
        run(&m).0,
        vec![error(
            0,
            7,
            "the glue names no function of this module (or a duplicated id)"
        )]
    );
}
#[test]
fn every_calling_convention_uses_exact_ptr_void_nonvariadic_signature_shape() {
    let mut m = valid();
    for conv in CallingConv::ALL {
        m.functions[0].calling_conv = conv;
        assert!(run(&m).0.is_empty());
    }
    for signature in [
        FuncTy::unrecorded(vec![], vec![], false),
        FuncTy::unrecorded(vec![Ty::U8], vec![], false),
        FuncTy::unrecorded(vec![Ty::PtrConst(Box::new(Ty::U8))], vec![], false),
        FuncTy::unrecorded(vec![Ty::Ref(Box::new(Ty::U8))], vec![], false),
        FuncTy::unrecorded(vec![Ty::Ptr, Ty::Ptr], vec![], false),
        FuncTy::unrecorded(vec![Ty::Ptr], vec![Ty::Unit], false),
        FuncTy::unrecorded(vec![Ty::Ptr], vec![], true),
    ] {
        m.func_types[0] = signature;
        assert_eq!(
            run(&m).0,
            vec![error(
                0,
                7,
                &signature_text(&m.functions[0], &m.func_types[0])
            )]
        );
    }
}
#[test]
fn only_bodyless_externalweak_is_the_original_weak_declaration_refusal() {
    for linkage in [
        Linkage::External,
        Linkage::Internal,
        Linkage::Private,
        Linkage::Weak,
        Linkage::LinkOnce,
        Linkage::AvailableExternally,
        Linkage::WeakOdr,
        Linkage::LinkOnceOdr,
        Linkage::ExternalWeak,
    ] {
        for body in [false, true] {
            let mut m = valid();
            m.functions[0] = function(7, "glueλ\0", body);
            m.functions[0].linkage = linkage;
            let expected = if !body && linkage == Linkage::ExternalWeak {
                vec![error(0, 7, &weak_text("glueλ\0"))]
            } else {
                vec![]
            };
            assert_eq!(run(&m).0, expected);
        }
    }
}
#[test]
fn every_rc_and_handle_pinned_symbol_refuses_by_exact_name_even_with_glue_signature() {
    let names = TRUSTED_RC_RUNTIMES
        .iter()
        .flat_map(|p| p.entry_points.iter().map(|e| e.symbol))
        .chain(
            TRUSTED_HANDLE_RUNTIMES
                .iter()
                .flat_map(|p| p.entry_points.iter().map(|e| e.symbol)),
        )
        .collect::<Vec<_>>();
    assert!(!names.is_empty());
    for name in names {
        for body in [false, true] {
            let mut m = valid();
            m.functions[0] = function(7, name, body);
            assert_eq!(run(&m).0, vec![error(0, 7, &pinned_text(name))]);
        }
    }
    for name in [
        format!("{}\0", TRUSTED_RC_RUNTIMES[0].entry_points[0].symbol),
        format!("{}λ", TRUSTED_HANDLE_RUNTIMES[0].entry_points[0].symbol),
    ] {
        let mut m = valid();
        m.functions[0].name = name;
        assert!(run(&m).0.is_empty());
    }
}
#[test]
fn row_order_compares_only_the_previous_physical_glue_and_enforces_injectivity() {
    let mut m = module();
    for id in [9, 2, 8] {
        m.functions.push(function(id, "glue", true));
        add(&mut m, id, Ty::Struct(StructId::new(id)));
    }
    assert_eq!(run(&m).0, vec![error(1, 2, &order_text(2, 9))]);
    let mut m = module();
    m.functions.push(function(u32::MAX, "extreme", true));
    add(&mut m, u32::MAX, Ty::Struct(StructId::new(1)));
    add(&mut m, u32::MAX, Ty::Struct(StructId::new(2)));
    assert_eq!(
        run(&m).0,
        vec![error(1, u32::MAX, &order_text(u32::MAX, u32::MAX))]
    );
}
#[test]
fn a_wrong_first_key_is_still_registered_for_every_later_duplicate_diagnostic() {
    let ty = Ty::Refine(TyId::new(0), PredId::new(4));
    let mut m = module();
    for id in [7, 8, 9] {
        m.functions.push(function(id, "glue", true));
        add(&mut m, id, ty.clone());
    }
    assert_eq!(
        run(&m).0,
        vec![
            error(0, 7, &key_text(&ty, true)),
            error(1, 8, &duplicate_text(&ty)),
            error(1, 8, &key_text(&ty, true)),
            error(2, 9, &duplicate_text(&ty)),
            error(2, 9, &key_text(&ty, true))
        ]
    );
}
#[test]
fn derived_key_identity_keeps_distinct_array_ids_even_when_their_table_types_equal() {
    let mut m = module();
    m.types = vec![Ty::Struct(StructId::new(3)); 2];
    for (id, key) in [(7, 0), (8, 1), (9, 0)] {
        m.functions.push(function(id, "glue", true));
        add(&mut m, id, Ty::Array(TyId::new(key), 1));
    }
    assert_eq!(
        run(&m).0,
        vec![error(2, 9, &duplicate_text(&Ty::Array(TyId::new(0), 1)))]
    );
}
#[test]
fn refined_zero_dangling_cyclic_and_done_array_keys_preserve_the_trivial_predicate() {
    let cases = [
        (
            Ty::Refine(TyId::new(0), PredId::new(1)),
            vec![Ty::Unit],
            Some(true),
        ),
        (Ty::Array(TyId::new(u32::MAX), 0), vec![], Some(false)),
        (Ty::Array(TyId::new(0), 1), vec![], None),
        (
            Ty::Array(TyId::new(0), 1),
            vec![Ty::Array(TyId::new(0), 1)],
            None,
        ),
        (
            Ty::Tuple(vec![Ty::Array(TyId::new(0), 1), Ty::Array(TyId::new(0), 2)]),
            vec![Ty::U8],
            Some(false),
        ),
    ];
    for (ty, types, rule) in cases {
        let mut m = valid();
        m.drop_glue[0].ty = ty.clone();
        m.types = types;
        let expected = rule
            .map(|refined| vec![error(0, 7, &key_text(&ty, refined))])
            .unwrap_or_default();
        assert_eq!(run(&m).0, expected);
    }
}
#[test]
fn all_six_failures_on_a_later_row_keep_t5_t6_t7_t2_t3_t4_order() {
    let m = multi();
    let f = &m.functions[1];
    assert_eq!(
        run(&m).0,
        vec![
            error(0, 9, &key_text(&Ty::Unit, false)),
            error(1, 7, &order_text(7, 9)),
            error(1, 7, &duplicate_text(&Ty::Unit)),
            error(1, 7, &key_text(&Ty::Unit, false)),
            error(1, 7, &signature_text(f, &m.func_types[1])),
            error(1, 7, &weak_text(&f.name)),
            error(1, 7, &pinned_text(&f.name))
        ]
    );
}
#[test]
fn complete_raw_function_names_and_nested_key_and_signature_text_are_not_truncated() {
    let mut m = module();
    let key = Ty::Tuple(vec![Ty::Struct(StructId::new(3)); 600]);
    m.func_types[0] = FuncTy::unrecorded(vec![Ty::Tuple(vec![Ty::U8; 600])], vec![Ty::Unit], false);
    let name = "rawλ'\0尾".repeat(600) + "FUNCTIONTAIL";
    for id in [u32::MAX - 1, u32::MAX] {
        m.functions.push(function(id, &name, true));
        add(&mut m, id, key.clone());
    }
    assert_eq!(
        run(&m).0,
        vec![
            error(
                0,
                u32::MAX - 1,
                &signature_text(&m.functions[0], &m.func_types[0])
            ),
            error(1, u32::MAX, &duplicate_text(&key)),
            error(
                1,
                u32::MAX,
                &signature_text(&m.functions[1], &m.func_types[0])
            )
        ]
    );
}
#[test]
fn missing_signature_does_not_suppress_weak_or_pinned_checks_and_full_indices() {
    let mut m = module();
    let name = TRUSTED_RC_RUNTIMES[0].entry_points[0].symbol;
    let mut f = function(u32::MAX, name, false);
    f.ty = FuncTyId::new(u32::MAX);
    f.linkage = Linkage::ExternalWeak;
    m.functions.push(f);
    add(&mut m, u32::MAX, Ty::Struct(StructId::new(3)));
    assert_eq!(
        run(&m).0,
        vec![
            error(
                0,
                u32::MAX,
                &format!(
                    "the glue '{name}' names function type functy.{}, which does not exist",
                    u32::MAX
                )
            ),
            error(0, u32::MAX, &weak_text(name)),
            error(0, u32::MAX, &pinned_text(name))
        ]
    );
}
