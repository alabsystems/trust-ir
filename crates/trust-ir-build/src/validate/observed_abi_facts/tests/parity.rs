// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_module_and_missing_signature_skip_only_this_original_group() {
    assert!(run(&module()).0.is_empty());
    let mut m = module();
    m.functions.push(function());
    assert!(run(&m).0.is_empty());
}
#[test]
fn no_fact_and_direct_do_not_demand_layout_or_pair_authority() {
    for attrs in [ParamAttrs::default(), fact(PassMode::Direct)] {
        assert!(run(&one(Ty::Sequence(TyId::new(999)), attrs)).0.is_empty());
    }
}
#[test]
fn extension_exact_closed_narrow_families_and_wide_refusal_keep_order() {
    for ty in [
        Ty::I8,
        Ty::U32,
        Ty::Bool,
        Ty::Char,
        Ty::U64,
        Ty::F64,
        Ty::Ptr,
        Ty::Refine(TyId::new(3), trust_ir::value::PredId::new(0)),
    ] {
        let okay = matches!(&ty, Ty::I8 | Ty::U32 | Ty::Bool | Ty::Char);
        let errors = run(&one(
            ty,
            ParamAttrs {
                ext: ArgExt::SignExt,
                ..Default::default()
            },
        ))
        .0;
        assert_eq!(errors.is_empty(), okay);
    }
}
#[test]
fn ignore_checks_zero_nonzero_and_unavailable_full_layouts() {
    for (ty, ok) in [
        (Ty::Unit, true),
        (Ty::U64, false),
        (Ty::Sequence(TyId::new(999)), false),
    ] {
        assert_eq!(run(&one(ty, fact(PassMode::Ignore))).0.is_empty(), ok);
    }
}
#[test]
fn pair_uses_actual_lanes_including_zero_sized_fields_and_fat_pointer() {
    for (ty, ok) in [
        (Ty::Tuple(vec![Ty::U64, Ty::Unit, Ty::Ptr]), true),
        (Ty::Tuple(vec![Ty::U64, Ty::Unit]), false),
        (Ty::FatPtr(trust_ir::ty::FatPtrKind::Str), true),
        (Ty::U64, false),
    ] {
        assert_eq!(run(&one(ty, fact(PassMode::Pair))).0.is_empty(), ok);
    }
}
#[test]
fn empty_cast_preserves_two_diagnostics_and_zero_sized_single_diagnostic() {
    let e = run(&one(Ty::U64, fact(PassMode::Cast { pieces: vec![] }))).0;
    assert_eq!(e.len(), 2);
    assert!(
        matches!(&e[0],ValidationError::InvalidAbiSlotFact{detail,..} if detail=="`cast` names no lanes")
    );
    assert_eq!(
        run(&one(Ty::Unit, fact(PassMode::Cast { pieces: vec![] })))
            .0
            .len(),
        1
    );
}
#[test]
fn cast_first_non_scalar_precedes_zero_width_then_full_coverage_check() {
    for pieces in [
        vec![Ty::Unit, Ty::Tuple(vec![])],
        vec![Ty::Unit],
        vec![Ty::U32],
        vec![Ty::U64],
        vec![Ty::U64, Ty::U64],
    ] {
        let expected = pieces == vec![Ty::U64] || pieces == vec![Ty::U64, Ty::U64];
        assert_eq!(
            run(&one(Ty::U64, fact(PassMode::Cast { pieces })))
                .0
                .is_empty(),
            expected
        );
    }
}
#[test]
fn indirect_byvalue_and_prelowered_claims_keep_contradictions() {
    for (ty, byval, pass, okay) in [
        (
            Ty::Tuple(vec![Ty::U64]),
            false,
            PassMode::Indirect { on_stack: false },
            true,
        ),
        (Ty::Ptr, true, PassMode::Indirect { on_stack: false }, true),
        (
            Ty::U64,
            false,
            PassMode::Indirect { on_stack: false },
            false,
        ),
        (Ty::Ptr, true, PassMode::Direct, false),
    ] {
        assert_eq!(
            run(&one(
                ty,
                ParamAttrs {
                    byval,
                    pass: Some(pass),
                    ..Default::default()
                }
            ))
            .0
            .is_empty(),
            okay
        );
    }
}
#[test]
fn missing_parameter_and_all_return_attribute_checks_have_whole_original_order() {
    assert!(run(&many_errors()).0.len() >= 10);
    for returns in [vec![], vec![Ty::U64], vec![Ty::U64, Ty::Ptr]] {
        let m = untyped(
            vec![],
            returns,
            vec![],
            ParamAttrs {
                byval: true,
                sret: true,
                readonly: true,
                ..Default::default()
            },
        );
        let e = run(&m).0;
        assert!(e.len() >= 3);
        for (i, name) in ["byval", "sret", "readonly"].into_iter().enumerate() {
            assert!(
                matches!(&e[i],ValidationError::InvalidAbiSlotFact{detail,..} if detail.starts_with(&format!("`{name}`")))
            );
        }
    }
}
#[test]
fn full_recorded_signature_and_legacy_sret_extension_are_accepted_as_data() {
    assert!(run(&typed()).0.is_empty());
}
#[test]
fn physical_function_slot_then_reconcile_precedes_later_signature_table_checks() {
    let mut m = typed();
    m.functions[0].calling_conv = trust_ir::CallingConv::Fast;
    m.functions[0].attrs.params[2].ext = ArgExt::SignExt;
    let mut second = m.functions[0].clone();
    second.id = FuncId::new(7);
    m.functions.push(second);
    m.func_types[0].abi.as_mut().unwrap().convention.clear();
    let e = run(&m).0;
    assert_eq!(e.len(), 5);
    assert!(matches!(
        &e[0],
        ValidationError::InvalidAbiSlotFact { function: 6602, .. }
    ));
    assert!(matches!(&e[1], ValidationError::InvalidSignatureAbi { .. }));
    assert!(matches!(
        &e[2],
        ValidationError::InvalidAbiSlotFact { function: 7, .. }
    ));
    assert!(matches!(&e[3], ValidationError::InvalidSignatureAbi { .. }));
    assert!(matches!(&e[4], ValidationError::InvalidSignatureAbi { .. }));
}
#[test]
fn target_only_runs_after_successful_signature_semantics_even_without_functions() {
    let mut m = typed();
    m.functions.clear();
    m.target_info = None;
    let target = run(&m).0;
    assert_eq!(target.len(), 1);
    m.func_types[0].abi.as_mut().unwrap().convention.clear();
    let semantic = run(&m).0;
    assert_eq!(semantic.len(), 1);
    assert_ne!(semantic, target);
}
#[test]
fn long_equal_length_unicode_target_difference_keeps_entire_original_detail() {
    let mut m = typed();
    m.functions.clear();
    let abi = m.func_types[0].abi.as_mut().unwrap();
    abi.target.triple = "λ🦀".repeat(700);
    m.target_info.as_mut().unwrap().triple = abi.target.triple.clone();
    assert!(run(&m).0.is_empty());
    m.target_info.as_mut().unwrap().triple.pop();
    m.target_info.as_mut().unwrap().triple.push('🐟');
    let e = run(&m).0;
    assert_eq!(e.len(), 1);
    assert!(
        matches!(&e[0],ValidationError::InvalidSignatureAbi{detail,..} if detail=="typed signature ABI target disagrees with the module target")
    );
}
#[test]
fn unrepresentable_wire_is_typed_outer_refusal_never_a_smaller_error_vector() {
    let mut m = typed();
    m.functions.clear();
    m.func_types[0].abi.as_mut().unwrap().target.features = vec!["x".repeat(1_048_577)];
    assert!(!original(&m).is_empty());
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let t = LayoutTable::new_observed(&m, &mut s, site()).unwrap();
    assert!(matches!(
        validate_module_abi_facts_observed(&t, &mut s, site()),
        Err(ObservedValueError::UnsupportedValue)
    ));
    assert!(s.first_refusal().is_none());
    dispose(t, &mut s);
}
