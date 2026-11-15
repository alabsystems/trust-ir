// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_func_type_is_checked_even_without_functions_and_slots_keep_parameter_return_order() {
    let m = fixture();
    assert!(m.functions.is_empty());
    let out = run(&m).0;
    let slots = out
        .iter()
        .map(|e| match e {
            ValidationError::AlwaysMemoryByValueAggregate { slot, .. } => slot.as_str(),
            _ => panic!("variant"),
        })
        .collect::<Vec<_>>();
    assert_eq!(slots, vec!["parameter 1", "parameter 2", "return 0"]);
}
#[test]
fn every_original_aggregate_spelling_is_reported_in_the_whole_type_table() {
    let mut m = fixture();
    m.func_types[0] = trust_ir::FuncTy::unrecorded(
        vec![
            Ty::Struct(StructId::new(0)),
            Ty::Tuple(vec![]),
            Ty::Array(TyId::new(0), 0),
            Ty::Enum(EnumId::new(0)),
            Ty::Record(RecordId::new(0)),
            Ty::Sequence(TyId::new(0)),
            Ty::Set(TyId::new(0), trust_ir::ty::SetRepr::Boxed),
            Ty::Closure(ClosureTyId::new(0)),
            Ty::Vector(Box::new(Ty::U8), 0),
        ],
        vec![],
        false,
    );
    assert_eq!(run(&m).0.len(), 9);
}
#[test]
fn policy_absence_native_c_and_unclassified_are_inert_without_new_type_walks() {
    let mut m = fixture();
    m.target_info = None;
    assert!(run(&m).0.is_empty());
    for policy in [
        trust_ir::StructPassingPolicy::NativeC,
        trust_ir::StructPassingPolicy::Unclassified,
    ] {
        m.target_info = Some(target(policy));
        assert!(run(&m).0.is_empty());
    }
}
#[test]
fn scalar_pointer_unit_never_and_wrapped_aggregates_are_not_by_value_slots() {
    let mut m = fixture();
    m.func_types[0] = trust_ir::FuncTy::unrecorded(
        vec![
            Ty::U8,
            Ty::Unit,
            Ty::Never,
            Ty::Ptr,
            Ty::PtrConst(Box::new(Ty::Tuple(vec![Ty::U8]))),
            Ty::FatPtr(trust_ir::FatPtrKind::Str),
        ],
        vec![],
        false,
    );
    assert!(run(&m).0.is_empty());
}
#[test]
fn one_refinement_peel_and_dangling_nested_cycles_preserve_fail_closed_classification() {
    let mut m = fixture();
    m.types = vec![
        Ty::U8,
        Ty::Tuple(vec![]),
        Ty::Refine(TyId::new(2), PredId::new(0)),
    ];
    m.func_types[0] = trust_ir::FuncTy::unrecorded(
        vec![
            Ty::Refine(TyId::new(0), PredId::new(0)),
            Ty::Refine(TyId::new(1), PredId::new(0)),
            Ty::Refine(TyId::new(2), PredId::new(0)),
            Ty::Refine(TyId::new(u32::MAX), PredId::new(0)),
        ],
        vec![],
        false,
    );
    assert_eq!(run(&m).0.len(), 3);
}
#[test]
fn complete_deep_type_display_is_preserved_without_truncation_or_width_normalization() {
    let mut m = fixture();
    m.func_types[0] = trust_ir::FuncTy::unrecorded(
        vec![Ty::Tuple(vec![Ty::Tuple(vec![Ty::U128, Ty::I128]); 1000])],
        vec![],
        false,
    );
    let out = run(&m).0;
    assert!(
        matches!(&out[0],ValidationError::AlwaysMemoryByValueAggregate {ty,..} if ty==&m.func_types[0].params[0].to_string()&&ty.len()>10000)
    );
}
#[test]
fn physical_duplicate_signatures_and_full_decimal_slot_indices_are_preserved() {
    let mut m = fixture();
    m.func_types[0] = trust_ir::FuncTy::unrecorded(vec![Ty::Tuple(vec![]); 1235], vec![], false);
    m.func_types.push(m.func_types[0].clone());
    let out = run(&m).0;
    assert_eq!(out.len(), 2470);
    assert!(
        matches!(&out[1234],ValidationError::AlwaysMemoryByValueAggregate {func_ty:0,slot,..} if slot=="parameter 1234")
    );
    assert!(
        matches!(&out[2469],ValidationError::AlwaysMemoryByValueAggregate {func_ty:1,slot,..} if slot=="parameter 1234")
    );
}
#[test]
fn successful_diagnostic_strings_are_independent_of_later_signature_mutation() {
    let mut m = fixture();
    let out = run(&m).0;
    let old = out.clone();
    m.func_types.clear();
    assert_eq!(out, old);
}
