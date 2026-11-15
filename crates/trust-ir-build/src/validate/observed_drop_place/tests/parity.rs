// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn plain_ptr_and_exactly_one_refinement_layer_match_actual_representation_lookup() {
    for ty in [Ty::Ptr, refine(0)] {
        for invoke in [false, true] {
            assert!(
                run(&fixture(ty.clone()), &drop_inst(invoke, 0))
                    .0
                    .is_empty()
            );
        }
    }
}
#[test]
fn nested_refinement_and_cycles_are_not_recursively_peeled_into_permission() {
    let m = fixture(refine(1));
    assert_eq!(run(&m, &drop_inst(false, 0)).0.len(), 1);
    let mut m = fixture(refine(1));
    m.types[1] = refine(1);
    assert_eq!(run(&m, &drop_inst(false, 0)).0.len(), 1);
}
#[test]
fn missing_refinement_base_refuses_but_unknown_value_keeps_original_local_skip() {
    let m = fixture(refine(u32::MAX));
    assert_eq!(run(&m, &drop_inst(false, 0)).0.len(), 1);
    assert!(run(&m, &drop_inst(false, 999)).0.is_empty());
}
#[test]
fn pointer_like_references_and_rich_inline_types_are_not_exact_ptr() {
    for ty in [
        Ty::Ref(Box::new(Ty::Bool)),
        Ty::PtrConst(Box::new(Ty::Bool)),
        Ty::Func(FuncTyId::new(0)),
        Ty::Tuple(vec![Ty::handle("é", "rt::中"), Ty::U64]),
        Ty::Bool,
    ] {
        let errors = run(&fixture(ty.clone()), &drop_inst(false, 0)).0;
        assert_eq!(errors.len(), 1);
        let ValidationError::OperandTypeMismatch { actual, .. } = &errors[0] else {
            panic!()
        };
        assert_eq!(actual, &ty.to_string());
    }
}
#[test]
fn both_actual_instruction_spellings_preserve_role_expected_and_block() {
    let m = fixture(Ty::U64);
    for invoke in [false, true] {
        let e = run(&m, &drop_inst(invoke, 0)).0;
        let ValidationError::OperandTypeMismatch {
            block,
            op,
            role,
            expected,
            ..
        } = &e[0]
        else {
            panic!()
        };
        assert_eq!(*block, 1);
        assert_eq!(op, if invoke { "drop_invoke" } else { "drop" });
        assert_eq!(role, "ptr");
        assert_eq!(expected, "ptr");
    }
}
#[test]
fn unrelated_instruction_and_dropped_type_payload_are_not_place_authority() {
    let m = fixture(Ty::Ptr);
    assert!(run(&m, &Inst::Return { values: vec![v(0)] }).0.is_empty());
    let inst = Inst::Drop {
        ty: Ty::Tuple(vec![Ty::handle("unread", "rt::unread"); 100]),
        ptr: v(0),
    };
    assert!(run(&m, &inst).0.is_empty());
}
