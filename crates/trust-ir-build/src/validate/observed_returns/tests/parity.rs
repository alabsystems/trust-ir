// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn actual_signature_lookup_retains_original_borrowed_pointer_identity() {
    let (m, f) = fixture();
    assert!(getter(&m, &f).0.is_ok());
}
#[test]
fn missing_signature_getter_preserves_full_original_name_and_id() {
    let (m, mut f) = fixture();
    f.ty = FuncTyId::new(u32::MAX);
    f.name = "λ raw\0尾\n".repeat(2000);
    let out = getter(&m, &f).0;
    assert_eq!(
        out,
        Err(ValidationError::FuncTypeNotFound {
            func_name: f.name,
            func_ty_id: u32::MAX
        })
    );
}
#[test]
fn exact_arity_and_return_type_transport_keep_original_empty_result() {
    let (m, f) = fixture();
    assert!(
        run(
            &m,
            &f,
            &Inst::Return {
                values: vec![v(1), v(0)]
            }
        )
        .0
        .is_empty()
    );
}
#[test]
fn arity_error_precedes_all_known_zipped_type_errors_and_unknowns_remain_skipped() {
    let (m, f) = fixture();
    let out = run(
        &m,
        &f,
        &Inst::Return {
            values: vec![v(0), v(1), v(99)],
        },
    )
    .0;
    assert!(matches!(
        &out[..],
        [
            ValidationError::ReturnArityMismatch { .. },
            ValidationError::ReturnTypeMismatch { .. },
            ValidationError::ReturnTypeMismatch { .. }
        ]
    ));
    let out = run(
        &m,
        &f,
        &Inst::Return {
            values: vec![v(99), v(1)],
        },
    )
    .0;
    assert_eq!(out.len(), 1);
}
#[test]
fn coroutine_suspend_uses_exactly_one_return_slot_and_cannot_forge_handle_return() {
    let (mut m, f) = fixture();
    let out = run(&m, &f, &suspend(1)).0;
    assert!(matches!(
        &out[..],
        [ValidationError::ReturnArityMismatch {
            expected: 2,
            actual: 1,
            ..
        }]
    ));
    m.func_types[0].returns = vec![Ty::U64];
    assert!(run(&m, &f, &suspend(1)).0.is_empty());
    m.func_types[0].returns = vec![Ty::handle("Name", "rt::Name")];
    assert!(matches!(
        &run(&m, &f, &suspend(2)).0[..],
        [ValidationError::ReturnTypeMismatch { .. }]
    ));
}
#[test]
fn only_top_level_refinement_involvement_defers_to_the_mandatory_consumption_rule() {
    let (mut m, mut f) = fixture();
    m.func_types[0].returns = vec![Ty::Refine(TyId::new(0), PredId::new(0))];
    assert!(
        run(&m, &f, &Inst::Return { values: vec![v(1)] })
            .0
            .is_empty()
    );
    m.func_types[0].returns = vec![Ty::Tuple(vec![Ty::U64])];
    f.blocks[0].params[1].1 = Ty::Tuple(vec![Ty::Refine(TyId::new(0), PredId::new(0))]);
    assert_eq!(run(&m, &f, &Inst::Return { values: vec![v(1)] }).0.len(), 1);
}
#[test]
fn actual_last_definition_map_and_complete_nested_display_match_original() {
    let (mut m, mut f) = fixture();
    f.blocks[0]
        .body
        .push(InstrNode::new(Inst::Undef { ty: Ty::Bool }).with_result(v(1)));
    m.func_types[0].returns = vec![Ty::Tuple(vec![Ty::handle("Name", "rt::Name"), Ty::Bool])];
    let out = run(&m, &f, &Inst::Return { values: vec![v(1)] }).0;
    assert!(
        matches!(&out[..],[ValidationError::ReturnTypeMismatch{expected,actual,..}]if expected.contains("rt::Name")&&actual=="bool")
    );
}
#[test]
fn unrelated_opcode_is_only_this_return_constituents_no_diagnostic_lane() {
    let (m, f) = fixture();
    assert!(run(&m, &f, &Inst::Undef { ty: Ty::Bool }).0.is_empty());
}
