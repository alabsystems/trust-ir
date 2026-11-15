// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn mixed_variadic_values_keep_handle_precedence_order_duplicates_and_unknown_skip() {
    let (m, f) = fixture();
    let out = run(&m, &f, &args(), 0, "L", Mode::Present).0;
    assert_eq!(out.len(), 4);
    assert!(
        matches!(&out[0], ValidationError::InvalidHandleUse { detail, .. } if detail == HANDLE)
    );
    assert!(
        matches!(&out[1], ValidationError::InvalidDialectType { detail, .. } if detail == DIALECT)
    );
    assert!(matches!(&out[2], ValidationError::InvalidHandleUse { .. }));
    assert_eq!(out[0], out[3]);
}
#[test]
fn fixed_prefix_and_out_of_range_skip_preserve_original_boundaries() {
    let (m, f) = fixture();
    let args = args();
    for fixed in (0..=args.len() + 1).chain(core::iter::once(usize::MAX)) {
        run(&m, &f, &args, fixed, "L", Mode::Present);
    }
}
#[test]
fn absent_optional_summary_reads_neither_argument_sequence_nor_location() {
    let (m, f) = fixture();
    let (out, a, start_a, end_a) = run(&m, &f, &[], 0, "", Mode::Absent);
    assert!(out.is_empty());
    let (_, b, start_b, end_b) = run(
        &m,
        &f,
        &vec![v(1); 4096],
        0,
        &"λ\0tail".repeat(4096),
        Mode::Absent,
    );
    assert_eq!(a.events[start_a..end_a], b.events[start_b..end_b]);
}
#[test]
fn actual_last_definition_value_rows_are_used_instead_of_first_declaration() {
    let (m, mut f) = fixture();
    f.blocks[0]
        .body
        .push(trust_ir::InstrNode::new(Inst::Undef { ty: Ty::Bool }).with_results([v(1)]));
    assert!(run(&m, &f, &[v(1)], 0, "L", Mode::Present).0.is_empty());
    assert_eq!(run(&m, &f, &[v(2)], 0, "L", Mode::Present).0.len(), 1);
}
#[test]
fn complete_raw_location_is_copied_only_for_actual_nominal_diagnostics() {
    let (m, f) = fixture();
    let raw = "λ\0尾\nraw".repeat(2000);
    let out = run(&m, &f, &[v(1), v(2)], 0, &raw, Mode::Present).0;
    assert_eq!(
        out,
        vec![
            ValidationError::InvalidHandleUse {
                location: raw.clone(),
                detail: HANDLE.into()
            },
            ValidationError::InvalidDialectType {
                location: raw,
                detail: DIALECT.into()
            }
        ]
    );
}
