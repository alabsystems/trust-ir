// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn full_actual_rule_reports_missing_inhabited_variants_in_original_order() {
    let m = fixture();
    let out = run(&m).0;
    assert_eq!(out.len(), 1);
    assert!(
        matches!(&out[0],ValidationError::ExhaustiveSwitchCasesIncomplete{block:1,reason,..}if reason=="no case for inhabited variant(s) {One = 1}, so the default arm is reachable")
    );
}
#[test]
fn complete_case_set_is_success_and_unknown_case_precedes_missing_diagnostic() {
    let mut m = fixture();
    m.functions[0].blocks[0].body[1] = switch(1, vec![Constant::Int(0), Constant::Int(1)]);
    assert!(run(&m).0.is_empty());
    m.functions[0].blocks[0].body[1] = switch(1, vec![Constant::Int(9)]);
    let out = run(&m).0;
    assert_eq!(out.len(), 2);
    assert!(
        matches!(&out[0],ValidationError::ExhaustiveSwitchCasesIncomplete{reason,..}if reason.starts_with("case value 9 is not a discriminant of "))
    );
    assert!(
        matches!(&out[1],ValidationError::ExhaustiveSwitchCasesIncomplete{reason,..}if reason.contains("{Zero = 0, One = 1}"))
    );
}
#[test]
fn structurally_uninhabited_variant_is_exempt_but_unknown_definition_is_not() {
    let mut m = fixture();
    m.enums[0].variants[1].fields = vec![Ty::Never];
    assert!(run(&m).0.is_empty());
    m.enums[0].variants[1].fields = vec![Ty::Struct(trust_ir::value::StructId::new(999))];
    assert_eq!(run(&m).0.len(), 1);
}
#[test]
fn successive_signed_widenings_apply_from_tag_outward_with_exact_masked_values() {
    let mut m = signed();
    assert!(run(&m).0.is_empty());
    m.functions[0].blocks[0].body[3] = switch(3, vec![Constant::Int(65535), Constant::Int(0)]);
    let out = run(&m).0;
    assert_eq!(out.len(), 2);
    assert!(
        matches!(&out[1],ValidationError::ExhaustiveSwitchCasesIncomplete{reason,..}if reason.contains("Zero = -1"))
    );
}
#[test]
fn zero_extension_and_equal_width_bitcast_keep_original_two_complement_tag_bits() {
    for op in [CastOp::ZExt, CastOp::Bitcast] {
        let mut m = signed();
        let dst = if op == CastOp::ZExt { Ty::U16 } else { Ty::U8 };
        m.functions[0].blocks[0].body = vec![
            m.functions[0].blocks[0].body[0].clone(),
            cast(op, Ty::I8, dst, 1, 2),
            switch(2, vec![Constant::Int(255), Constant::Int(0)]),
        ];
        assert!(run(&m).0.is_empty());
    }
}
#[test]
fn copy_chains_across_physical_block_order_keep_actual_origin() {
    let mut m = fixture();
    m.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::Copy {
            ty: Ty::U8,
            operand: v(2),
        })
        .with_result(v(3)),
        switch(3, vec![Constant::Int(0)]),
    ];
    let mut b = Block::new(BlockId::new(80));
    b.body = vec![
        InstrNode::new(Inst::Copy {
            ty: Ty::U8,
            operand: v(1),
        })
        .with_result(v(2)),
        InstrNode::new(Inst::ExtractField {
            ty: Ty::U8,
            aggregate: v(0),
            field: 0,
        })
        .with_result(v(1)),
    ];
    m.functions[0].blocks.push(b);
    assert_eq!(run(&m).0.len(), 1);
}
#[test]
fn ambiguous_all_result_definitions_and_cyclic_copies_preserve_local_no_origin_skip() {
    let mut m = fixture();
    m.functions[0].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Copy {
            ty: Ty::U8,
            operand: v(0),
        })
        .with_results(vec![v(1), v(1)]),
    );
    assert!(run(&m).0.is_empty());
    m.functions[0].blocks[0].body = vec![
        InstrNode::new(Inst::Copy {
            ty: Ty::U8,
            operand: v(2),
        })
        .with_result(v(1)),
        InstrNode::new(Inst::Copy {
            ty: Ty::U8,
            operand: v(1),
        })
        .with_result(v(2)),
        switch(1, vec![Constant::Int(9)]),
    ];
    assert!(run(&m).0.is_empty());
}
#[test]
fn narrowing_width_mismatch_noninteger_and_non_tag_field_provenance_skip_only_rule2() {
    let mut m = fixture();
    for node in [
        cast(CastOp::Trunc, Ty::U16, Ty::U8, 1, 2),
        cast(CastOp::ZExt, Ty::U16, Ty::U32, 1, 2),
        InstrNode::new(Inst::Copy {
            ty: Ty::Bool,
            operand: v(1),
        })
        .with_result(v(2)),
        InstrNode::new(Inst::ExtractField {
            ty: Ty::U8,
            aggregate: v(0),
            field: 1,
        })
        .with_result(v(2)),
    ] {
        m.functions[0].blocks[0].body = vec![
            InstrNode::new(Inst::ExtractField {
                ty: Ty::U8,
                aggregate: v(0),
                field: 0,
            })
            .with_result(v(1)),
            node,
            switch(2, vec![Constant::Int(9)]),
        ];
        assert!(run(&m).0.is_empty());
    }
}
#[test]
fn actual_indexed_id_preference_is_kept_even_before_first_matching_duplicate() {
    let mut m = fixture();
    for id in 100..106 {
        m.enums.push(EnumDef::new(
            EnumId::new(id),
            "padding",
            vec![variant("P", vec![])],
        ));
    }
    let mut indexed = m.enums[0].clone();
    indexed.discriminants = vec![Some(3), Some(4)];
    m.enums.push(indexed);
    m.functions[0].blocks[0].body[1] = switch(1, vec![Constant::Int(3)]);
    let out = run(&m).0;
    assert_eq!(out.len(), 1);
    assert!(
        matches!(&out[0],ValidationError::ExhaustiveSwitchCasesIncomplete{reason,..}if reason.contains("One = 4"))
    );
}
#[test]
fn malformed_discriminants_missing_enum_or_inadequate_tag_hint_remain_existing_skip() {
    for which in 0..3 {
        let mut m = fixture();
        match which {
            0 => m.enums[0].discriminants = vec![Some(1), Some(1)],
            1 => m.enums.clear(),
            _ => {
                m.enums[0].discriminants = vec![Some(0), Some(300)];
                m.enums[0].repr = Some(EnumTagRepr::U8);
            }
        }
        assert!(run(&m).0.is_empty());
    }
}
#[test]
fn only_flagged_actual_last_terminators_select_coverage_and_no_flag_builds_no_definitions() {
    let mut m = fixture();
    m.functions[0].blocks[0]
        .body
        .push(InstrNode::new(Inst::Unreachable));
    let (out, _, _, _) = run(&m);
    assert!(out.is_empty());
    let layouts = m.layout_table();
    let mut o = Observer::default();
    let mut s = ObservedSession::new(InterpretOptions::default(), &mut o);
    let values = setup(&m, &mut s);
    let mut state = State::default();
    let mut w = Work {
        session: &mut s,
        site: site(),
    };
    state
        .run(&layouts, &m.functions[0], &values, &mut w)
        .unwrap();
    assert_eq!(state.definitions.capacity(), 0);
    drain(&mut state, &mut w);
    values.retire_observed(w.session, w.site).unwrap();
}
#[test]
fn full_noninteger_literal_display_and_unicode_missing_names_keep_error_order() {
    let mut m = fixture();
    m.enums[0].variants[1].name = "é🦀".repeat(300);
    m.functions[0].blocks[0].body[1] = switch(
        1,
        vec![Constant::Aggregate(vec![
            Constant::Float(0.5),
            Constant::Bytes {
                data: b"a".to_vec(),
                utf8: true,
            },
        ])],
    );
    let out = run(&m).0;
    assert_eq!(out.len(), 2);
    assert!(
        matches!(&out[0],ValidationError::ExhaustiveSwitchCasesIncomplete{reason,..}if reason.starts_with("case value ")&&reason.contains(" is not a discriminant of "))
    );
    assert!(
        matches!(&out[1],ValidationError::ExhaustiveSwitchCasesIncomplete{reason,..}if reason.contains(&m.enums[0].variants[1].name))
    );
}
