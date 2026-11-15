// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_summary_and_unread_payloads_keep_original_first_loop_scope() {
    let (m, f, mut s) = fixture();
    let (_, before) = run(&m, &f, &s);
    s.params = vec!["unused".repeat(10000)];
    s.proved = true;
    s.backed_by = Some(trust_ir::ExternRef::new(
        trust_ir::ImportId::new(u32::MAX),
        "unused",
    ));
    let (_, after) = run(&m, &f, &s);
    assert_eq!(before.events, after.events);
}
#[test]
fn all_three_roles_preserve_blank_schema_and_exact_whitespace_name_diagnostics() {
    for role in 0..3 {
        let (m, f, mut s) = fixture();
        let mut c = clause(ClauseSort::Bool, ClausePlace::WorldPre);
        c.schema = "\u{2003}\n".into();
        c.bindings[0].0 = "\u{3000}".into();
        with_role(&mut s, role, c);
        assert_eq!(run(&m, &f, &s).0.len(), 2);
    }
}
#[test]
fn duplicate_binding_names_are_raw_and_every_later_repetition_is_reported_in_order() {
    let (m, f, mut s) = fixture();
    let mut c = clause(ClauseSort::Bool, ClausePlace::WorldPre);
    for name in ["x", " x", "", "", "x"] {
        c.bindings.push((name.into(), c.bindings[0].1.clone()));
    }
    s.requires.push(c);
    assert_eq!(run(&m, &f, &s).0.len(), 5);
}
#[test]
fn parameter_and_result_extreme_indices_keep_original_full_unsigned_arity_errors() {
    for role in 0..3 {
        for index in [0, 1, 3, 4, u32::MAX] {
            for place in [
                ClausePlace::Param { index },
                ClausePlace::ResultSlot { index },
            ] {
                let (m, f, mut s) = fixture();
                with_role(&mut s, role, clause(ClauseSort::Bool, place));
                run(&m, &f, &s);
            }
        }
    }
}
#[test]
fn missing_signature_skips_type_refusal_but_keeps_each_original_resolution_error() {
    let (mut m, mut f, mut s) = fixture();
    f.ty = FuncTyId::new(u32::MAX);
    m.functions[0].ty = f.ty;
    for place in [
        ClausePlace::Param { index: 0 },
        ClausePlace::ResultSlot { index: 0 },
        ClausePlace::MutParamExit { index: 0 },
        ClausePlace::ParamPointeeEntry { index: 0 },
    ] {
        s.requires.push(clause(ClauseSort::Bool, place));
    }
    assert_eq!(run(&m, &f, &s).0.len(), 5);
}
#[test]
fn mutable_exit_role_refusal_precedes_arity_then_type_and_remains_direct_only() {
    for role in 0..3 {
        for index in [0, 1, 2, 3, u32::MAX] {
            let (m, f, mut s) = fixture();
            with_role(
                &mut s,
                role,
                clause(ClauseSort::Int, ClausePlace::MutParamExit { index }),
            );
            run(&m, &f, &s);
        }
    }
}
#[test]
fn world_epoch_and_unwind_rules_keep_proved_and_role_boundaries() {
    for proved in [false, true] {
        for role in 0..3 {
            for place in [
                ClausePlace::World,
                ClausePlace::WorldPre,
                ClausePlace::WorldPost,
                ClausePlace::Unwind,
            ] {
                let (m, f, mut s) = fixture();
                s.proved = proved;
                with_role(&mut s, role, clause(ClauseSort::Bool, place));
                run(&m, &f, &s);
            }
        }
    }
}
#[test]
fn spec_places_are_always_illegal_and_never_reinterpreted_as_parameter_indices() {
    for role in 0..3 {
        for place in [
            ClausePlace::SpecVar { index: 0 },
            ClausePlace::SpecVarNext { index: u32::MAX },
        ] {
            let (m, f, mut s) = fixture();
            with_role(&mut s, role, clause(ClauseSort::Bool, place));
            assert_eq!(run(&m, &f, &s).0.len(), 1);
        }
    }
}
#[test]
fn ssa_membership_checks_all_block_parameters_and_instruction_results_and_declarations() {
    let (m, mut f, mut s) = fixture();
    for id in [4, 5, u32::MAX] {
        s.requires
            .push(clause(ClauseSort::BitVec(32), ClausePlace::Value(v(id))));
    }
    run(&m, &f, &s);
    f.blocks.clear();
    assert_eq!(run(&m, &f, &s).0.len(), 3);
}
#[test]
fn defined_but_uninferrable_ssa_value_keeps_complete_sort_debug_refusal() {
    let (m, mut f, mut s) = fixture();
    f.blocks[0]
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }).with_results([v(9)]));
    s.requires.push(clause(
        ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(ClauseSort::Bool)),
        ClausePlace::Value(v(9)),
    ));
    let out = run(&m, &f, &s).0;
    assert_eq!(out.len(), 1);
    assert!(
        matches!(&out[0],ValidationError::InvalidFunctionSummary {detail,..} if detail.contains("whose IR type the validator cannot infer"))
    );
}
#[test]
fn ssa_type_inference_uses_last_physical_definition_without_cloning_the_map_result() {
    let (m, mut f, mut s) = fixture();
    f.blocks[0].body.push(
        InstrNode::new(Inst::Copy {
            ty: Ty::U16,
            operand: v(4),
        })
        .with_results([v(5)]),
    );
    s.requires
        .push(clause(ClauseSort::BitVec(16), ClausePlace::Value(v(5))));
    assert!(run(&m, &f, &s).0.is_empty());
}
#[test]
fn missing_or_ambiguous_module_function_type_resolution_never_uses_the_supplied_row_as_fallback() {
    let (mut m, f, mut s) = fixture();
    s.requires.push(clause(
        ClauseSort::BitVec(8),
        ClausePlace::Param { index: 0 },
    ));
    m.functions.clear();
    assert_eq!(run(&m, &f, &s).0.len(), 1);
    m.functions = vec![f.clone(), f.clone()];
    assert_eq!(run(&m, &f, &s).0.len(), 1);
}
#[test]
fn every_current_parameter_type_tag_and_all_sort_tags_preserve_full_original_type_check() {
    for ty in types::types() {
        for sort in [
            ClauseSort::Bool,
            ClauseSort::Int,
            ClauseSort::BitVec(8),
            ClauseSort::Float { eb: 8, sb: 24 },
            ClauseSort::RoundingMode,
            ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(ClauseSort::Bool)),
            ClauseSort::Datatype {
                name: "D".into(),
                constructors: vec![],
            },
        ] {
            let (mut m, _, mut s) = fixture();
            m.func_types[0].params = vec![ty.clone()];
            let f = m.functions[0].clone();
            s.requires
                .push(clause(sort, ClausePlace::Param { index: 0 }));
            run(&m, &f, &s);
        }
    }
}
#[test]
fn pointer_integer_unknown_width_and_char_boundary_text_are_exact() {
    for ty in [Ty::Isize, Ty::Usize, Ty::Char] {
        let (mut m, f, mut s) = fixture();
        m.func_types[0].params = vec![ty];
        s.requires.push(clause(
            ClauseSort::BitVec(64),
            ClausePlace::Param { index: 0 },
        ));
        run(&m, &f, &s);
        m.target_info = Some(trust_ir::TargetInfo {
            triple: "aarch64-unknown-linux-gnu".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        });
        run(&m, &f, &s);
    }
}
#[test]
fn wrong_pointee_and_mutable_types_preserve_full_nested_type_display_in_errors() {
    let (mut m, f, mut s) = fixture();
    m.func_types[0].params = vec![Ty::Tuple(vec![Ty::U8, Ty::Ref(Box::new(Ty::Bool))])];
    for place in [
        ClausePlace::MutParamExit { index: 0 },
        ClausePlace::ParamPointeeEntry { index: 0 },
    ] {
        s.ensures.push(clause(ClauseSort::Int, place));
    }
    assert_eq!(run(&m, &f, &s).0.len(), 2);
}
#[test]
fn opaque_schema_payload_and_irrelevant_formula_renderings_are_never_parsed() {
    let (m, f, mut s) = fixture();
    let mut c = clause(ClauseSort::Bool, ClausePlace::WorldPre);
    s.requires.push(c.clone());
    let (_, before) = run(&m, &f, &s);
    c.payload = "not SMT-LIB".repeat(100000);
    c.smtlib = Some("unrelated".repeat(100000));
    c.sort = Some("unrelated".repeat(100000));
    s.requires[0] = c;
    let (_, after) = run(&m, &f, &s);
    assert_eq!(before.events, after.events);
}
