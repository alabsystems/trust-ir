// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn empty_module_absent_formula_and_empty_bindings_do_not_resolve_an_unused_scope() {
    assert!(run(&Module::new("")).0.is_empty());
    let mut m = fixture();
    m.proof_obligations[0].function = Some(FuncId::new(u32::MAX));
    m.proof_obligations[0].formula = None;
    assert!(run(&m).0.is_empty());
    m.proof_obligations[0].formula = Some(formula(vec![]));
    assert!(run(&m).0.is_empty());
}
#[test]
fn explicit_function_scope_precedes_site_and_unresolved_or_ambiguous_scope_skips_names() {
    for ambiguous in [false, true] {
        let mut m = fixture();
        m.proof_obligations[0].site = Some(ObligationSite::new(FuncId::new(7), BlockId::new(0), 0));
        m.proof_obligations[0].formula = Some(formula(vec![
            ("", ClausePlace::Param { index: u32::MAX }, ClauseSort::Int),
            ("", ClausePlace::World, ClauseSort::Bool),
        ]));
        if ambiguous {
            m.functions.push(m.functions[0].clone());
        } else {
            m.proof_obligations[0].function = Some(FuncId::new(99));
        }
        assert!(run(&m).0.is_empty());
    }
}
#[test]
fn absent_explicit_scope_uses_site_function_without_requiring_this_constituent_to_resolve_its_block()
 {
    let mut m = fixture();
    let expected = run(&m).0;
    m.proof_obligations[0].function = None;
    m.proof_obligations[0].site = Some(ObligationSite::new(
        FuncId::new(7),
        BlockId::new(u32::MAX),
        u32::MAX,
    ));
    assert_eq!(run(&m).0, expected);
}
#[test]
fn all_places_keep_unscoped_world_and_spec_boundaries_without_parameter_reinterpretation() {
    let places = [
        ClausePlace::Param { index: 0 },
        ClausePlace::ResultSlot { index: 0 },
        ClausePlace::MutParamExit { index: 0 },
        ClausePlace::World,
        ClausePlace::WorldPre,
        ClausePlace::WorldPost,
        ClausePlace::Unwind,
        ClausePlace::Value(v(4)),
        ClausePlace::SpecVar { index: u32::MAX },
        ClausePlace::SpecVarNext { index: u32::MAX },
        ClausePlace::ParamPointeeEntry { index: 0 },
    ];
    for place in places {
        let mut m = fixture();
        m.proof_obligations[0].function = None;
        set(&mut m, place, ClauseSort::Int);
        assert_eq!(
            run(&m).0.is_empty(),
            matches!(
                place,
                ClausePlace::World | ClausePlace::SpecVar { .. } | ClausePlace::SpecVarNext { .. }
            )
        );
    }
}
#[test]
fn unicode_blank_and_raw_duplicate_checks_precede_world_and_spec_place_skips() {
    let mut m = fixture();
    m.proof_obligations[0].formula = Some(formula(vec![
        ("\u{2003}\n", ClausePlace::World, ClauseSort::Bool),
        ("x", ClausePlace::SpecVar { index: 0 }, ClauseSort::Bool),
        (" x", ClausePlace::World, ClauseSort::Bool),
        ("x", ClausePlace::SpecVarNext { index: 0 }, ClauseSort::Bool),
        ("", ClausePlace::World, ClauseSort::Bool),
        ("", ClausePlace::World, ClauseSort::Bool),
    ]));
    assert_eq!(run(&m).0.len(), 5);
}
#[test]
fn parameter_and_result_extreme_indices_preserve_unsigned_labels_and_arity() {
    for index in [0, 1, 3, 4, u32::MAX] {
        for place in [
            ClausePlace::Param { index },
            ClausePlace::ResultSlot { index },
        ] {
            let mut m = fixture();
            set(&mut m, place, ClauseSort::Bool);
            run(&m);
        }
    }
}
#[test]
fn missing_signature_keeps_resolution_and_role_errors_without_inventing_a_type() {
    let mut m = fixture();
    m.functions[0].ty = FuncTyId::new(u32::MAX);
    m.proof_obligations[0].formula = Some(formula(vec![
        ("p", ClausePlace::Param { index: 0 }, ClauseSort::Bool),
        ("r", ClausePlace::ResultSlot { index: 0 }, ClauseSort::Bool),
        (
            "m",
            ClausePlace::MutParamExit { index: 0 },
            ClauseSort::Bool,
        ),
        (
            "e",
            ClausePlace::ParamPointeeEntry { index: 0 },
            ClauseSort::Bool,
        ),
    ]));
    assert_eq!(run(&m).0.len(), 5);
}
#[test]
fn all_sixteen_kinds_keep_mutable_exit_world_post_and_unwind_role_refusals_exact() {
    for kind in kinds() {
        for place in [
            ClausePlace::MutParamExit { index: 1 },
            ClausePlace::WorldPost,
            ClausePlace::Unwind,
        ] {
            let mut m = fixture();
            m.proof_obligations[0].kind = kind.clone();
            set(&mut m, place, ClauseSort::BitVec(16));
            run(&m);
        }
    }
}
#[test]
fn mutable_exit_and_entry_pointee_rules_distinguish_references_raw_pointers_and_by_value() {
    for index in [0, 1, 2, 3, u32::MAX] {
        for place in [
            ClausePlace::MutParamExit { index },
            ClausePlace::ParamPointeeEntry { index },
        ] {
            let mut m = fixture();
            m.proof_obligations[0].kind = ObligationKind::Postcondition;
            set(&mut m, place, ClauseSort::Int);
            run(&m);
        }
    }
}
#[test]
fn all_ssa_definition_locations_missing_values_and_bodyless_declarations_match_original_membership()
{
    for id in [4, 5, u32::MAX] {
        let mut m = fixture();
        set(&mut m, ClausePlace::Value(v(id)), ClauseSort::BitVec(32));
        run(&m);
        m.functions[0].blocks.clear();
        assert_eq!(run(&m).0.len(), 1);
    }
}
#[test]
fn defined_but_uninferrable_ssa_value_preserves_complete_recursive_sort_debug() {
    let mut m = fixture();
    m.functions[0].blocks[0]
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }).with_results([v(9)]));
    let sort = ClauseSort::Array(Box::new(ClauseSort::Int), Box::new(ClauseSort::Bool));
    set(&mut m, ClausePlace::Value(v(9)), sort.clone());
    assert_eq!(
        run(&m).0,
        vec![ValidationError::InvalidObligationBinding {
            obligation: 3,
            detail: format!(
                "binding \"x\" names SSA value v9, whose IR type the validator cannot infer, so its sort {sort:?} cannot be checked"
            )
        }]
    );
}
#[test]
fn inferred_ssa_type_uses_last_physical_definition_and_multiple_rows_keep_their_own_maps() {
    let mut m = fixture();
    m.functions[0].blocks[0].body.push(
        InstrNode::new(Inst::Copy {
            ty: Ty::U16,
            operand: v(4),
        })
        .with_results([v(5)]),
    );
    set(&mut m, ClausePlace::Value(v(5)), ClauseSort::BitVec(16));
    m.proof_obligations.push(m.proof_obligations[0].clone());
    assert!(run(&m).0.is_empty());
}
#[test]
fn all_forty_parameter_type_tags_cross_all_seven_sort_tags_against_the_ordinary_rule() {
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
            let mut m = fixture();
            m.func_types[0].params = vec![ty.clone()];
            set(&mut m, ClausePlace::Param { index: 0 }, sort);
            run(&m);
        }
    }
}
#[test]
fn pointer_integer_unknown_width_and_char_diagnostics_preserve_the_target_axis() {
    for ty in [Ty::Isize, Ty::Usize, Ty::Char] {
        let mut m = fixture();
        m.func_types[0].params = vec![ty];
        set(
            &mut m,
            ClausePlace::Param { index: 0 },
            ClauseSort::BitVec(64),
        );
        run(&m);
        m.target_info = Some(trust_ir::TargetInfo {
            triple: "aarch64-unknown-linux-gnu".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        });
        run(&m);
    }
}
#[test]
fn full_nested_type_display_and_raw_quoted_binding_names_survive_every_error_prefix() {
    let mut m = fixture();
    m.func_types[0].params = vec![Ty::Tuple(vec![Ty::U8, Ty::Ref(Box::new(Ty::Bool))])];
    m.proof_obligations[0].kind = ObligationKind::Postcondition;
    m.proof_obligations[0].formula = Some(formula(vec![
        (
            "λ\n\"'\\\0TAIL",
            ClausePlace::MutParamExit { index: 0 },
            ClauseSort::Int,
        ),
        (
            "尾\n\"'\\",
            ClausePlace::ParamPointeeEntry { index: 0 },
            ClauseSort::Int,
        ),
    ]));
    assert_eq!(run(&m).0.len(), 2);
}
#[test]
fn unrelated_schema_payload_rendering_description_and_names_are_never_parsed() {
    let m = fixture();
    let (_, a, cut_a) = run(&m);
    let mut huge = m.clone();
    let p = &mut huge.proof_obligations[0];
    p.description = "unused".repeat(100_000);
    let f = p.formula.as_mut().unwrap();
    f.schema = "unused".repeat(100_000);
    f.payload = "unused".repeat(100_000);
    f.smtlib = Some("unused".repeat(100_000));
    f.sort = Some("unused".repeat(100_000));
    huge.functions[0].name = "unused".repeat(100_000);
    let (_, b, cut_b) = run(&huge);
    assert_eq!(cut_a, cut_b);
    assert_eq!(a.events, b.events);
}
