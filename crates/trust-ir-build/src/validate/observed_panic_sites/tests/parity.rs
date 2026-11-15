// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn every_actual_kind_operand_count_and_location_outer_shape_matches_original() {
    for kind in [
        AssertKind::Unspecified,
        AssertKind::Overflow(trust_ir::inst::AssertOverflowOp::Add),
        AssertKind::DivByZero,
        AssertKind::RemByZero,
        AssertKind::BoundsCheck {
            index: v(1),
            len: v(2),
        },
        AssertKind::MisalignedPtr {
            required: v(1),
            found: v(2),
        },
        AssertKind::NullPtr,
    ] {
        for location in [
            Ty::Ptr,
            Ty::Ref(Box::new(Ty::Bool)),
            Ty::PtrConst(Box::new(Ty::Bool)),
        ] {
            let mut m = fixture();
            let mut params = vec![Ty::Usize; kind.operand_count()];
            params.push(location.clone());
            m.func_types[1].params = params;
            m.functions[0].blocks[0].params[3].1 = location;
            if let Inst::Assert { kind: k, .. } = &mut m.functions[0].blocks[0].body[1].inst {
                *k = kind;
            }
            assert!(run(&m).0.is_empty());
        }
    }
}
#[test]
fn assert_invoke_and_siteless_or_unrelated_nodes_preserve_original_routes() {
    let mut m = fixture();
    m.functions[0].blocks[0].body[1].inst = Inst::AssertInvoke {
        cond: v(0),
        kind: AssertKind::BoundsCheck {
            index: v(1),
            len: v(2),
        },
        site: PanicSite {
            entry: FuncId::new(9),
            location: PanicLocation::Value(v(3)),
        },
        normal_dest: BlockId::new(2),
        normal_args: vec![],
        unwind_dest: BlockId::new(3),
    };
    assert!(run(&m).0.is_empty());
    m.functions[0].blocks[0].body[1].inst = Inst::Assert {
        cond: v(0),
        kind: AssertKind::Unspecified,
        site: None,
    };
    assert!(run(&m).0.is_empty());
    assert!(run_at(&m, 0, 2).0.is_empty());
}
#[test]
fn global_mutability_tls_missing_and_callee_errors_keep_original_v3_before_v1_order() {
    let mut m = fixture();
    change_site(&mut m, PanicLocation::Global(GlobalId::new(0)));
    m.globals[0].mutable = true;
    m.globals[0].tls = Some(TlsModel::LocalExec);
    m.functions.pop();
    let e = run(&m).0;
    assert!(matches!(
        e[0],
        ValidationError::PanicLocationGlobalInvalid {
            reason: "the global is mutable",
            ..
        }
    ));
    assert!(matches!(e[1], ValidationError::CalleeNotFound { .. }));
    m.globals[0].mutable = false;
    assert!(matches!(
        run(&m).0[0],
        ValidationError::PanicLocationGlobalInvalid {
            reason: "the global is thread-local",
            ..
        }
    ));
    m.globals.clear();
    let e = run(&m).0;
    assert!(matches!(e[0], ValidationError::GlobalNotFound { .. }));
    assert!(matches!(e[1], ValidationError::CalleeNotFound { .. }));
}
#[test]
fn missing_or_ambiguous_entry_and_missing_entry_signature_remain_exact() {
    let mut m = fixture();
    m.functions.push(m.functions[1].clone());
    assert!(matches!(
        &run(&m).0[..],
        [ValidationError::CalleeNotFound { .. }]
    ));
    let mut m = fixture();
    m.functions[1].ty = FuncTyId::new(999);
    assert!(matches!(
        &run(&m).0[..],
        [ValidationError::FuncTypeNotFound {
            func_ty_id: 999,
            ..
        }]
    ));
}
#[test]
fn wrong_entry_shape_preserves_found_spelling_and_short_circuits_location_types() {
    for params in [
        vec![],
        vec![Ty::Bool, Ty::Usize, Ty::Ptr],
        vec![Ty::Usize, Ty::Usize, Ty::PtrMut(Box::new(Ty::Bool))],
    ] {
        let mut m = fixture();
        m.func_types[1].params = params;
        m.functions[0].blocks[0].params[3].1 = Ty::Bool;
        let e = run(&m).0;
        assert!(matches!(
            &e[..],
            [ValidationError::PanicEntrySignatureMismatch { .. }]
        ));
    }
    let mut m = fixture();
    m.func_types[1].is_vararg = true;
    m.func_types[1].returns = vec![Ty::Never];
    let e = run(&m).0;
    let ValidationError::PanicEntrySignatureMismatch {
        expected, found, ..
    } = &e[0]
    else {
        panic!()
    };
    assert_eq!(expected, "fn(usize, usize, ptr | ref | ptr_const) -> ()");
    assert!(found.starts_with("fn(usize, usize, ptr) (variadic) -> ("));
    for params in [vec![], vec![Ty::Usize], vec![Ty::Usize, Ty::Usize]] {
        for returns in [
            vec![],
            vec![Ty::Bool],
            vec![Ty::Tuple(vec![Ty::Bool, Ty::U64])],
        ] {
            for variadic in [false, true] {
                let mut m = fixture();
                m.func_types[1].params = params.clone();
                m.func_types[1].returns = returns.clone();
                m.func_types[1].is_vararg = variadic;
                let errors = run(&m).0;
                let [ValidationError::PanicEntrySignatureMismatch { found, .. }] = &errors[..]
                else {
                    panic!("malformed panic signature")
                };
                let original_list = super::super::super::format_ty_list;
                assert_eq!(
                    found,
                    &format!(
                        "fn{}{} -> {}",
                        original_list(&params),
                        if variadic { " (variadic)" } else { "" },
                        original_list(&returns)
                    )
                );
            }
        }
    }
}
#[test]
fn location_equality_is_strict_including_refinements_but_unknown_value_skips() {
    let mut m = fixture();
    m.functions[0].blocks[0].params[3].1 = Ty::Refine(TyId::new(0), PredId::new(0));
    assert!(
        matches!(&run(&m).0[..],[ValidationError::OperandTypeMismatch {op,role,..}]if op=="assert"&&role=="location")
    );
    change_site(&mut m, PanicLocation::Value(v(999)));
    assert!(run(&m).0.is_empty());
}
#[test]
fn direct_global_address_is_noncanonical_even_if_id_invalid_but_first_definition_wins() {
    let mut m = fixture();
    m.functions[0].blocks[0].body[0] = InstrNode::new(Inst::GlobalAddr {
        global: GlobalId::new(999),
    })
    .with_result(v(3));
    assert!(matches!(
        &run(&m).0[..],
        [ValidationError::NonCanonicalPanicLocation { .. }]
    ));
    m.functions[0].blocks[0]
        .body
        .insert(0, InstrNode::new(Inst::NullPtr).with_result(v(3)));
    assert!(run_at(&m, 0, 2).0.is_empty());
}
#[test]
fn symbol_origin_uses_exact_bytes_addend_and_no_copy_provenance() {
    let mut m = long_symbol();
    assert!(matches!(
        &run(&m).0[..],
        [ValidationError::NonCanonicalPanicLocation { .. }]
    ));
    if let Inst::Const {
        value: Constant::SymbolAddr { addend, .. },
        ..
    } = &mut m.functions[0].blocks[0].body[0].inst
    {
        *addend = 1;
    }
    assert!(run(&m).0.is_empty());
    let mut m = long_symbol();
    m.globals.pop();
    assert!(run(&m).0.is_empty());
    let mut m = long_symbol();
    m.functions[0].blocks[0].body[0].results = vec![v(10)];
    m.functions[0].blocks[0].body.insert(
        1,
        InstrNode::new(Inst::Copy {
            ty: Ty::Ptr,
            operand: v(10),
        })
        .with_result(v(3)),
    );
    assert!(run_at(&m, 0, 2).0.is_empty());
}
#[test]
fn first_definition_scans_real_multi_results_and_physical_block_order() {
    let mut m = fixture();
    let mut origin = InstrNode::new(Inst::GlobalAddr {
        global: GlobalId::new(0),
    });
    origin.results = (100..140).map(v).chain([v(3)]).collect();
    let mut b = Block::new(BlockId::new(99));
    b.body.push(origin);
    m.functions[0].blocks.insert(0, b);
    assert!(matches!(
        &run_at(&m, 1, 1).0[..],
        [ValidationError::NonCanonicalPanicLocation { .. }]
    ));
}
#[test]
fn mutable_location_then_malformed_entry_retains_both_complete_diagnostics() {
    let mut m = fixture();
    change_site(&mut m, PanicLocation::Global(GlobalId::new(0)));
    m.globals[0].mutable = true;
    m.func_types[1].params = vec![Ty::Bool];
    let e = run(&m).0;
    assert!(matches!(
        e[0],
        ValidationError::PanicLocationGlobalInvalid { .. }
    ));
    assert!(matches!(
        e[1],
        ValidationError::PanicEntrySignatureMismatch { .. }
    ));
}
