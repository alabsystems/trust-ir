// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn actual_global_and_function_nested_closure_environments_match_complete_original() {
    assert!(run(&fixture()).0.is_empty());
}
#[test]
fn root_arity_is_reported_before_known_capture_errors_in_actual_stored_order() {
    let mut m = fixture();
    captures(&mut m)[0] = Constant::Int(1);
    captures(&mut m)[1] = Constant::Bool(false);
    captures(&mut m).push(Constant::Uninit);
    assert!(matches!(
        &run(&m).0[..],
        [
            ValidationError::ClosureCaptureArityMismatch { .. },
            ValidationError::ClosureCaptureTypeMismatch {
                capture_index: 0,
                ..
            },
            ValidationError::ClosureCaptureTypeMismatch {
                capture_index: 1,
                ..
            }
        ]
    ));
}
#[test]
fn missing_closure_rows_keep_exact_global_and_function_location_text() {
    let mut m = fixture();
    m.closure_types.clear();
    m.globals[0].name = "G'é🦀".into();
    m.functions[0].name = "f'中".into();
    let e = run(&m).0;
    assert!(
        matches!(&e[..],[ValidationError::ClosureTypeNotFound{location:a,closure_ty_id:0},ValidationError::ClosureTypeNotFound{location:b,closure_ty_id:1}]if a=="global 'G'é🦀'"&&b=="function 'f'中' bb7")
    );
}
#[test]
fn capture_integer_signedness_and_char_scalar_boundaries_use_actual_value_rule() {
    for (ty, n) in [
        (Ty::U8, 256),
        (Ty::U8, -1),
        (Ty::I8, 128),
        (Ty::Char, 0xd800),
        (Ty::Char, 0x110000),
        (Ty::Refine(TyId::new(0), trust_ir::value::PredId::new(0)), 1),
    ] {
        let mut m = fixture();
        m.globals.clear();
        m.closure_types[1].captures = vec![ty];
        m.functions[0].blocks[0].body[0].inst = Inst::Const {
            ty: c(1),
            value: closure(vec![Constant::Int(n)]),
        };
        assert_eq!(run(&m).0.len(), 1);
    }
}
#[test]
fn original_module_pointer_width_decides_usize_capture_without_host_default() {
    let mut m = fixture();
    m.globals.clear();
    m.closure_types[1].captures = vec![Ty::Usize];
    m.functions[0].blocks[0].body[0].inst = Inst::Const {
        ty: c(1),
        value: closure(vec![Constant::Int(1i128 << 32)]),
    };
    m.target_info = Some(trust_ir::TargetInfo {
        triple: "wasm32-unknown-unknown".into(),
        pointer_size: 4,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    assert_eq!(run(&m).0.len(), 1);
    m.target_info.as_mut().unwrap().pointer_size = 8;
    assert!(run(&m).0.is_empty());
}
#[test]
fn actual_late_nested_vector_mismatch_is_reported_at_own_capture_index() {
    let mut m = fixture();
    let Constant::Vector(v) = &mut captures(&mut m)[1] else {
        panic!()
    };
    v[1] = Constant::Int(256);
    assert!(
        matches!(&run(&m).0[..],[ValidationError::ClosureCaptureTypeMismatch{closure_ty_id:0,capture_index:1,actual,..}]if actual=="vector[2]")
    );
}
#[test]
fn nonnull_typed_pointer_spellings_defer_only_local_capture_error_to_module_checker() {
    use trust_ir::FatPtrKind;
    for (ty, value) in [
        (
            Ty::Ref(Box::new(Ty::Bool)),
            Constant::symbol_addr_with_addend("unresolved", 7),
        ),
        (
            Ty::PtrConst(Box::new(Ty::Bool)),
            Constant::symbol_addr("unresolved"),
        ),
        (
            Ty::FatPtr(FatPtrKind::Str),
            Constant::Aggregate(vec![Constant::symbol_addr("unresolved"), Constant::Int(-1)]),
        ),
    ] {
        let mut m = fixture();
        m.globals.clear();
        m.closure_types[1].captures = vec![ty];
        m.functions[0].blocks[0].body[0].inst = Inst::Const {
            ty: c(1),
            value: closure(vec![value]),
        };
        assert!(run(&m).0.is_empty());
    }
}
#[test]
fn excess_unknown_capture_types_keep_ordinary_unit_sentinel_not_new_refusals() {
    let mut m = fixture();
    captures(&mut m).push(Constant::Closure {
        func: FuncId::new(u32::MAX),
        captures: vec![Constant::Uninit],
    });
    assert!(matches!(
        &run(&m).0[..],
        [ValidationError::ClosureCaptureArityMismatch { .. }]
    ));
}
#[test]
fn nonclosure_root_and_unknown_aggregate_children_keep_original_scoped_leniency() {
    let mut m = fixture();
    m.globals[0].ty = Ty::Tuple(vec![c(999)]);
    m.globals[0].initializer = Some(Constant::Aggregate(vec![closure(vec![Constant::Uninit])]));
    assert!(run(&m).0.is_empty());
}
#[test]
fn every_actual_record_sequence_set_array_and_splat_child_inventory_is_walked_once() {
    for value in [
        Constant::Record(vec![("unread".into(), closure(vec![Constant::Uninit]))]),
        Constant::Sequence(vec![closure(vec![Constant::Uninit])]),
        Constant::Set(vec![closure(vec![Constant::Uninit])]),
        Constant::Array(vec![closure(vec![Constant::Uninit])]),
        Constant::Splat {
            elem: Box::new(closure(vec![Constant::Uninit])),
            len: u64::MAX,
        },
    ] {
        let mut m = fixture();
        m.globals[0].ty = Ty::Unit;
        m.globals[0].initializer = Some(value);
        assert!(run(&m).0.is_empty());
    }
}
#[test]
fn splat_declared_length_is_never_expanded_or_used_as_constant_child_work() {
    let mut traces = Vec::new();
    for len in [2, u64::MAX] {
        let mut m = fixture();
        m.globals[0].ty = Ty::Unit;
        m.globals[0].initializer = Some(Constant::Splat {
            elem: Box::new(Constant::Uninit),
            len,
        });
        let (e, o, end) = run(&m);
        assert!(e.is_empty());
        traces.push(o.events[..end].to_vec());
    }
    assert_eq!(traces[0], traces[1]);
}
#[test]
fn complete_symbol_shape_name_and_signed_addend_are_retained_in_error() {
    let m = rich_bad();
    let e = run(&m).0;
    assert!(
        matches!(&e[1],ValidationError::ClosureCaptureTypeMismatch{location,expected,actual,..}if location.contains("é🦀Global中")&&expected=="bool"&&actual==&symbol().shape_label())
    );
}
#[test]
fn all_physical_global_then_function_block_and_node_error_order_is_preserved() {
    let mut m = fixture();
    captures(&mut m)[0] = Constant::Int(1);
    m.functions[0].blocks[0].body[0].inst = Inst::Const {
        ty: c(1),
        value: closure(vec![Constant::Bool(false)]),
    };
    let duplicate = m.functions[0].blocks[0].clone();
    m.functions[0].blocks.push(duplicate);
    let e = run(&m).0;
    assert_eq!(e.len(), 3);
    assert!(
        matches!(&e[0],ValidationError::ClosureCaptureTypeMismatch{location,..}if location=="global 'G'")
    );
    assert!(e[1..].iter().all(|e|matches!(e,ValidationError::ClosureCaptureTypeMismatch{location,..}if location=="function 'body' bb7")));
}
#[test]
fn absent_initializers_nonconstant_nodes_and_unconstrained_closure_target_ids_are_unchanged() {
    let mut m = fixture();
    m.globals.push(global("none", c(999), None));
    if let Constant::Closure { func, .. } = m.globals[0].initializer.as_mut().unwrap() {
        *func = FuncId::new(u32::MAX);
    }
    m.functions[0].blocks[0]
        .body
        .push(InstrNode::new(Inst::Undef { ty: c(999) }));
    assert!(run(&m).0.is_empty());
}
