// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn standalone_and_module_keep_their_distinct_single_and_multi_result_rules() {
    let f = fixture();
    let module = Module::new("types");
    let standalone = parity(&f, None);
    let contextual = parity(&f, Some(&module));
    assert_eq!(standalone.get(&2), Some(&Ty::Tuple(vec![Ty::U32, Ty::Ptr])));
    assert!(!contextual.contains_key(&2));
    for rows in [&standalone, &contextual] {
        assert_eq!(rows.get(&3), Some(&Ty::I64));
        assert_eq!(rows.get(&4), Some(&Ty::Bool));
        assert!(!rows.contains_key(&5));
        assert_eq!(rows.get(&6), Some(&Ty::Vector(Box::new(Ty::Bool), 8)));
    }
}

#[test]
fn reverse_block_borrow_chain_reads_complete_phase_one_before_any_overwrite() {
    let map = parity(&fixture(), None);
    assert_eq!(map.get(&7), map.get(&9));
    assert_eq!(map.get(&8), map.get(&9));
    assert!(matches!(
        map.get(&7),
        Some(Ty::FatPtr(FatPtrKind::Slice(_)))
    ));
}

#[test]
fn physical_last_declarations_and_late_borrow_correction_match_ordinary_maps() {
    let mut f = function(vec![
        node(Inst::Borrow { ptr: v(3) }, &[1]),
        node(Inst::Undef { ty: Ty::U16 }, &[1]),
        node(Inst::Undef { ty: Ty::U8 }, &[2]),
    ]);
    f.blocks[0].params.push((v(1), Ty::U32));
    let mut tail = Block::new(b(8));
    tail.params.push((v(2), Ty::I128));
    tail.params.push((v(3), Ty::FatPtr(FatPtrKind::Str)));
    f.blocks.push(tail);
    for module in [None, Some(Module::new("last"))] {
        let map = parity(&f, module.as_ref());
        assert_eq!(map.get(&1), Some(&Ty::FatPtr(FatPtrKind::Str)));
        assert_eq!(map.get(&2), Some(&Ty::I128));
    }
}

#[test]
fn concrete_module_lookup_preserves_indexed_preference_sparse_fallback_and_missing_signatures() {
    let mut module = Module::new("lookup");
    for ty in [Ty::U8, Ty::U16, Ty::U32] {
        module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![ty, Ty::Bool],
                abi: None,
                is_vararg: false,
            })
            .unwrap();
    }
    for (id, signature) in [(1, 0), (1, 1), (9, 2)] {
        module.functions.push(Function::new(
            FuncId::new(id),
            "callee",
            FuncTyId::new(signature),
            b(0),
        ));
    }
    let f = function(vec![
        node(
            Inst::Call {
                callee: FuncId::new(1),
                args: vec![],
            },
            &[1, 2, 3],
        ),
        node(
            Inst::CallCannotUnwind {
                callee: FuncId::new(9),
                args: vec![],
            },
            &[4, 5],
        ),
        node(
            Inst::Call {
                callee: FuncId::new(8),
                args: vec![],
            },
            &[6],
        ),
        node(
            Inst::CallIndirect {
                callee: v(0),
                sig: FuncTyId::new(99),
                args: vec![],
                calling_conv: CallingConv::C,
            },
            &[7],
        ),
    ]);
    let map = parity(&f, Some(&module));
    assert_eq!(map.get(&1), Some(&Ty::U16));
    assert_eq!(map.get(&2), Some(&Ty::Bool));
    assert_eq!(map.get(&4), Some(&Ty::U32));
    assert!(!map.contains_key(&3) && !map.contains_key(&6) && !map.contains_key(&7));
    assert!(parity(&f, None).is_empty());
}

#[test]
fn direct_indirect_and_invoke_families_expand_exact_signature_returns() {
    let mut module = Module::new("calls");
    module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Tuple(vec![Ty::U8]), Ty::Bool],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    module.functions.push(Function::new(
        FuncId::new(0),
        "callee",
        FuncTyId::new(0),
        b(0),
    ));
    let instructions = vec![
        Inst::Call {
            callee: FuncId::new(0),
            args: vec![],
        },
        Inst::CallCannotUnwind {
            callee: FuncId::new(0),
            args: vec![],
        },
        Inst::Invoke {
            callee: FuncId::new(0),
            args: vec![],
            normal_dest: b(1),
            normal_args: vec![],
            unwind_dest: b(2),
        },
        Inst::CallIndirect {
            callee: v(9),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
        },
        Inst::CallIndirectCannotUnwind {
            callee: v(9),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
        },
        Inst::InvokeIndirect {
            callee: v(9),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
            normal_dest: b(1),
            normal_args: vec![],
            unwind_dest: b(2),
        },
    ];
    for instruction in instructions {
        let f = function(vec![node(instruction, &[1, 2, 3])]);
        let rows = parity(&f, Some(&module));
        assert_eq!(rows.get(&1), Some(&Ty::Tuple(vec![Ty::U8])));
        assert_eq!(rows.get(&2), Some(&Ty::Bool));
        assert!(!rows.contains_key(&3));
        assert!(parity(&f, None).is_empty());
    }
}

#[test]
fn dialect_arity_landing_pad_and_no_result_instructions_keep_the_original_boundary() {
    for count in [0, 1, 3] {
        let mut op = trust_ir::dialect::DialectInst::new("opaque", "results");
        op.result_tys = vec![Ty::U64; count];
        let f = function(vec![node(Inst::DialectOp(Box::new(op)), &[1, 2, 3, 4])]);
        assert_eq!(parity(&f, None).len(), if count == 1 { 4 } else { 0 });
        assert_eq!(parity(&f, Some(&Module::new("dialect"))).len(), count);
    }
    let f = function(vec![
        node(
            Inst::LandingPad {
                is_cleanup: true,
                catch_type_indices: vec![0],
            },
            &[1, 2, 3],
        ),
        node(
            Inst::Drop {
                ty: Ty::U8,
                ptr: v(1),
            },
            &[4],
        ),
        node(Inst::Return { values: vec![v(1)] }, &[5]),
    ]);
    assert!(parity(&f, None).is_empty());
    assert_eq!(
        parity(&f, Some(&Module::new("pad"))),
        BTreeMap::from([(1, Ty::Ptr), (2, Ty::I32)])
    );
}

#[test]
fn nested_owned_types_clone_exactly_and_empty_or_unused_results_do_not_infer_extra_ids() {
    let ty = Ty::Tuple(vec![
        Ty::Ref(Box::new(Ty::Tuple(vec![Ty::U8; 256]))),
        Ty::Array(TyId::new(4), u64::MAX),
    ]);
    let f = function(vec![
        node(Inst::Undef { ty: ty.clone() }, &[1, 2]),
        node(Inst::Undef { ty }, &[]),
    ]);
    assert_eq!(parity(&f, None).len(), 2);
    assert_eq!(parity(&f, Some(&Module::new("nested"))).len(), 1);
    assert!(parity(&function(vec![]), None).is_empty());
}

#[test]
fn observed_lookup_returns_exact_borrowed_row_and_missing_without_new_authority() {
    let f = fixture();
    let (map, _) = run(&f, None);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let found = map
        .get_observed(v(7), &mut session, site())
        .unwrap()
        .unwrap();
    assert!(core::ptr::eq(
        found,
        &map.rows.iter().find(|(id, _)| *id == 7).unwrap().1
    ));
    assert!(
        map.get_observed(v(999), &mut session, site())
            .unwrap()
            .is_none()
    );
    map.retire_observed(&mut session, site()).unwrap();
}
