// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;

#[test]
fn all_current_constructor_witnesses_keep_original_counts_and_mismatch_diagnostics() {
    let mut shapes = BTreeSet::new();
    for instruction in witnesses::all() {
        assert!(shapes.insert(instruction.shape()));
        for count in [0, 1, 2, 4] {
            parity(&module(vec![node(instruction.clone(), count)]));
        }
    }
    assert_eq!(shapes, InstShape::ALL.iter().copied().collect());
}

#[test]
fn direct_indirect_and_all_invoke_call_forms_use_exact_signature_return_count() {
    let instructions = [
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
            callee: v(),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
        },
        Inst::CallIndirectCannotUnwind {
            callee: v(),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
        },
        Inst::InvokeIndirect {
            callee: v(),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
            normal_dest: b(1),
            normal_args: vec![],
            unwind_dest: b(2),
        },
    ];
    for instruction in instructions {
        for actual in [0, 1, 3, 4] {
            let mut m = module(vec![node(instruction.clone(), actual)]);
            m.func_types.push(FuncTy {
                params: vec![],
                returns: vec![Ty::U8, Ty::Bool, Ty::Ptr],
                abi: None,
                is_vararg: false,
            });
            m.functions.insert(
                0,
                Function::new(FuncId::new(0), "callee", FuncTyId::new(0), b(0)),
            );
            let errors = parity(&m);
            assert_eq!(errors.len(), usize::from(actual != 3));
            if actual != 3 {
                assert!(matches!(
                    errors[0],
                    ValidationError::InstrResultArityMismatch { expected: 3, .. }
                ));
            }
        }
    }
}

#[test]
fn indexed_duplicate_preference_sparse_fallback_and_missing_function_signature_are_preserved() {
    let mut m = module(vec![
        node(
            Inst::Call {
                callee: FuncId::new(1),
                args: vec![],
            },
            0,
        ),
        node(
            Inst::Call {
                callee: FuncId::new(9),
                args: vec![],
            },
            0,
        ),
        node(
            Inst::Call {
                callee: FuncId::new(8),
                args: vec![],
            },
            0,
        ),
        node(
            Inst::CallIndirect {
                callee: v(),
                sig: FuncTyId::new(99),
                args: vec![],
                calling_conv: CallingConv::C,
            },
            0,
        ),
    ]);
    for count in [1, 2, 3] {
        m.func_types.push(FuncTy {
            params: vec![],
            returns: vec![Ty::U8; count],
            abi: None,
            is_vararg: false,
        });
    }
    let caller = m.functions.pop().unwrap();
    for (id, signature) in [(1, 0), (1, 1), (9, 2)] {
        m.functions.push(Function::new(
            FuncId::new(id),
            "callee",
            FuncTyId::new(signature),
            b(0),
        ));
    }
    m.functions.push(caller);
    let errors = parity(&m);
    assert_eq!(errors.len(), 2);
    assert!(matches!(
        errors[0],
        ValidationError::InstrResultArityMismatch { expected: 2, .. }
    ));
    assert!(matches!(
        errors[1],
        ValidationError::InstrResultArityMismatch { expected: 3, .. }
    ));
}

#[test]
fn physical_function_block_node_order_and_exact_opcode_tokens_are_retained() {
    let mut m = fixture();
    let mut duplicate = m.functions[0].clone();
    duplicate.blocks[0].id = b(99);
    m.functions.push(duplicate);
    let errors = parity(&m);
    assert_eq!(errors.len(), 8);
    for (i, op) in ["undef", "landingpad", "return", "dialect"]
        .into_iter()
        .enumerate()
    {
        assert!(
            matches!(&errors[i],ValidationError::InstrResultArityMismatch {block:0,op:actual,..} if actual==op)
        );
        assert!(
            matches!(&errors[i+4],ValidationError::InstrResultArityMismatch {block:99,op:actual,..} if actual==op)
        );
    }
}

#[test]
fn result_type_payloads_and_unrelated_proof_metadata_are_not_walked_or_cloned() {
    let shallow = module(vec![node(Inst::Undef { ty: Ty::U32 }, 1)]);
    let mut deep = module(vec![node(
        Inst::Undef {
            ty: Ty::Tuple(vec![Ty::U8; 100_000]),
        },
        1,
    )]);
    deep.functions[0].name = "name".repeat(100_000);
    deep.functions[0].blocks[0].body[0].proofs = vec![ProofAnnotation::Tainted; 100_000];
    assert_eq!(run(&shallow).1.events, run(&deep).1.events);
    assert!(run(&deep).0.is_empty());
    parity(&module(vec![node(
        Inst::Undef {
            ty: Ty::Tuple(vec![Ty::Error; 32]),
        },
        1,
    )]));
}

#[test]
fn dialect_declared_count_is_exact_without_scanning_or_cloning_unpaired_types() {
    let mut a = module(vec![node(dialect(5000), 5000)]);
    let mut c = module(vec![node(dialect(5000), 5000)]);
    if let Inst::DialectOp(op) = &mut c.functions[0].blocks[0].body[0].inst {
        op.result_tys = vec![Ty::Tuple(vec![Ty::Error; 100]); 5000];
    }
    assert_eq!(run(&a).1.events, run(&c).1.events);
    assert!(run(&c).0.is_empty());
    a.functions[0].blocks[0].body[0].results.pop();
    let errors = parity(&a);
    assert!(matches!(
        errors[0],
        ValidationError::InstrResultArityMismatch {
            expected: 5000,
            actual: 4999,
            ..
        }
    ));
}

#[test]
fn pair_and_no_result_operators_keep_exact_constant_arity_despite_malformed_results() {
    let m = module(vec![
        node(
            Inst::Drop {
                ty: Ty::U32,
                ptr: v(),
            },
            1,
        ),
        node(
            Inst::LandingPad {
                is_cleanup: true,
                catch_type_indices: vec![],
            },
            3,
        ),
    ]);
    let errors = parity(&m);
    assert!(matches!(
        errors[0],
        ValidationError::InstrResultArityMismatch {
            expected: 0,
            actual: 1,
            ..
        }
    ));
    assert!(matches!(
        errors[1],
        ValidationError::InstrResultArityMismatch {
            expected: 2,
            actual: 3,
            ..
        }
    ));
}

#[test]
fn empty_module_bodyless_functions_empty_blocks_and_correct_counts_are_clean() {
    assert!(parity(&Module::new("empty")).is_empty());
    assert!(parity(&module(vec![])).is_empty());
    let mut m = module(vec![
        node(Inst::Undef { ty: Ty::U8 }, 1),
        node(Inst::Return { values: vec![] }, 0),
    ]);
    m.functions.push(Function::new(
        FuncId::new(1),
        "external",
        FuncTyId::new(99),
        b(0),
    ));
    assert!(parity(&m).is_empty());
}
