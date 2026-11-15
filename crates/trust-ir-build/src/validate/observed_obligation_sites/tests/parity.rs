// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn absent_scope_and_absent_site_keep_the_original_well_formed_unsited_boundary() {
    assert!(run(&Module::new("empty")).0.is_empty());
    let mut m = fixture();
    m.proof_obligations[0].site = None;
    assert!(run(&m).0.is_empty());
    m.proof_obligations[0].function = Some(FuncId::new(7));
    assert!(run(&m).0.is_empty());
}
#[test]
fn missing_and_ambiguous_function_scopes_have_distinct_reasons_and_skip_the_site() {
    let mut m = fixture();
    m.proof_obligations[0].function = Some(FuncId::new(99));
    assert_eq!(
        run(&m).0,
        vec![ValidationError::ObligationFunctionScopeUnresolved {
            obligation: 1,
            function: 99,
            reason: "no such function"
        }]
    );
    m.functions.push(function(99, 2, Inst::Unreachable));
    m.functions.push(function(99, 9, Inst::Unreachable));
    assert_eq!(
        run(&m).0,
        vec![ValidationError::ObligationFunctionScopeUnresolved {
            obligation: 1,
            function: 99,
            reason: "the id names more than one function"
        }]
    );
}
#[test]
fn resolved_scope_site_mismatch_precedes_dangling_site_function_block_and_index() {
    let mut m = fixture();
    m.proof_obligations[0].function = Some(FuncId::new(7));
    m.proof_obligations[0].site = Some(ObligationSite::new(
        FuncId::new(99),
        BlockId::new(u32::MAX),
        u32::MAX,
    ));
    assert_eq!(
        run(&m).0,
        vec![ValidationError::ObligationSiteFunctionMismatch {
            obligation: 1,
            site_function: 99,
            scope_function: 7
        }]
    );
}
#[test]
fn each_exact_function_block_and_instruction_range_refusal_remains_separate() {
    for (at, reason) in [
        ((99, 3, 0), "no such function"),
        ((7, 99, 0), "no such block in that function"),
        (
            (7, 3, u32::MAX),
            "instruction index past the end of the block",
        ),
    ] {
        let mut m = fixture();
        m.proof_obligations[0].site = Some(ObligationSite::new(
            FuncId::new(at.0),
            BlockId::new(at.1),
            at.2,
        ));
        assert_eq!(
            run(&m).0,
            vec![ValidationError::ObligationSiteOutOfRange {
                obligation: 1,
                function: at.0,
                block: at.1,
                inst_index: at.2,
                reason
            }]
        );
    }
    let mut m = fixture();
    m.functions.push(m.functions[0].clone());
    assert!(matches!(
        &run(&m).0[0],
        ValidationError::ObligationSiteOutOfRange {
            reason: "no such function",
            ..
        }
    ));
}
#[test]
fn unique_sparse_ids_and_first_physical_duplicate_block_match_the_original_catalog_rules() {
    let mut m = fixture();
    m.functions[0].id = FuncId::new(u32::MAX);
    m.proof_obligations[0].site.as_mut().unwrap().function = FuncId::new(u32::MAX);
    let mut other = m.functions[0].blocks[0].clone();
    other.body[0].inst = Inst::BinOp {
        op: BinOp::Add,
        ty: Ty::U32,
        lhs: ValueId::new(0),
        rhs: ValueId::new(1),
    };
    m.functions[0].blocks.push(other);
    assert_eq!(
        run(&m).0,
        vec![ValidationError::ObligationSiteKindMismatch {
            obligation: 1,
            kind: "arithmetic_safety",
            op: "return"
        }]
    );
    m.functions[0].blocks.swap(0, 1);
    assert!(run(&m).0.is_empty());
}
#[test]
fn all_sixteen_current_kind_families_match_the_original_fixed_instruction_whitelist() {
    let instructions = vec![
        Inst::Return { values: vec![] },
        Inst::Unreachable,
        Inst::Load {
            ty: Ty::U32,
            ptr: ValueId::new(0),
            volatile: false,
            align: None,
        },
        Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U32,
            lhs: ValueId::new(0),
            rhs: ValueId::new(1),
        },
        Inst::Call {
            callee: FuncId::new(0),
            args: vec![],
        },
        Inst::CallCannotUnwind {
            callee: FuncId::new(0),
            args: vec![],
        },
        Inst::Const {
            ty: Ty::U32,
            value: trust_ir::Constant::Int(0),
        },
    ];
    let kinds = kinds();
    assert_eq!(kinds.len(), 16);
    for kind in kinds {
        for inst in &instructions {
            let mut m = fixture();
            m.functions[0].blocks[0].body[0].inst = inst.clone();
            m.proof_obligations[0].kind = kind.clone();
            let expected = !obligation_kind_admits_site_instruction(&kind, inst);
            assert_eq!(run(&m).0.len(), usize::from(expected));
        }
    }
}
#[test]
fn all_fourteen_assert_shapes_keep_bounds_arithmetic_memory_and_panic_families_separate() {
    let mut checks = vec![
        AssertKind::Unspecified,
        AssertKind::DivByZero,
        AssertKind::RemByZero,
        AssertKind::NullPtr,
        AssertKind::BoundsCheck {
            index: ValueId::new(0),
            len: ValueId::new(1),
        },
        AssertKind::MisalignedPtr {
            required: ValueId::new(0),
            found: ValueId::new(1),
        },
    ];
    checks.extend(AssertOverflowOp::ALL.into_iter().map(AssertKind::Overflow));
    assert_eq!(checks.len(), 14);
    for check in checks {
        for kind in [
            ObligationKind::BoundsCheck,
            ObligationKind::ArithmeticSafety,
            ObligationKind::MemorySafety,
            ObligationKind::PanicFreedom,
        ] {
            let inst = Inst::Assert {
                cond: ValueId::new(0),
                kind: check,
                site: None,
            };
            let mut m = fixture();
            m.functions[0].blocks[0].body[0].inst = inst.clone();
            m.proof_obligations[0].kind = kind.clone();
            assert_eq!(
                run(&m).0.len(),
                usize::from(!obligation_kind_admits_site_instruction(&kind, &inst))
            );
        }
    }
}
#[test]
fn unrelated_large_text_and_type_payloads_do_not_enter_this_scope_site_constituent() {
    let mut m = fixture();
    m.functions[0].blocks[0].body[0].inst = Inst::Const {
        ty: Ty::Tuple(vec![]),
        value: trust_ir::Constant::Int(0),
    };
    m.proof_obligations[0].kind = ObligationKind::Custom {
        namespace: "short".into(),
        name: "n".into(),
    };
    let before = run(&m);
    m.functions[0].name = "unread λ\0".repeat(10000);
    m.functions[0].ty = FuncTyId::new(u32::MAX);
    m.proof_obligations[0].description = "unread description".repeat(10000);
    m.proof_obligations[0].formula = Some(ProofFormula::new("opaque", "unread".repeat(10000)));
    m.proof_obligations[0].kind = ObligationKind::Custom {
        namespace: "unread".repeat(10000),
        name: "unread".repeat(10000),
    };
    if let Inst::Const { ty, .. } = &mut m.functions[0].blocks[0].body[0].inst {
        *ty = Ty::Tuple(vec![Ty::Error; 10000]);
    }
    let after = run(&m);
    assert_eq!(before.0, after.0);
    assert_eq!(before.1.events, after.1.events);
}
