// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn complete_actual_three_ordinary_consumer_oracles_match_for_empty_and_rich_inputs() {
    for m in [Module::new(""), fixture()] {
        let a = input_empty_or_rich(&m);
        for g in [Group::Contexts, Group::References, Group::Discharged] {
            run(&a, g);
        }
    }
}
fn input_empty_or_rich(m: &Module) -> Authority<'_> {
    if m.proof_certificates.len() >= 2 {
        input(m)
    } else {
        Authority {
            module: m,
            kernel: vec![],
            discharged: vec![],
        }
    }
}
#[test]
fn contexts_preserve_last_scoped_owner_even_when_later_duplicate_is_unscoped() {
    let mut m = fixture();
    m.proof_obligations.push(row(
        0,
        ObligationKind::Postcondition,
        ProofStatus::Pending,
        None,
    ));
    let a = input(&m);
    let expected = oracle(&a, Group::Contexts);
    assert!(
        !expected
            .iter()
            .any(|e| matches!(e, ValidationError::ProofContextAssumeScopeMismatch { .. }))
    );
    run(&a, Group::Contexts);
    m.proof_obligations.push(row(
        0,
        ObligationKind::Postcondition,
        ProofStatus::Pending,
        Some(9),
    ));
    let a = input(&m);
    assert!(oracle(&a, Group::Contexts).iter().any(|e| matches!(
        e,
        ValidationError::ProofContextAssumeScopeMismatch {
            actual_owner: 9,
            ..
        }
    )));
    run(&a, Group::Contexts);
}
#[test]
fn references_use_last_whole_row_and_preserve_authority_claim_kind_scope_site_order() {
    let mut m = fixture();
    m.proof_obligations.push(row(
        1,
        ObligationKind::Postcondition,
        ProofStatus::Pending,
        None,
    ));
    let mut a = input(&m);
    a.kernel.clear();
    let out = oracle(&a, Group::References);
    assert!(out.iter().any(|e| matches!(
        e,
        ValidationError::ProofRefUnresolved {
            obligation: 1,
            missing: false,
            ..
        }
    )));
    assert!(out.iter().any(|e| matches!(
        e,
        ValidationError::ProofRefKindMismatch { obligation: 1, .. }
    )));
    run(&a, Group::References);
}
#[test]
fn contexts_cover_all_six_call_families_and_resolved_ambiguous_missing_drop_glue() {
    let choices = vec![
        Inst::Call {
            callee: FuncId::new(7),
            args: vec![],
        },
        Inst::CallCannotUnwind {
            callee: FuncId::new(7),
            args: vec![],
        },
        Inst::CallIndirect {
            callee: ValueId::new(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
        },
        Inst::CallIndirectCannotUnwind {
            callee: ValueId::new(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
        },
        Inst::Invoke {
            callee: FuncId::new(7),
            args: vec![],
            normal_dest: BlockId::new(9),
            normal_args: vec![],
            unwind_dest: BlockId::new(10),
        },
        Inst::InvokeIndirect {
            callee: ValueId::new(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
            normal_dest: BlockId::new(9),
            normal_args: vec![],
            unwind_dest: BlockId::new(10),
        },
        Inst::Drop {
            ty: Ty::Ptr,
            ptr: ValueId::new(0),
        },
        Inst::DropInvoke {
            ty: Ty::Ptr,
            ptr: ValueId::new(0),
            normal_dest: BlockId::new(9),
            normal_args: vec![],
            unwind_dest: BlockId::new(10),
        },
        Inst::Unreachable,
    ];
    for inst in choices {
        for count in 0..=2 {
            let mut m = fixture();
            m.functions[0].blocks[0].body[0].inst = inst.clone();
            m.drop_glue = (0..count)
                .map(|_| DropGlueEntry {
                    ty: Ty::Ptr,
                    glue: FuncId::new(7),
                })
                .collect();
            run(&input(&m), Group::Contexts);
        }
    }
}
#[test]
fn all_claim_categories_use_complete_original_kind_compatibility_at_both_levels() {
    let kinds = vec![
        ObligationKind::MemorySafety,
        ObligationKind::ArithmeticSafety,
        ObligationKind::PanicFreedom,
        ObligationKind::BoundsCheck,
        ObligationKind::Termination,
        ObligationKind::Ownership,
        ObligationKind::Postcondition,
        ObligationKind::Liveness,
        ObligationKind::TemporalSafety,
        ObligationKind::GiveBackRefinement,
    ];
    let claims = vec![
        ProofAnnotation::NoOverflow,
        ProofAnnotation::InBounds,
        ProofAnnotation::NotNull,
        ProofAnnotation::NoPanic,
        ProofAnnotation::Terminates,
        ProofAnnotation::DataRaceFree,
        ProofAnnotation::Pure,
        ProofAnnotation::Custom(trust_ir::ProofTag::new(0)),
        ProofAnnotation::Wrapping,
        ProofAnnotation::BranchWeights(vec![1, 2]),
    ];
    for kind in kinds {
        for claim in &claims {
            let mut m = fixture();
            m.proof_obligations[1].kind = kind.clone();
            m.functions[0].proofs = vec![claim.clone(), ProofAnnotation::ProofRef(ProofId::new(1))];
            m.functions[0].blocks[0].body[0].proofs = m.functions[0].proofs.clone();
            run(&input(&m), Group::References);
        }
    }
}
#[test]
fn discharged_currency_cannot_back_contexts_or_refs_and_identity_is_exact() {
    let m = fixture();
    let mut a = input(&m);
    a.kernel.clear();
    run(&a, Group::Discharged);
    assert!(oracle(&a, Group::Discharged).is_empty());
    assert!(oracle(&a, Group::Contexts).iter().any(|e| matches!(
        e,
        ValidationError::ProofContextAssumeNotAuthoritative { .. }
    )));
    run(&a, Group::Contexts);
    run(&a, Group::References);
    a.discharged[2].prover.push('x');
    assert_eq!(oracle(&a, Group::Discharged).len(), 1);
    run(&a, Group::Discharged);
}
