// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn duplicate_display_collisions_default_first_and_last_block_definition_match() {
    let errors = parity(&fixture());
    assert_eq!(
        errors,
        vec![
            ValidationError::DuplicateSwitchCase {
                block: 0,
                value: "0".into()
            },
            ValidationError::BranchTargetNotFound {
                block: 0,
                target: 99
            },
            ValidationError::BranchTargetNotFound {
                block: 0,
                target: 8
            },
            ValidationError::BranchTargetNotFound {
                block: 0,
                target: 7
            },
            ValidationError::UnreachableBlock(1),
            ValidationError::UnreachableBlock(2),
        ]
    );
}
#[test]
fn all_invoke_families_reach_both_normal_and_unwind_destinations() {
    let normal_dest = BlockId::new(1);
    let unwind_dest = BlockId::new(2);
    let instructions = vec![
        Inst::Invoke {
            callee: FuncId::new(5),
            args: vec![],
            normal_dest,
            normal_args: vec![],
            unwind_dest,
        },
        Inst::AssertInvoke {
            cond: ValueId::new(0),
            kind: AssertKind::DivByZero,
            site: PanicSite {
                entry: FuncId::new(5),
                location: PanicLocation::Value(ValueId::new(0)),
            },
            normal_dest,
            normal_args: vec![],
            unwind_dest,
        },
        Inst::DropInvoke {
            ty: Ty::Bool,
            ptr: ValueId::new(0),
            normal_dest,
            normal_args: vec![],
            unwind_dest,
        },
        Inst::InvokeIndirect {
            callee: ValueId::new(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
            normal_dest,
            normal_args: vec![],
            unwind_dest,
        },
    ];
    for instruction in instructions {
        assert!(
            parity(&function(
                vec![block(0, instruction), return_block(1), return_block(2)],
                0
            ))
            .is_empty()
        );
    }
}
#[test]
fn absent_entry_and_nonfinal_terminators_keep_original_reachability_rules() {
    let mut nonfinal = branch(0, 99);
    nonfinal.body.push(InstrNode::new(Inst::NullPtr));
    let f = function(vec![nonfinal, return_block(1), return_block(1)], 0);
    assert_eq!(
        parity(&f),
        vec![
            ValidationError::UnreachableBlock(1),
            ValidationError::UnreachableBlock(1)
        ]
    );
    let mut missing = f;
    missing.entry = BlockId::new(42);
    assert!(parity(&missing).is_empty());
    assert!(parity(&function(vec![], 0)).is_empty());
}
#[test]
fn cyclic_duplicate_missing_edges_and_wide_chain_preserve_bfs_results() {
    let f = function(
        vec![
            block(
                0,
                Inst::CondBr {
                    cond: ValueId::new(0),
                    then_target: BlockId::new(1),
                    then_args: vec![],
                    else_target: BlockId::new(1),
                    else_args: vec![],
                },
            ),
            branch(1, 0),
            branch(2, 99),
        ],
        0,
    );
    assert_eq!(
        parity(&f),
        vec![
            ValidationError::BranchTargetNotFound {
                block: 2,
                target: 99
            },
            ValidationError::UnreachableBlock(2)
        ]
    );
    let mut chain: Vec<_> = (0..2048).map(|id| branch(id, id + 1)).collect();
    chain.push(return_block(2048));
    assert!(parity(&function(chain, 0)).is_empty());
}
#[test]
fn raw_unicode_and_large_byte_case_spellings_compare_actual_full_keys() {
    let cases = vec![
        Constant::SymbolAddr {
            symbol: "λ".repeat(3000),
            addend: -1,
        },
        Constant::SymbolAddr {
            symbol: "λ".repeat(3000),
            addend: -1,
        },
        Constant::Bytes {
            data: vec![255; 2049],
            utf8: false,
        },
        Constant::Bytes {
            data: vec![255; 2049],
            utf8: false,
        },
    ];
    let f = function(vec![block(0, switch(cases, vec![0; 4], 0))], 0);
    let errors = parity(&f);
    assert_eq!(errors.len(), 2);
    assert!(
        matches!(&errors[0], ValidationError::DuplicateSwitchCase { value, .. } if value.len() > 6000)
    );
    assert!(
        matches!(&errors[1], ValidationError::DuplicateSwitchCase { value, .. } if value.len() > 4098)
    );
}
#[test]
fn float_keys_preserve_complete_ordinary_diagnostics_and_refuse_final_publication() {
    let f = function(
        vec![block(
            0,
            switch(
                vec![
                    Constant::Int(1),
                    Constant::Int(1),
                    Constant::Float(f64::NAN),
                    Constant::Float(f64::NAN),
                    Constant::Float(1.0),
                    Constant::Float(-0.0),
                    Constant::Int(0),
                ],
                vec![0; 7],
                99,
            ),
        )],
        0,
    );
    let errors = parity(&f);
    assert!(errors.iter().any(|e| matches!(e,
        ValidationError::DuplicateSwitchCase { value, .. } if value == "NaN")));
    assert!(matches!(
        errors.last(),
        Some(ValidationError::BranchTargetNotFound { target: 99, .. })
    ));
    let (_, baseline) = observed(&f);
    let stop = baseline.events.len();
    let mut observer = Observer {
        stop_at: Some(stop),
        ..Observer::default()
    };
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_control_flow_observed(&f, &mut session, site()),
        Err(ObservedValueError::AdmissionRefused)
    );
    assert_eq!(session.first_refusal().unwrap().cause, "original stop");
    assert_eq!(
        session.first_refusal().unwrap().progress.phase,
        ExecutionPhase::Publication
    );
    assert_eq!(&observer.events[..stop], baseline.events.as_slice());
    assert!(
        observer.events[stop..]
            .iter()
            .all(|e| e.phase == ExecutionPhase::ScratchRetirement)
    );
}
