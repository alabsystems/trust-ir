// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn ordinary_success_and_public_standalone_convenience_have_exact_parity() {
    let f = simple();
    assert!(parity(&f, None).errors.is_empty());
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    assert_eq!(
        validate_function_observed(&f, &mut session, site()).unwrap(),
        validate_function(&f)
    );
}
#[test]
fn multiple_pass_diagnostics_keep_original_whole_function_order() {
    let f = fixture();
    let report = parity(&f, None);
    assert!(report.errors.len() > 5);
    assert!(
        report
            .errors
            .iter()
            .any(|e| matches!(e, ValidationError::AccessAlignInvalid { .. }))
    );
    assert!(
        report
            .errors
            .iter()
            .any(|e| matches!(e, ValidationError::WrappingConflictsWithNoOverflow { .. }))
    );
    assert!(
        report
            .errors
            .iter()
            .any(|e| matches!(e, ValidationError::FuncAttrClaimViolated { .. }))
    );
}
#[test]
fn empty_body_preserves_early_metadata_checks_and_skips_instruction_effect_classification() {
    let mut f = fixture();
    f.blocks.clear();
    f.body_gate = Some(trust_ir::BodyGate::Gated {
        authority: " ".into(),
        evidence: None,
    });
    let report = parity(&f, None);
    assert!(!report.has_indirect_call);
    assert!(!report.errors.is_empty());
    assert!(!report.errors.iter().any(|e| matches!(
        e,
        ValidationError::FuncAttrClaimViolated { .. } | ValidationError::AccessAlignInvalid { .. }
    )));
}
#[test]
fn module_context_keeps_cross_function_effect_claims_out_of_local_report() {
    let f = fixture();
    let module = Module::new("");
    let report = parity(&f, Some(&module));
    assert!(
        !report
            .errors
            .iter()
            .any(|e| matches!(e, ValidationError::FuncAttrClaimViolated { .. }))
    );
    assert!(
        parity(&f, None)
            .errors
            .iter()
            .any(|e| matches!(e, ValidationError::FuncAttrClaimViolated { .. }))
    );
}
#[test]
fn every_indirect_call_route_keeps_original_fused_classification() {
    for instruction in [
        Inst::CallIndirect {
            callee: v(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
        },
        Inst::CallIndirectCannotUnwind {
            callee: v(0),
            sig: FuncTyId::new(0),
            args: vec![],
            calling_conv: CallingConv::C,
        },
        Inst::InvokeIndirect {
            callee: v(0),
            sig: FuncTyId::new(0),
            args: vec![],
            normal_dest: BlockId::new(1),
            normal_args: vec![],
            unwind_dest: BlockId::new(2),
            calling_conv: CallingConv::C,
        },
    ] {
        let f = function(vec![InstrNode::new(instruction)]);
        assert!(parity(&f, None).has_indirect_call);
    }
    assert!(!parity(&simple(), None).has_indirect_call);
}
#[test]
fn malformed_duplicate_blocks_values_and_missing_entry_keep_diagnostic_parity() {
    let mut f = fixture();
    f.entry = BlockId::new(77);
    f.blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Copy {
            ty: Ty::I32,
            operand: v(900),
        })
        .with_result(v(0)),
    );
    f.blocks.push(f.blocks[0].clone());
    assert!(!parity(&f, None).errors.is_empty());
}
#[test]
fn aggregation_keeps_prefix_and_all_owned_helper_rows_in_order() {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut s = State {
        errors: vec![error(1), error(2)],
        pending: vec![error(3), owned_error(), error(5)],
        indirect: false,
    };
    let expected = vec![error(1), error(2), error(3), owned_error(), error(5)];
    s.merge(&mut work).unwrap();
    assert_eq!(s.errors, expected);
    assert_eq!(s.pending.capacity(), 0);
    drain(&mut s, &mut work);
    assert!(empty(&s));
}

#[test]
fn complete_module_context_observes_real_binding_body_digest_and_natural_loop_success() {
    let module = source_module();
    assert!(
        parity(&module.functions[0], Some(&module))
            .errors
            .is_empty()
    );
    let report = parity(&module.functions[0], None);
    assert!(report.errors.iter().any(|error|matches!(error,ValidationError::InvalidSourceProvenance{detail,..} if detail=="module context is required to rederive semantic_body_digest")));
}
#[test]
fn source_carrier_tampering_remains_an_ordered_original_failure_in_complete_composition() {
    let mut module = source_module();
    module.functions[0]
        .source_provenance
        .as_mut()
        .unwrap()
        .loops[0]
        .bindings[0]
        .name = "changed".into();
    let report = parity(&module.functions[0], Some(&module));
    assert!(report.errors.iter().any(|error|matches!(error,ValidationError::InvalidSourceProvenance{detail,..} if detail=="binding_digest does not cover the stored identity/body/map")));
}
