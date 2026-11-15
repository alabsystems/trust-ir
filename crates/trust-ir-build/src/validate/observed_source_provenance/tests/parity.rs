// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
#[test]
fn actual_complete_natural_loop_is_clean_and_absent_carrier_never_derives_context() {
    let mut module = module();
    assert!(parity(&module.functions[0], Some(&module)).is_empty());
    module.functions[0].source_provenance = None;
    module.types.push(Ty::Error);
    assert!(parity(&module.functions[0], Some(&module)).is_empty());
    assert!(parity(&module.functions[0], None).is_empty());
}
#[test]
fn standalone_requires_module_and_empty_loops_return_before_cfg_or_binding_checks() {
    let mut module = module();
    assert_eq!(
        details(&parity(&module.functions[0], None)),
        vec!["module context is required to rederive semantic_body_digest"]
    );
    seal(&mut module, vec![]);
    let errors = parity(&module.functions[0], None);
    assert_eq!(
        details(&errors),
        vec![
            "module context is required to rederive semantic_body_digest",
            "a present carrier must contain at least one source loop"
        ]
    );
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let mut work = Work {
        session: &mut session,
        site: site(),
    };
    let mut state = State::default();
    state.walk(&module.functions[0], None, &mut work).unwrap();
    assert!(state.dominators.is_none());
    assert!(state.global_names.is_empty() && state.loop_hir.is_empty());
    retire(&mut state, &mut work);
    assert!(empty(&state));
}
#[test]
fn schema_all_algorithms_all_zero_fields_binding_context_and_empty_rows_keep_exact_order() {
    let mut module = module();
    seal(&mut module, vec![]);
    let source = module.functions[0].source_provenance.as_mut().unwrap();
    source.schema = u32::MAX;
    let bad = ProofDigest {
        algorithm: ProofDigestAlgorithm::TrustIrStableV1,
        bytes: [0; 32],
    };
    source.compiler_source_digest = bad;
    source.semantic_body_digest = bad;
    source.binding_digest = bad;
    let errors = parity(&module.functions[0], None);
    assert_eq!(
        details(&errors),
        vec![
            "unsupported schema 4294967295 (expected 1)",
            "compiler_source_digest must use sha256, not trust_ir-stable-v1",
            "compiler_source_digest must not be zero",
            "semantic_body_digest must use sha256, not trust_ir-stable-v1",
            "semantic_body_digest must not be zero",
            "binding_digest must use sha256, not trust_ir-stable-v1",
            "binding_digest must not be zero",
            "binding_digest does not cover the stored identity/body/map",
            "module context is required to rederive semantic_body_digest",
            "a present carrier must contain at least one source loop",
        ]
    );
}
#[test]
fn compiler_identity_and_complete_map_tampering_are_caught_by_the_actual_binding_helper() {
    let original = module();
    for case in 0..4 {
        let mut module = original.clone();
        let source = module.functions[0].source_provenance.as_mut().unwrap();
        match case {
            0 => source.compiler_source_digest.bytes[31] ^= 1,
            1 => source.binding_digest.bytes[17] ^= 1,
            2 => source.loops[0].bindings[0].name = "aardvark".into(),
            3 => source.loops[0].hir_local_id = 11,
            _ => unreachable!(),
        }
        assert_eq!(
            details(&parity(&module.functions[0], Some(&module))),
            vec!["binding_digest does not cover the stored identity/body/map"]
        );
    }
}
#[test]
fn real_module_and_function_body_changes_report_exact_stored_and_expected_digest_text() {
    let original = module();
    for case in 0..3 {
        let mut module = original.clone();
        match case {
            0 => module.name.push('x'),
            1 => module.functions[0].name.push('λ'),
            2 => module.functions[0].blocks[0].body.insert(
                0,
                node(Inst::Const {
                    ty: Ty::U32,
                    value: Constant::Int(17),
                }),
            ),
            _ => unreachable!(),
        }
        let stored = module.functions[0]
            .source_provenance
            .as_ref()
            .unwrap()
            .semantic_body_digest;
        let expected = module
            .source_provenance_semantic_digest(module.functions[0].id)
            .unwrap();
        assert_ne!(expected, stored);
        let errors = parity(&module.functions[0], Some(&module));
        assert_eq!(
            details(&errors),
            vec![format!(
                "semantic_body_digest is stale: stored {stored}, expected {expected}"
            )]
        );
    }
}
#[test]
fn actual_semantic_missing_and_duplicate_targets_are_diagnostics_not_silent_context_exemptions() {
    let module = module();
    for id in [0, u32::MAX] {
        let mut function = module.functions[0].clone();
        function.id = FuncId::new(id);
        let errors = parity(&function, Some(&module));
        assert_eq!(
            details(&errors),
            vec![format!(
                "cannot derive semantic_body_digest: source provenance target function #{id} is missing or duplicated"
            )]
        );
        assert!(
            matches!(&errors[0],ValidationError::InvalidSourceProvenance{function,..} if *function==id)
        );
    }
    let mut duplicated = module.clone();
    duplicated.functions.push(duplicated.functions[0].clone());
    assert_eq!(
        details(&parity(&duplicated.functions[0], Some(&duplicated))),
        vec![
            "cannot derive semantic_body_digest: source provenance target function #161 is missing or duplicated"
        ]
    );
    duplicated.functions.clear();
    assert_eq!(
        details(&parity(&module.functions[0], Some(&duplicated))),
        vec![
            "cannot derive semantic_body_digest: source provenance target function #161 is missing or duplicated"
        ]
    );
}
