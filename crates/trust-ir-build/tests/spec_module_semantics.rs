// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_ir::{
    Module, ProofKind, SpecAnchor, SpecInvariant, SpecLinkViolation, SpecModule, SpecOrigin,
    SpecProjectionTarget, SpecProof, SpecVar, SpecWaiver, TEMPORAL_FIELD_PATH_PROJECTION_V1,
    validate_spec_structure,
};
use trust_ir_build::{ValidationError, validate_module, validate_spec_module_semantics};

fn bare_spec(name: &str, action: &str) -> SpecModule {
    let mut spec = SpecModule::new(name);
    spec.actions.push(action.to_string());
    spec
}

fn anchor(machine: &str, action: &str, project: Option<&str>) -> SpecAnchor {
    SpecAnchor {
        machine: machine.to_string(),
        action: action.to_string(),
        function: None,
        rust_symbol: format!("crate::{machine}::{action}"),
        span: "fixture.rs:1:1".to_string(),
        project: project.map(str::to_string),
        projection_target: None,
    }
}

fn proof(machine: &str, action: &str, proof_name: &str) -> SpecProof {
    SpecProof {
        machine: machine.to_string(),
        action: action.to_string(),
        proof_name: proof_name.to_string(),
        kind: ProofKind::Kani,
    }
}

fn structural_violations(errors: &[ValidationError]) -> Vec<&SpecLinkViolation> {
    errors
        .iter()
        .filter_map(|error| match error {
            ValidationError::InvalidSpecStructure { violation } => Some(violation),
            _ => None,
        })
        .collect()
}

#[test]
fn duplicate_machine_identity_reaches_focused_and_full_validation() {
    let mut module = Module::new("duplicate_machine");
    module.spec_modules.push(bare_spec("Machine", "Step"));
    module.spec_modules.push(bare_spec("Machine", "Step"));

    let focused = validate_spec_module_semantics(&module);
    assert!(matches!(
        structural_violations(&focused).as_slice(),
        [SpecLinkViolation::DuplicateMachineIdentity { machine }] if machine == "Machine"
    ));
    assert!(validate_module(&module).iter().any(|error| matches!(
        error,
        ValidationError::InvalidSpecStructure {
            violation: SpecLinkViolation::DuplicateMachineIdentity { machine }
        } if machine == "Machine"
    )));
}

#[test]
fn duplicate_member_identities_are_all_reported_once() {
    let mut spec = bare_spec("Machine", "Step");
    spec.actions.push("Step".to_string());
    spec.vars = vec![SpecVar::new("state", "Int"), SpecVar::new("state", "Bool")];
    spec.invariants = vec![
        SpecInvariant::new("Safe", "state >= 0"),
        SpecInvariant::new("Safe", "state < 10"),
    ];

    let violations = validate_spec_structure(&[spec]);
    let members: Vec<_> = violations
        .iter()
        .filter_map(|violation| match violation {
            SpecLinkViolation::DuplicateMemberIdentity { member, name, .. } => {
                Some((*member, name.as_str()))
            }
            _ => None,
        })
        .collect();
    assert_eq!(
        members,
        vec![
            ("action", "Step"),
            ("invariant", "Safe"),
            ("variable", "state")
        ]
    );
}

#[test]
fn foreign_bindings_cannot_escape_their_containing_machine() {
    let mut a = bare_spec("A", "Step");
    a.anchors.push(anchor("B", "Step", Some("crate::project")));
    a.waivers.push(SpecWaiver {
        machine: "B".to_string(),
        action: "Step".to_string(),
        reason: "not implemented".to_string(),
    });
    a.proofs.push(proof("B", "Step", "step_refines"));
    let b = bare_spec("B", "Step");

    let violations = validate_spec_structure(&[a.clone(), b.clone()]);
    let sources: Vec<_> = violations
        .iter()
        .filter_map(|violation| match violation {
            SpecLinkViolation::ReferenceContainerMismatch { from, .. } => Some(*from),
            _ => None,
        })
        .collect();
    assert_eq!(sources, vec!["anchor", "proof", "waiver"]);

    let mut module = Module::new("foreign_bindings");
    module.spec_modules = vec![a, b];
    assert_eq!(
        structural_violations(&validate_spec_module_semantics(&module)).len(),
        3
    );
}

#[test]
fn proof_reference_closure_is_structural_without_a_manifest() {
    let mut spec = bare_spec("Machine", "Step");
    spec.proofs.push(proof("Machine", "Missing", "bad_action"));
    spec.proofs.push(proof("Ghost", "Step", "bad_machine"));

    let violations = validate_spec_structure(&[spec.clone()]);
    assert!(violations.iter().any(|violation| matches!(
        violation,
        SpecLinkViolation::ActionMissing { from: "proof", action, .. } if action == "Missing"
    )));
    assert!(violations.iter().any(|violation| matches!(
        violation,
        SpecLinkViolation::MachineMissing { from: "proof", machine, .. } if machine == "Ghost"
    )));

    let mut module = Module::new("proof_closure");
    module.spec_modules.push(spec);
    assert_eq!(
        structural_violations(&validate_spec_module_semantics(&module)).len(),
        2
    );
}

#[test]
fn duplicate_bindings_conflicts_and_whitespace_projection_fail_closed() {
    let mut spec = bare_spec("Machine", "Step");
    let malformed = anchor("Machine", "Step", Some(" \t "));
    spec.anchors = vec![malformed.clone(), malformed];
    spec.waivers = vec![
        SpecWaiver {
            machine: "Machine".to_string(),
            action: "Step".to_string(),
            reason: "first rationale".to_string(),
        },
        SpecWaiver {
            machine: "Machine".to_string(),
            action: "Step".to_string(),
            reason: "second rationale".to_string(),
        },
    ];

    let violations = validate_spec_structure(&[spec]);
    assert_eq!(
        violations
            .iter()
            .filter(|violation| matches!(
                violation,
                SpecLinkViolation::DuplicateBindingIdentity { .. }
            ))
            .count(),
        2
    );
    assert!(
        violations
            .iter()
            .any(|violation| matches!(violation, SpecLinkViolation::AnchorWaiverConflict { .. }))
    );
    assert_eq!(
        violations
            .iter()
            .filter(|violation| matches!(violation, SpecLinkViolation::ProjectionMissing { .. }))
            .count(),
        1,
        "duplicate malformed anchors should normalize to one L2 diagnostic"
    );
}

#[test]
fn blank_executable_module_identity_is_rejected() {
    let module = Module::new(" \t ");
    assert_eq!(
        validate_spec_module_semantics(&module),
        vec![ValidationError::BlankModuleName]
    );
    assert!(
        validate_module(&module)
            .iter()
            .any(|error| matches!(error, ValidationError::BlankModuleName))
    );
}

#[test]
fn linked_anchors_require_typed_action_and_projection_targets() {
    let mut spec = SpecModule::linked("Machine");
    spec.actions.push("Step".to_string());
    spec.anchors
        .push(anchor("Machine", "Step", Some("crate::project")));

    let violations = validate_spec_structure(&[spec.clone()]);
    let missing: Vec<_> = violations
        .iter()
        .filter_map(|violation| match violation {
            SpecLinkViolation::TypedTargetRequired { target, .. } => Some(*target),
            _ => None,
        })
        .collect();
    assert_eq!(missing, vec!["action function", "projection"]);

    let mut module = Module::new("linked_embedded");
    module.spec_modules.push(spec);
    assert_eq!(
        structural_violations(&validate_spec_module_semantics(&module))
            .iter()
            .filter(|violation| matches!(violation, SpecLinkViolation::TypedTargetRequired { .. }))
            .count(),
        2
    );
}

#[test]
fn external_origin_cannot_weaken_linked_action_identity() {
    let mut spec = SpecModule::linked("Machine");
    spec.origin = SpecOrigin::External("Machine.tla".to_string());
    spec.actions.push("Step".to_string());
    let mut external = anchor("Machine", "Step", Some(TEMPORAL_FIELD_PATH_PROJECTION_V1));
    external.projection_target = Some(SpecProjectionTarget::ExternalUnresolved);
    spec.anchors.push(external);

    let violations = validate_spec_structure(&[spec]);
    assert!(
        violations.iter().any(|violation| matches!(
            violation,
            SpecLinkViolation::TypedTargetRequired {
                target: "action function",
                ..
            }
        )),
        "external origin must not weaken linked action identity: {violations:?}"
    );
    assert!(!violations.iter().any(|violation| matches!(
        violation,
        SpecLinkViolation::TypedTargetRequired {
            target: "projection",
            ..
        }
    )));
}
