// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! D1a: every digest-keyed entry point of this crate refuses a module the
//! binary writer cannot encode BY NAME (`ValidationError::
//! ModuleHasNoWireIdentity`), because `wire_identity_blocker` is an adapter
//! over the writer run in check mode (`Module::wire_image_refusal`), not a
//! hand-written list of constructs.
//!
//! The hand-written list this replaced omitted the producer-internal
//! `Ty::Error`, which JSON and MessagePack spell: `wire_identity_blocker`
//! answered `None`, and the linked import walk then panicked inside
//! `stable_digest`. Test rung: evidence on these inputs, never proof.

use std::panic::{AssertUnwindSafe, catch_unwind};

use trust_ir::Module;
use trust_ir::proof::RejectingModuleProofAuthority;
use trust_ir::ty::Ty;
use trust_ir_build::{ModuleSet, ValidationError, validate_linked_module, wire_identity_blocker};

#[path = "../../trust-ir-conformance/tests/generate/signature_abi.rs"]
mod abi_fixture;

fn module_with_producer_internal_type() -> Module {
    let mut module = Module::new("producer-internal");
    module.types.push(Ty::Error);
    module
}

fn names_the_producer_internal_type(error: &ValidationError) -> bool {
    matches!(
        error,
        ValidationError::ModuleHasNoWireIdentity { construct, .. } if construct.contains("Ty::Error")
    )
}

/// Kind (i): red before D1a (`None`).
#[test]
fn wire_identity_blocker_names_a_producer_internal_type() {
    let module = module_with_producer_internal_type();
    let blocker = wire_identity_blocker(&module).expect("a Ty::Error module has no wire identity");
    assert!(names_the_producer_internal_type(&blocker), "{blocker:?}");
    assert!(
        wire_identity_blocker(&Module::new("control")).is_none(),
        "an empty module has a wire identity"
    );
}

/// Kind (i): red before D1a (a panic in `stable_digest`, reached through the
/// linked walk's root guard).
#[test]
fn the_linked_walk_refuses_a_root_without_a_wire_identity_by_name() {
    let module = module_with_producer_internal_type();
    let set = ModuleSet::new(std::iter::empty());
    let errors = catch_unwind(AssertUnwindSafe(|| {
        validate_linked_module(&module, &set, &RejectingModuleProofAuthority)
            .errors()
            .to_vec()
    }))
    .expect("a refusal, never a panic");
    assert!(
        errors.iter().any(names_the_producer_internal_type),
        "{errors:?}"
    );
}

/// T-A6 (the adapter half). `wire_identity_blocker` is an adapter over
/// `Module::wire_image_refusal`: it answers exactly when the writer refuses,
/// keeps the location strings the carriers it already named had, and keeps
/// the precedence (a scope chain before a completeness claim before a typed
/// signature ABI past its limits before `Ty::Error`). Mutation check: a blocker that answered from its own list
/// again would miss `Ty::Error` (red above) or disagree here.
#[test]
fn the_blocker_answers_exactly_when_the_writer_refuses() {
    use trust_ir::value::{InlinedAt, ScopeData, SourceSpan};
    use trust_ir::{BlockId, FuncId, FuncTyId, Function, ModuleCompleteness};

    let mut chained = Module::new("chained");
    let mut function = Function::new(FuncId::new(3), "inlined", FuncTyId::new(0), BlockId::new(0));
    function.scopes = Some(vec![
        ScopeData::new(None, None),
        ScopeData {
            parent: Some(0),
            span: None,
            inlined_at: Some(InlinedAt {
                span: SourceSpan {
                    file: 0,
                    line: 1,
                    col: 1,
                },
                callee: "callee".into(),
            }),
        },
    ]);
    chained.functions.push(function);
    let mut claimed = Module::new("claimed");
    claimed.completeness = Some(ModuleCompleteness::Complete);
    // A typed signature ABI (wire v60) past its node budget, on an unused
    // signature row.
    let mut placed = abi_fixture::module().expect("signature_abi::module: test fixture");
    let unused = placed.func_types[0].clone();
    placed.func_types.push(unused);
    if let Some(abi) = placed.func_types[1].abi.as_mut() {
        abi.target.features = vec!["n".to_owned(); 70_000];
    }

    for module in [
        &Module::new("plain"),
        &abi_fixture::module().expect("signature_abi::module: test fixture"),
        &chained,
        &claimed,
        &placed,
        &module_with_producer_internal_type(),
    ] {
        assert_eq!(
            wire_identity_blocker(module).is_some(),
            module.wire_image_refusal().is_some(),
            "{}",
            module.name
        );
    }
    let location = |module: &Module| match wire_identity_blocker(module) {
        Some(ValidationError::ModuleHasNoWireIdentity { location, .. }) => location,
        other => panic!("{other:?}"),
    };
    assert_eq!(location(&chained), "function 'inlined' lexical scope #1");
    assert_eq!(location(&claimed), "module");
    assert_eq!(location(&placed), "signature #1");
    assert!(
        matches!(
            wire_identity_blocker(&placed),
            Some(ValidationError::ModuleHasNoWireIdentity { construct, .. })
                if construct.starts_with("typed signature ABI exceeds encoding limits: ")
        ),
        "the construct string the hand-written blocker gave it"
    );

    let mut all = module_with_producer_internal_type();
    all.functions = chained.functions.clone();
    all.completeness = Some(ModuleCompleteness::Complete);
    assert_eq!(location(&all), "function 'inlined' lexical scope #1");
    // The descriptor ranks after the carriers pinned before it and ahead of
    // `Ty::Error`.
    let mut later = placed.clone();
    later.types.push(Ty::Error);
    assert_eq!(location(&later), "signature #1");
    later.completeness = Some(ModuleCompleteness::Complete);
    assert_eq!(location(&later), "module");
}

/// Kind (i): red before D1a. The bundle coverage paths are digest-keyed too:
/// the legacy `coverage_assurance_report` binds the ROOT module by its
/// `stable_digest`, and `coverage_establishment_report` binds the bundle's
/// EMBEDDED module (through the bundle's `validate`). Each consulted the old
/// hand-written blocker, which answered `None` for `Ty::Error`, and then
/// panicked inside `stable_digest`. Both now report one named refusal and
/// stay unchecked.
#[test]
// The legacy rule is exercised because it is still a public digest-keyed
// entry point; it keeps its wire-identity refusal until it is deleted.
#[allow(deprecated)]
fn the_bundle_coverage_paths_refuse_a_producer_internal_type_by_name() {
    use trust_ir::proof::ProofLineageManifest;
    use trust_ir::request::{NativeAdapterInput, NativeBundleProducer, NativeVerificationBundle};
    use trust_ir_build::{
        CoverageInputs, coverage_assurance_report, coverage_establishment_report,
    };

    let bundle_for = |module: Module| {
        NativeVerificationBundle::new(
            NativeBundleProducer::TrustIr,
            NativeAdapterInput::TrustIrModule,
            Module::new("encodable").stable_digest(),
            module,
            ProofLineageManifest::default(),
        )
    };

    // The root carries `Ty::Error`; the bundle is for an encodable module.
    let root = module_with_producer_internal_type();
    let legacy = catch_unwind(AssertUnwindSafe(|| {
        coverage_assurance_report(&root, Some(&bundle_for(Module::new("encodable"))))
    }))
    .expect("the legacy coverage rule refuses, never panics");
    assert!(!legacy.is_checked());
    let errors = legacy.into_errors();
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(names_the_producer_internal_type(&errors[0]), "{errors:?}");

    // The bundle's embedded module carries `Ty::Error`.
    let bundle = bundle_for(module_with_producer_internal_type());
    let inputs = CoverageInputs {
        attestation: None,
        solved_bundles: &[],
        attachments: &[],
        replay: None,
    };
    let report = catch_unwind(AssertUnwindSafe(|| {
        coverage_establishment_report(&bundle, inputs)
    }))
    .expect("the coverage establishment rule refuses, never panics");
    assert!(!report.is_checked());
    assert_eq!(report.refusals().len(), 1, "{:?}", report.refusals());
    assert!(
        names_the_producer_internal_type(&report.refusals()[0]),
        "{:?}",
        report.refusals()
    );
}
