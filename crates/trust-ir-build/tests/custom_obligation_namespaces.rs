// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// `ObligationKind::Custom { namespace }` is admitted from a PINNED list.
//
// The namespace is authority-bearing, not decorative: downstream it is a
// routing capability (`trust.vc.hardened` grants a full-verifier route,
// trust-mc ownership and an assertion lowering; `trust.vc.unbounded_allocation`
// is confined to the certificate-import lane and must never reach a
// whole-function CHC). Before this rule the field was free text in TrustIr —
// every `ObligationKind::Custom` site in the crate was codec or digest, with no
// validator arm at all — so a module could mint a producer identity no
// component defines and a consumer keying on it would honour it.
//
// WHICH namespaces are pinned is an OWNER-REVISABLE decision. The seed was
// measured, not chosen: it is exactly the sibling `trust-verifier-api` crate's
// `ADMITTED_OBLIGATION_NAMESPACES` — the crate that owns this vocabulary and
// whose `ObligationKind` the TrustIr wire enum mirrors. See the constant's
// rustdoc.

use trust_ir::Module;
use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};
use trust_ir::value::ProofId;
use trust_ir_build::is_admitted_obligation_namespace;
use trust_ir_build::validate::{ADMITTED_OBLIGATION_NAMESPACES, ValidationError, validate_module};

fn module_with_custom(namespace: &str, name: &str) -> Module {
    let mut module = Module::new("ns");
    module.proof_obligations.push(ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Custom {
            namespace: namespace.to_string(),
            name: name.to_string(),
        },
        ProofStatus::Pending,
        "k",
    ));
    module
}

#[test]
fn every_pinned_namespace_is_admitted_through_validate_module() {
    // The DEFAULT entry point, not an opt-in helper: that reachability is what
    // the residual ledger disqualified the old state for.
    for namespace in ADMITTED_OBLIGATION_NAMESPACES {
        let module = module_with_custom(namespace, "anything");
        assert_eq!(
            validate_module(&module),
            Vec::new(),
            "{namespace} must be admitted"
        );
    }
}

#[test]
fn an_unpinned_namespace_is_refused_by_validate_module() {
    let module = module_with_custom("vendor.acme", "audited");
    assert_eq!(
        validate_module(&module),
        vec![ValidationError::UnpinnedCustomObligationNamespace {
            obligation: 0,
            namespace: "vendor.acme".to_string(),
            name: "audited".to_string(),
        }]
    );
}

#[test]
fn the_refusal_is_the_documented_default_for_an_unmeasured_namespace() {
    // Two strings a reader might expect to be pinned and which deliberately
    // are not: this repo's own codec fixture invention, and trust-cg's
    // `unrecognized_obligation_kinds_grant_no_authority` vendor string. No
    // component in the constellation defines either. The fixtures that use
    // them exercise the codec/digest/authority layers, none of which runs
    // `validate_module` — which is why they keep passing.
    for namespace in ["trust.concurrency", "vendor"] {
        let module = module_with_custom(namespace, "data_race");
        assert!(
            validate_module(&module)
                .iter()
                .any(|e| matches!(e, ValidationError::UnpinnedCustomObligationNamespace { .. })),
            "{namespace} must be refused until an owner pins it"
        );
    }
}

#[test]
fn admission_is_byte_exact_and_never_a_prefix_test() {
    // A `starts_with` test would hand `trust.vc.hardened`'s routing capability
    // to anything under it, and would let the unbounded-allocation lane
    // inherit `trust.vc`'s. Case folding would do the same.
    for forged in [
        "trust.vc.hardened.evil",
        "trust.vc.hardened ",
        " trust.vc.hardened",
        "TRUST.VC.HARDENED",
        "trust.vc.hardene",
        "",
    ] {
        assert!(
            !is_admitted_obligation_namespace(forged),
            "{forged:?} must not be admitted"
        );
        assert!(
            validate_module(&module_with_custom(forged, "x"))
                .iter()
                .any(|e| matches!(e, ValidationError::UnpinnedCustomObligationNamespace { .. })),
            "{forged:?} must be refused"
        );
    }
}

#[test]
fn name_is_not_sealed_within_an_admitted_namespace() {
    // `name` is a label, never an authority test: the hardened lane forwards
    // an unrecognized name as `Unknown`, and the two name-sensitive consumers
    // narrow on exact equality, so an unknown name already fails closed
    // THERE. Sealing it here would refuse honest rows for no gain.
    for name in ["", "lemma_validity", "something nobody has defined", "…"] {
        assert_eq!(
            validate_module(&module_with_custom("trust.proof_item", name)),
            Vec::new(),
            "name {name:?} must not be admission-tested"
        );
    }
}

#[test]
fn every_offending_obligation_is_named_once() {
    let mut module = Module::new("ns");
    for (i, namespace) in ["vendor.a", "trust.vc", "vendor.b"].iter().enumerate() {
        module.proof_obligations.push(ProofObligation::new(
            ProofId::new(i as u32),
            ObligationKind::Custom {
                namespace: (*namespace).to_string(),
                name: "x".to_string(),
            },
            ProofStatus::Pending,
            "k",
        ));
    }
    let offenders: Vec<u32> = validate_module(&module)
        .into_iter()
        .filter_map(|e| match e {
            ValidationError::UnpinnedCustomObligationNamespace { obligation, .. } => {
                Some(obligation)
            }
            _ => None,
        })
        .collect();
    assert_eq!(
        offenders,
        vec![0, 2],
        "one refusal per unpinned row, in id order"
    );
}

#[test]
fn a_nominal_obligation_kind_is_untouched() {
    let mut module = Module::new("ns");
    module.proof_obligations.push(ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Termination,
        ProofStatus::Pending,
        "k",
    ));
    assert_eq!(validate_module(&module), Vec::new());
}

/// WS1.9 (F-023, F-025): the two namespaces pinned by owner decision, each the
/// TrustIr spelling of a `trust_verifier_api` kind this wire enum lacks —
/// `Protocol`, and the E6 facets `pure` / `deterministic` / `total` / `nopanic`.
/// Positive: a row in either validates through the DEFAULT entry point, with
/// every facet name (and, as everywhere, an unpinned name too, since `name` is
/// a label).
#[test]
fn ws1_9_pins_trust_protocol_and_trust_facet() {
    for namespace in ["trust.protocol", "trust.facet"] {
        assert!(
            is_admitted_obligation_namespace(namespace),
            "{namespace} is pinned by WS1.9"
        );
    }
    for name in ["pure", "deterministic", "total", "nopanic", "not-a-facet"] {
        assert_eq!(
            validate_module(&module_with_custom("trust.facet", name)),
            Vec::new(),
            "trust.facet/{name} must validate"
        );
    }
    assert_eq!(
        validate_module(&module_with_custom("trust.protocol", "state_machine")),
        Vec::new()
    );
}

/// Negative twins of the WS1.9 pins: the byte-exact rule applies to the new
/// rows as to the old — a sub-namespace, a case variant, a facet name spelled
/// INTO the namespace and the pre-WS1.9 fixture invention `trust.concurrency`
/// are all refused with the named reason.
#[test]
fn ws1_9_pins_are_byte_exact() {
    for forged in [
        "trust.facet.pure",
        "trust.protocol.v2",
        "TRUST.FACET",
        "trust.facets",
        "trust.protoco",
        "trust.concurrency",
    ] {
        assert!(!is_admitted_obligation_namespace(forged));
        assert_eq!(
            validate_module(&module_with_custom(forged, "pure")),
            vec![ValidationError::UnpinnedCustomObligationNamespace {
                obligation: 0,
                namespace: forged.to_string(),
                name: "pure".to_string(),
            }],
            "{forged:?} must be refused by name"
        );
    }
}

#[test]
fn the_pinned_list_is_sorted_and_duplicate_free() {
    // Not cosmetic: the list is the vocabulary, and a duplicate or an
    // out-of-order insert is the shape a careless edit takes.
    let mut sorted = ADMITTED_OBLIGATION_NAMESPACES.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(sorted.as_slice(), ADMITTED_OBLIGATION_NAMESPACES);
}
