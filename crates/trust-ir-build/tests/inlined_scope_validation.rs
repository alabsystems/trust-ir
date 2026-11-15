// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS4.19 / F-082: the validator's rules for a lexical scope's inlining chain
// link (`ScopeData.inlined_at`). The link is debug metadata, so a wrong one
// cannot make a false verdict — but a consumer fails closed on it rather than
// letting a producer bug become a debugger lie, exactly as it does for the
// tree invariant and for every other span's file index.
//
//   * positive: a well-formed link validates;
//   * negative twin: a call-site span whose file index is out of the
//     `Module.files` table is `SpanFileIndexOutOfRange` (the same rule every
//     span obeys — an inlined-at span is a span);
//   * `InvalidInlinedScope`: the outermost scope cannot have been inlined,
//     and a link must name its callee;
//   * mutation control: each twin differs from the positive fixture in ONE
//     field, and repairing that field validates again.

use trust_ir::{InlinedAt, Module, ScopeData, SourceSpan, Ty};
use trust_ir_build::{ModuleBuilder, ValidationError, validate_module};

fn module_with_chain() -> Module {
    let mut mb = ModuleBuilder::new("ws4_19_validation");
    let caller_rs = mb.intern_file("src/caller.rs");
    let island = mb.intern_file("src/island.clean");
    let sig = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let mut fb = mb.function("caller", sig);
    fb.set_scopes(vec![
        ScopeData::new(
            None,
            Some(SourceSpan {
                file: caller_rs,
                line: 10,
                col: 1,
            }),
        ),
        ScopeData {
            parent: Some(0),
            span: Some(SourceSpan {
                file: island,
                line: 3,
                col: 1,
            }),
            inlined_at: Some(InlinedAt {
                span: SourceSpan {
                    file: caller_rs,
                    line: 12,
                    col: 9,
                },
                callee: "clean::island::checked_index".into(),
            }),
        },
    ]);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U32);
    fb.switch_to_block(entry);
    fb.set_scope(1);
    let one = fb.iconst(Ty::U32, 1);
    let sum = fb.add(Ty::U32, x, one);
    fb.set_scope(0);
    fb.ret(vec![sum]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn scope_mut(m: &mut Module, index: usize) -> &mut ScopeData {
    &mut m.functions[0].scopes.as_mut().expect("scopes")[index]
}

#[test]
fn well_formed_chain_link_validates() {
    let m = module_with_chain();
    assert_eq!(m.files.len(), 2);
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
}

/// Negative twin: the call-site span's file index is checked against the
/// file table like every other span. Repairing the index validates again.
#[test]
fn inlined_at_file_index_out_of_range_is_refused() {
    let mut m = module_with_chain();
    let file_count = m.files.len();
    scope_mut(&mut m, 1)
        .inlined_at
        .as_mut()
        .expect("link")
        .span
        .file = file_count as u32;
    let errors = validate_module(&m);
    assert!(
        !errors.is_empty(),
        "out-of-range call-site file must be refused"
    );
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::SpanFileIndexOutOfRange { file, file_count: n }
                if *file == file_count as u32 && *n == file_count
        )),
        "expected SpanFileIndexOutOfRange, got {errors:?}"
    );
    // The scope's OWN span is in range, so nothing else is reported for it.
    assert!(
        !errors
            .iter()
            .any(|e| matches!(e, ValidationError::InvalidInlinedScope { .. })),
        "the link itself is well-formed: {errors:?}"
    );

    // Mutation control: same module, index repaired.
    scope_mut(&mut m, 1)
        .inlined_at
        .as_mut()
        .expect("link")
        .span
        .file = 0;
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
}

/// The outermost scope is the function's own body: it cannot have been
/// inlined from anywhere.
#[test]
fn root_scope_with_chain_link_is_refused() {
    let mut m = module_with_chain();
    let link = scope_mut(&mut m, 1).inlined_at.take().expect("link");
    scope_mut(&mut m, 0).inlined_at = Some(link);
    let errors = validate_module(&m);
    assert!(!errors.is_empty(), "an inlined root scope must be refused");
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidInlinedScope {
                function: 0,
                scope: 0,
                ..
            }
        )),
        "expected InvalidInlinedScope on scope #0, got {errors:?}"
    );
    let rendered = errors
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("\n");
    assert!(rendered.contains("cannot have been inlined"), "{rendered}");

    // Mutation control: moving the link back to scope #1 validates.
    let link = scope_mut(&mut m, 0).inlined_at.take().expect("link");
    scope_mut(&mut m, 1).inlined_at = Some(link);
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
}

/// A link must name its callee: an empty display path is refused, never
/// shown as "inlined from <unknown>".
#[test]
fn chain_link_without_callee_is_refused() {
    let mut m = module_with_chain();
    scope_mut(&mut m, 1)
        .inlined_at
        .as_mut()
        .expect("link")
        .callee
        .clear();
    let errors = validate_module(&m);
    assert!(!errors.is_empty(), "a nameless callee must be refused");
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidInlinedScope {
                function: 0,
                scope: 1,
                detail
            } if detail.contains("callee")
        )),
        "expected InvalidInlinedScope naming the callee, got {errors:?}"
    );

    // Mutation control.
    scope_mut(&mut m, 1)
        .inlined_at
        .as_mut()
        .expect("link")
        .callee = "clean::island::checked_index".into();
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
}

/// The chain does not relax the tree invariant: an inlined scope still needs
/// an earlier parent (a link is not a substitute for `parent`).
#[test]
fn chain_link_does_not_replace_the_parent_edge() {
    let mut m = module_with_chain();
    scope_mut(&mut m, 1).parent = Some(1);
    let errors = validate_module(&m);
    assert!(!errors.is_empty(), "self-parent must still be refused");
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidScopeTree {
                function: 0,
                scope: 1,
                ..
            }
        )),
        "expected InvalidScopeTree, got {errors:?}"
    );
}

// ---------------------------------------------------------------------------
// REVIEW — adversarial inputs the increment did not write
// ---------------------------------------------------------------------------

/// A legitimate chain-bearing module must never CRASH a validator. The
/// increment made every binary writer refuse the chain (fallibly by name,
/// infallibly by panic), but left the digest-keyed entry points — the linked
/// import walk (root or resolved candidate) and the bundle binding — to reach
/// `stable_digest` and abort. Each now refuses by name through
/// `wire_identity_blocker`, exactly as the WS3.5 `MakeAggregate` precedent:
/// `ModuleHasNoWireIdentity` on the root / bundle path, `UnauthenticatedImport`
/// naming the reason on the candidate path. The plain structural validator
/// keeps accepting the module, and removing the link restores its identity.
#[test]
// The bundle path is exercised through the deprecated legacy coverage rule,
// which keeps its wire-identity refusal until it is deleted.
#[allow(deprecated)]
fn a_chain_bearing_module_has_no_wire_identity_and_is_refused_by_name_never_by_panic() {
    use trust_ir::proof::{ProofLineageManifest, RejectingModuleProofAuthority};
    use trust_ir::request::{NativeAdapterInput, NativeBundleProducer, NativeVerificationBundle};
    use trust_ir_build::{ModuleSet, coverage_assurance_report, validate_linked_module};

    let m = module_with_chain();
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    assert_eq!(m.first_inlined_scope_chain(), Some((0, 1)));
    let blocker = trust_ir_build::wire_identity_blocker(&m).expect("no binary carrier yet");
    assert!(
        matches!(
            &blocker,
            ValidationError::ModuleHasNoWireIdentity { location, construct }
                if location == "function 'caller' lexical scope #1"
                    && construct.contains("inlined_at")
        ),
        "{blocker:?}"
    );

    // Root of a linked walk (no imports at all): named refusal, no panic.
    let none = ModuleSet::new(std::iter::empty::<&Module>());
    let linked = validate_linked_module(&m, &none, &RejectingModuleProofAuthority);
    assert!(!linked.is_ok());
    assert_eq!(linked.errors().len(), 1, "{:?}", linked.errors());
    assert!(matches!(
        linked.errors()[0],
        ValidationError::ModuleHasNoWireIdentity { .. }
    ));

    // Bundle binding: a bundle for another (encodable) module cannot be bound
    // to a module with no identity — `checked: false`, one named error.
    let other = Module::new("ws4_19_some_other_module");
    let bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TrustIr,
        NativeAdapterInput::TrustIrModule,
        other.stable_digest(),
        other,
        ProofLineageManifest::default(),
    );
    let report = coverage_assurance_report(&m, Some(&bundle));
    assert!(!report.is_checked());
    let errors = report.into_errors();
    assert_eq!(errors.len(), 1, "{errors:?}");
    assert!(matches!(
        errors[0],
        ValidationError::ModuleHasNoWireIdentity { .. }
    ));

    // Resolved CANDIDATE of an import row: the importer is encodable, the
    // resolver hands back the chain-bearing module. The row cannot
    // authenticate, and says why.
    let mut importer = Module::new("importer");
    importer.imports.push(trust_ir::ModuleImport {
        name: "ws4_19_validation".into(),
        digest: trust_ir::proof::ProofDigest::sha256([7u8; 32]),
        producer: Some(trust_ir::Producer::TRust),
        scheme: trust_ir::IdentityScheme::CURRENT,
    });
    let resolver = |_import: &trust_ir::ModuleImport| Some(&m);
    let linked = validate_linked_module(&importer, &resolver, &RejectingModuleProofAuthority);
    assert!(
        linked.errors().iter().any(|e| matches!(
            e,
            ValidationError::UnauthenticatedImport { import: 0, detail, .. }
                if detail.contains("no wire identity") && detail.contains("inlined_at")
        )),
        "{:?}",
        linked.errors()
    );

    // Mutation control: the same module with the link removed HAS a wire
    // identity again, and the linked walk of it as a root is clean.
    let mut plain = m.clone();
    scope_mut(&mut plain, 1).inlined_at = None;
    assert_eq!(plain.first_inlined_scope_chain(), None);
    assert!(trust_ir_build::wire_identity_blocker(&plain).is_none());
    let linked = validate_linked_module(&plain, &none, &RejectingModuleProofAuthority);
    assert!(linked.is_ok(), "{:?}", linked.errors());
}

/// A chain link on a scope no instruction uses is still range-checked and
/// still refused on the root: the validator's rules are about the scope
/// TABLE, not about the nodes that happen to cite it. (An adversarial
/// producer could otherwise park a malformed link on an unreferenced scope
/// and have the tree accepted.)
#[test]
fn an_unreferenced_scope_with_a_malformed_link_is_still_refused() {
    let mut m = module_with_chain();
    let file_count = m.files.len();
    // Add scope #2: never cited by any node, chained from a file that does
    // not exist.
    m.functions[0]
        .scopes
        .as_mut()
        .expect("scopes")
        .push(ScopeData {
            parent: Some(0),
            span: None,
            inlined_at: Some(InlinedAt {
                span: SourceSpan {
                    file: file_count as u32,
                    line: 1,
                    col: 1,
                },
                callee: "clean::island::unused".into(),
            }),
        });
    let errors = validate_module(&m);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::SpanFileIndexOutOfRange { file, .. } if *file == file_count as u32
        )),
        "an unreferenced scope's call site is still range-checked: {errors:?}"
    );
    // Same scope, nameless callee: refused by name on scope #2.
    let link = scope_mut(&mut m, 2).inlined_at.as_mut().expect("link");
    link.span.file = 0;
    link.callee.clear();
    let errors = validate_module(&m);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::InvalidInlinedScope {
                function: 0,
                scope: 2,
                ..
            }
        )),
        "{errors:?}"
    );
    // Control: repaired, the unreferenced chained scope is legal.
    scope_mut(&mut m, 2)
        .inlined_at
        .as_mut()
        .expect("link")
        .callee = "clean::island::unused".into();
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
}
