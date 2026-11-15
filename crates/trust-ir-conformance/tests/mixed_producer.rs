// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// WS3-M1 seed (Program CK1, designs/2026-07-07 ~"mixed module + specs flow,
// negative-test-first"): ONE trust-ir module legally carries functions from
// BOTH producers (v23 `Function.producer` tags) with cross-producer calls in
// BOTH directions, and a skewed cross-producer call edge is REJECTED with a
// diagnostic that attributes both sides by producer.
//
// The NEGATIVE tests come first in this file, in the spirit of
// negative-test-first: the rejection contract is the acceptance seed, the
// green fixture is what remains once the rejection holds. The byte-golden
// four-format wire pinning of the green fixture lives in the corpus
// (`tests/conformance.rs`, fixture `mixed_producer_module`); the subset gate
// (`tests/lowering_subset.rs`) additionally holds it inside lowering-target
// current lowering-target subset with no exemption.

use trust_ir::inst::Inst;
use trust_ir::{Interpreter, Producer};
use trust_ir_build::validate::ValidationError;

// Fixture generators live in a sibling file and are included directly so
// these tests walk the exact module the byte-golden corpus pins. (dead_code
// allowed: only the mixed-producer builders are used here.)
// The fixture generators (tests/generate.rs), compiled once as the library's
// `fixtures` module rather than again inside every test binary.
use trust_ir_conformance::fixtures as generate;

// ============================================================
// NEGATIVE: mismatched-FuncTy cross-call is rejected, with
// producer-attributed diagnostics (lands first)
// ============================================================

/// A tRust-produced caller invoking a Clean-produced callee against a stale
/// signature (i64 arg where the callee declares i32) must be rejected, and
/// the diagnostic must name BOTH producers of the broken edge.
#[test]
fn cross_producer_functy_type_mismatch_is_rejected_with_producer_attribution() {
    let module =
        generate::build_mixed_producer_cross_functy_mismatch().expect("the fixture builds");
    let errors = trust_ir_build::validate_module(&module);

    let type_mismatch = errors
        .iter()
        .find(|e| matches!(e, ValidationError::CallArgTypeMismatch { .. }))
        .unwrap_or_else(|| {
            panic!("skewed tRust->Clean call must produce CallArgTypeMismatch, got: {errors:?}")
        });
    let rendered = type_mismatch.to_string();
    assert!(
        rendered.contains("call to clean_double")
            && rendered.contains("expected i32")
            && rendered.contains("got i64"),
        "diagnostic must state the FuncTy skew, got: {rendered}"
    );
    assert!(
        rendered.contains("caller producer: trust") && rendered.contains("callee producer: clean"),
        "diagnostic must attribute BOTH sides of the cross-producer edge \
         (caller producer: trust / callee producer: clean), got: {rendered}"
    );
}

/// The reverse direction: a Clean-produced caller invoking a tRust-produced
/// callee with the wrong arity must be rejected with the same attribution.
#[test]
fn cross_producer_functy_arity_mismatch_is_rejected_with_producer_attribution() {
    let module =
        generate::build_mixed_producer_cross_functy_mismatch().expect("the fixture builds");
    let errors = trust_ir_build::validate_module(&module);

    let count_mismatch = errors
        .iter()
        .find(|e| matches!(e, ValidationError::CallArgCountMismatch { .. }))
        .unwrap_or_else(|| {
            panic!("skewed Clean->tRust call must produce CallArgCountMismatch, got: {errors:?}")
        });
    let rendered = count_mismatch.to_string();
    assert!(
        rendered.contains("call to trust_inc")
            && rendered.contains("has 2 args")
            && rendered.contains("expected 1"),
        "diagnostic must state the arity skew, got: {rendered}"
    );
    assert!(
        rendered.contains("caller producer: clean") && rendered.contains("callee producer: trust"),
        "diagnostic must attribute BOTH sides of the cross-producer edge \
         (caller producer: clean / callee producer: trust), got: {rendered}"
    );
}

// ============================================================
// POSITIVE: the mixed-producer module is legal
// ============================================================

/// WS3-M1 acceptance floor: the mixed-producer module validates with ZERO
/// errors, carries both producer tags, and has cross-producer calls in BOTH
/// directions (TRust caller -> Clean callee AND Clean caller -> TRust callee).
#[test]
fn mixed_producer_module_validates_with_both_call_directions() {
    let module = generate::build_mixed_producer_module().expect("the fixture builds");

    // 1. validate_module: 0 errors.
    let errors = trust_ir_build::validate_module(&module);
    assert!(
        errors.is_empty(),
        "mixed-producer module must validate cleanly: {errors:?}"
    );

    // 2. Both producers are present as function tags.
    let producer_of = |name: &str| -> &Producer {
        module
            .functions
            .iter()
            .find(|f| f.name == name)
            .unwrap_or_else(|| panic!("fixture lost function `{name}`"))
            .producer
            .as_ref()
            .unwrap_or_else(|| panic!("function `{name}` lost its producer tag"))
    };
    assert_eq!(producer_of("clean_double"), &Producer::Clean);
    assert_eq!(producer_of("trust_inc"), &Producer::TRust);
    assert_eq!(producer_of("trust_calls_clean"), &Producer::TRust);
    assert_eq!(producer_of("clean_calls_trust"), &Producer::Clean);

    // 3. Cross-producer call edges exist in BOTH directions. Collect every
    //    (caller producer, callee producer) pair over direct calls.
    let mut edges = Vec::new();
    for func in &module.functions {
        for block in &func.blocks {
            for node in &block.body {
                if let Inst::Call { callee, .. } = &node.inst {
                    let callee_func = module
                        .functions
                        .iter()
                        .find(|f| f.id == *callee)
                        .expect("callee resolves");
                    edges.push((
                        func.producer.clone().expect("caller tagged"),
                        callee_func.producer.clone().expect("callee tagged"),
                    ));
                }
            }
        }
    }
    assert!(
        edges.contains(&(Producer::TRust, Producer::Clean)),
        "missing tRust -> Clean call edge; edges: {edges:?}"
    );
    assert!(
        edges.contains(&(Producer::Clean, Producer::TRust)),
        "missing Clean -> tRust call edge; edges: {edges:?}"
    );
}

/// Executable end-to-end: both cross-producer call chains run through the
/// reference interpreter (callee included) and produce the arithmetic the
/// bodies spell out. `trust_calls_clean(20) = 20*2 + 1 = 41`;
/// `clean_calls_trust(20) = (20+1)*2 = 42`.
#[test]
fn mixed_producer_module_executes_both_cross_calls() {
    let module = generate::build_mixed_producer_module().expect("the fixture builds");

    let func_id = |name: &str| {
        module
            .functions
            .iter()
            .find(|f| f.name == name)
            .unwrap_or_else(|| panic!("fixture lost function `{name}`"))
            .id
    };
    let run = |name: &str, arg: i128| -> i128 {
        let outcome = Interpreter::with_module(&module)
            .execute_func(
                func_id(name),
                [trust_ir::InterpretValue::int(trust_ir::Ty::I32, arg).expect("i32 arg")],
            )
            .unwrap_or_else(|e| panic!("`{name}` executes: {e}"));
        outcome.returns[0].as_int().expect("i32 result").as_signed()
    };

    assert_eq!(run("trust_calls_clean", 20), 41, "tRust -> Clean chain");
    assert_eq!(run("clean_calls_trust", 20), 42, "Clean -> tRust chain");
}

// ============================================================
// WS4.16 (F-080): the verification bundle STATES a two-language package
// ============================================================
//
// Schema 8 of `NativeVerificationBundle`: `NativeBundleProducer::Clean`,
// `NativeSourceLanguage::{Lean, Clean}`, and the language SET
// `NativeBundleProvenance.source_languages`, which must contain the primary
// `source_language` and cover every `Function.producer` of the bound module
// under the total map `NativeSourceLanguage::candidates_for_producer`
// (`None` -> `Unknown`, which must itself be a member). These tests are named
// `bundle_language_set_*` on purpose: gate 8 runs this crate with
// `-- --skip native_request_bundle`, a SUBSTRING filter, so a test whose
// name contains `native_request_bundle` would be silently skipped.

use std::collections::BTreeSet;
use trust_ir::binary::{
    deserialize_native_verification_bundle, serialize_native_verification_bundle,
};
use trust_ir::proof::ProofDigest;
use trust_ir::proof::ProofLineageManifest;
use trust_ir::value::ImportId;
use trust_ir::{
    FuncId, Linkage, Module, ModuleImport, NativeAdapterInput, NativeBundleProducer,
    NativeSourceLanguage, NativeVerificationBundle, NativeVerificationBundleError,
};

/// A COMPLETE, validating schema-8 bundle around `module` (obligation,
/// lineage, sidecar, and all three request lanes — see
/// `generate::build_language_set_bundle`), so `Ok(())` below means the whole
/// bundle validates and a single error means the language rule alone fired.
/// The language set is `languages`, the primary is its first entry.
fn bundle_over(
    module: Module,
    producer: NativeBundleProducer,
    languages: &[NativeSourceLanguage],
) -> NativeVerificationBundle {
    generate::build_language_set_bundle(module, producer, languages).expect("the fixture builds")
}

fn language_errors(bundle: &NativeVerificationBundle) -> Vec<NativeVerificationBundleError> {
    match bundle.validate() {
        Ok(()) => Vec::new(),
        Err(errors) => errors,
    }
}

fn function_ids(module: &Module, producer: Option<&Producer>) -> Vec<FuncId> {
    module
        .functions
        .iter()
        .filter(|f| f.producer.as_ref() == producer)
        .map(|f| f.id)
        .collect()
}

use NativeSourceLanguage::{Clean as LangClean, Lean, Rust, Unknown};

/// POSITIVE: the two-producer module (`build_mixed_producer_module`: two
/// `TRust` and two `Clean` functions, cross-calls both ways) gets a bundle
/// declaring `{Rust, Lean}` and it VALIDATES — the whole bundle, not the
/// language rule alone. `{Rust, Clean}` validates too (either Clean-side
/// language covers `Producer::Clean`), and so does the over-complete
/// `{Rust, Lean, Clean, Unknown}`.
#[test]
fn bundle_language_set_two_producer_module_validates() {
    for languages in [
        &[Rust, Lean][..],
        &[Rust, LangClean],
        &[Lean, Rust],
        &[Rust, Lean, LangClean, Unknown],
    ] {
        let bundle = bundle_over(
            generate::build_mixed_producer_module().expect("the fixture builds"),
            NativeBundleProducer::TRust,
            languages,
        );
        assert_eq!(bundle.schema_version, 8);
        assert_eq!(bundle.validate(), Ok(()), "{languages:?}");
        assert!(
            bundle
                .provenance
                .uncovered_functions(&bundle.module)
                .is_empty()
        );
    }
}

/// An EMPTY language set has no primary language: the builder refuses with a
/// `FixtureError` naming itself instead of panicking on `languages[0]`
/// (the verified survey's slice-bounds row on `build_language_set_bundle`).
#[test]
fn bundle_language_set_empty_is_refused_by_the_builder_not_a_panic() {
    let err = generate::build_language_set_bundle(
        generate::build_mixed_producer_module().expect("the fixture builds"),
        NativeBundleProducer::TRust,
        &[],
    )
    .expect_err("an empty language set has no primary language");
    assert_eq!(err.context, "build_language_set_bundle");
    assert!(err.message.contains("empty"), "{err}");
}

/// NEGATIVE TWIN: the same bundle declaring only `{Rust}` is refused with
/// EXACTLY `BundleLanguageUncovered { producer: Some(Clean), .. }` naming the
/// two Clean functions — and nothing else, so the refusal is the language
/// rule and not a side effect of the fixture.
#[test]
fn bundle_language_set_rust_only_is_refused_for_the_clean_functions() {
    let bundle = bundle_over(
        generate::build_mixed_producer_module().expect("the fixture builds"),
        NativeBundleProducer::TRust,
        &[Rust],
    );
    let clean = function_ids(&bundle.module, Some(&Producer::Clean));
    assert_eq!(clean.len(), 2, "fixture carries two Clean functions");
    let errors = language_errors(&bundle);
    assert_eq!(
        errors,
        vec![NativeVerificationBundleError::BundleLanguageUncovered {
            producer: Some(Producer::Clean),
            functions: clean,
            source_languages: BTreeSet::from([Rust]),
        }]
    );
    let rendered = errors[0].to_string();
    assert!(
        rendered.contains("covers none of [Lean, Clean] for producer Clean"),
        "{rendered}"
    );
    // The symmetric twin: `{Lean}` alone leaves the two TRust functions
    // uncovered — `Rust` is the only language covering `Producer::TRust`.
    let bundle = bundle_over(
        generate::build_mixed_producer_module().expect("the fixture builds"),
        NativeBundleProducer::Clean,
        &[Lean],
    );
    let rust = function_ids(&bundle.module, Some(&Producer::TRust));
    assert_eq!(
        language_errors(&bundle),
        vec![NativeVerificationBundleError::BundleLanguageUncovered {
            producer: Some(Producer::TRust),
            functions: rust,
            source_languages: BTreeSet::from([Lean]),
        }]
    );
}

/// NEGATIVE TWIN (none is not a wildcard): a module with one `producer: None`
/// function under `{Rust}` is refused with
/// `BundleLanguageUncovered { producer: None, .. }`; only an EXPLICIT
/// `Unknown` member covers it.
#[test]
fn bundle_language_set_unstamped_function_needs_an_explicit_unknown() {
    let mut module = generate::build_mixed_producer_module().expect("the fixture builds");
    module.functions[1].producer = None; // trust_inc, no longer stamped
    let unstamped = function_ids(&module, None);
    assert_eq!(unstamped, vec![FuncId::new(1)]);

    let bundle = bundle_over(module.clone(), NativeBundleProducer::TrustIr, &[Rust, Lean]);
    let errors = language_errors(&bundle);
    assert_eq!(
        errors,
        vec![NativeVerificationBundleError::BundleLanguageUncovered {
            producer: None,
            functions: unstamped,
            source_languages: BTreeSet::from([Rust, Lean]),
        }]
    );
    assert!(
        errors[0]
            .to_string()
            .contains("no Unknown member for the unstamped (producer: None) function(s) [f1]"),
        "{}",
        errors[0]
    );
    // The fix is to SAY Unknown, not to drop the stamp check.
    let bundle = bundle_over(
        module,
        NativeBundleProducer::TrustIr,
        &[Rust, Lean, Unknown],
    );
    assert_eq!(bundle.validate(), Ok(()));
}

/// NEGATIVE TWIN (the primary is a member): `source_language = Rust` with a
/// set `{Lean}` contradicts itself and is refused with
/// `BundlePrimaryLanguageUncovered`; the EMPTY set (what a v7 blob without
/// the key decodes to) covers neither the primary nor any function.
#[test]
fn bundle_language_set_primary_must_be_a_member_and_empty_covers_nothing() {
    let mut bundle = bundle_over(
        generate::build_mixed_producer_module().expect("the fixture builds"),
        NativeBundleProducer::TRust,
        &[Rust, Lean],
    );
    bundle.provenance.source_languages = BTreeSet::from([Lean]);
    let errors = language_errors(&bundle);
    assert!(
        errors.contains(
            &NativeVerificationBundleError::BundlePrimaryLanguageUncovered {
                primary: Rust,
                source_languages: BTreeSet::from([Lean]),
            }
        ),
        "{errors:?}"
    );
    assert_eq!(errors.len(), 2, "primary + the TRust functions: {errors:?}");

    bundle.provenance.source_languages = BTreeSet::new();
    let errors = language_errors(&bundle);
    let uncovered_producers: Vec<Option<Producer>> = errors
        .iter()
        .filter_map(|e| match e {
            NativeVerificationBundleError::BundleLanguageUncovered { producer, .. } => {
                Some(producer.clone())
            }
            _ => None,
        })
        .collect();
    assert_eq!(
        uncovered_producers,
        vec![Some(Producer::Clean), Some(Producer::TRust)],
        "module order: clean_double first, then trust_inc; {errors:?}"
    );
    assert!(errors.iter().any(|e| matches!(
        e,
        NativeVerificationBundleError::BundlePrimaryLanguageUncovered { primary: Rust, .. }
    )));
}

/// MUTATION CONTROL: a validator that ignored `Function.producer` — checking
/// only that the primary is a member — would ACCEPT the `{Rust}` twin; one
/// that treated `producer: None` as covered would ACCEPT the unstamped twin.
/// Both mutants are spelled out here and shown to pass exactly the bundles
/// the real rule refuses, so the twins above are the tests that catch them.
#[test]
fn bundle_language_set_mutation_control_ignoring_function_producer() {
    fn mutant_primary_only(bundle: &NativeVerificationBundle) -> bool {
        bundle
            .provenance
            .source_languages
            .contains(&bundle.provenance.source_language)
    }
    fn mutant_none_is_wildcard(bundle: &NativeVerificationBundle) -> bool {
        mutant_primary_only(bundle)
            && bundle.module.functions.iter().all(|f| {
                f.producer.is_none()
                    || NativeSourceLanguage::set_covers_producer(
                        &bundle.provenance.source_languages,
                        f.producer.as_ref(),
                    )
            })
    }

    let twin = bundle_over(
        generate::build_mixed_producer_module().expect("the fixture builds"),
        NativeBundleProducer::TRust,
        &[Rust],
    );
    assert!(mutant_primary_only(&twin), "the mutant accepts the twin");
    assert!(twin.validate().is_err(), "the real rule refuses it");

    let mut module = generate::build_mixed_producer_module().expect("the fixture builds");
    module.functions[1].producer = None;
    let twin = bundle_over(module, NativeBundleProducer::TrustIr, &[Rust, Lean]);
    assert!(
        mutant_none_is_wildcard(&twin),
        "the mutant accepts the twin"
    );
    assert!(twin.validate().is_err(), "the real rule refuses it");

    // The map itself is total and exact.
    assert_eq!(
        NativeSourceLanguage::candidates_for_producer(Some(&Producer::Clean)),
        &[Lean, LangClean]
    );
    assert_eq!(
        NativeSourceLanguage::candidates_for_producer(None),
        &[Unknown]
    );
    assert_eq!(
        NativeSourceLanguage::candidates_for_producer(Some(&Producer::Other("x".into()))),
        &[NativeSourceLanguage::Other]
    );
    assert!(!NativeSourceLanguage::set_covers_producer(
        &BTreeSet::new(),
        None
    ));
}

/// A v7 bundle is refused with the EXACT-VERSION error (never best-effort
/// upgraded): as a decoded value, and as a v7 JSON blob whose provenance has
/// no `source_languages` key — which decodes to the empty set and is refused
/// twice over (schema and coverage), so a pre-two-language producer cannot
/// slip a bundle past the language rule by omitting the claim.
#[test]
fn bundle_language_set_v7_bundle_is_refused_exactly() {
    let mut bundle = bundle_over(
        generate::build_mixed_producer_module().expect("the fixture builds"),
        NativeBundleProducer::TRust,
        &[Rust, Lean],
    );
    assert_eq!(NativeVerificationBundle::SCHEMA_VERSION, 8);
    bundle.schema_version = 7;
    bundle.serialization.schema_version = 7;
    let errors = language_errors(&bundle);
    assert!(errors.contains(&NativeVerificationBundleError::UnsupportedSchemaVersion(7)));
    assert!(
        errors.contains(&NativeVerificationBundleError::UnsupportedSerializationSchemaVersion(7))
    );

    let mut json: serde_json::Value = serde_json::to_value(&bundle).expect("json");
    let provenance = json["provenance"]
        .as_object_mut()
        .expect("provenance object");
    assert!(provenance.remove("source_languages").is_some());
    assert_eq!(json["schema_version"], 7);
    let decoded: NativeVerificationBundle = serde_json::from_value(json).expect("v7 shape decodes");
    assert!(
        decoded.provenance.source_languages.is_empty(),
        "absent key = EMPTY set"
    );
    let errors = language_errors(&decoded);
    assert!(errors.contains(&NativeVerificationBundleError::UnsupportedSchemaVersion(7)));
    assert!(errors.iter().any(|e| matches!(
        e,
        NativeVerificationBundleError::BundlePrimaryLanguageUncovered { .. }
    )));
    assert!(errors.iter().any(|e| matches!(
        e,
        NativeVerificationBundleError::BundleLanguageUncovered { .. }
    )));
}

/// The set is part of the bundle's identity: two bundles differing only in
/// the language set have different stable digests (the v8 domain), the digest
/// is set-order independent by construction, and the set survives JSON and
/// MessagePack byte-for-byte.
#[test]
fn bundle_language_set_enters_the_digest_and_round_trips_serde() {
    let a = bundle_over(
        generate::build_mixed_producer_module().expect("the fixture builds"),
        NativeBundleProducer::TRust,
        &[Rust, Lean],
    );
    let b = bundle_over(
        generate::build_mixed_producer_module().expect("the fixture builds"),
        NativeBundleProducer::TRust,
        &[Rust, LangClean],
    );
    // `bundle_over` takes the first entry as the primary: this one is
    // primary Lean over the same set as `a`.
    let primary_lean = bundle_over(
        generate::build_mixed_producer_module().expect("the fixture builds"),
        NativeBundleProducer::TRust,
        &[Lean, Rust],
    );
    assert_ne!(a.stable_digest(), b.stable_digest());
    let mut a_reordered = a.clone();
    a_reordered.provenance.source_languages = [Lean, Rust].into_iter().collect();
    assert_eq!(a.stable_digest(), a_reordered.stable_digest());
    assert_ne!(
        a.stable_digest(),
        primary_lean.stable_digest(),
        "the primary scalar is still bound"
    );

    let json = serde_json::to_value(&a).expect("json");
    assert_eq!(
        json["provenance"]["source_languages"],
        serde_json::json!(["Rust", "Lean"])
    );
    let back: NativeVerificationBundle = serde_json::from_value(json).expect("decode");
    assert_eq!(back, a);
    let bytes = rmp_serde::to_vec_named(&a).expect("msgpack");
    let back: NativeVerificationBundle = rmp_serde::from_slice(&bytes).expect("decode");
    assert_eq!(back, a);
    assert_eq!(back.validate(), Ok(()));
}

/// `NativeBundleProducer::Clean` has a spelling in every bundle transport:
/// serde `"Clean"` (JSON and MessagePack) and TMVB envelope tag 4 (the
/// `.tmbc`-family binary codec, whose provenance must be the default — so
/// the envelope sample is a default-provenance bundle over an unstamped
/// module, which `{Unknown}` covers). A Clean-only module labelled `Clean`
/// with `{Lean, Clean}` validates.
#[test]
fn bundle_language_set_clean_producer_round_trips_every_transport() {
    let mut module = generate::build_mixed_producer_module().expect("the fixture builds");
    for f in &mut module.functions {
        f.producer = Some(Producer::Clean);
    }
    let bundle = bundle_over(module, NativeBundleProducer::Clean, &[LangClean, Lean]);
    assert_eq!(bundle.validate(), Ok(()));
    let json = serde_json::to_string(&bundle).expect("json");
    assert!(json.contains("\"producer\":\"Clean\""), "{json}");
    let back: NativeVerificationBundle = serde_json::from_str(&json).expect("decode");
    assert_eq!(back.producer, NativeBundleProducer::Clean);
    let bytes = rmp_serde::to_vec_named(&bundle).expect("msgpack");
    let back: NativeVerificationBundle = rmp_serde::from_slice(&bytes).expect("decode");
    assert_eq!(back, bundle);

    // TMVB envelope: tag 4 round-trips; provenance stays at its default.
    let envelope = NativeVerificationBundle::new(
        NativeBundleProducer::Clean,
        NativeAdapterInput::TrustIrModule,
        Module::new("clean_envelope").stable_digest(),
        Module::new("clean_envelope"),
        ProofLineageManifest::new(),
    );
    assert_eq!(
        envelope.provenance.source_languages,
        BTreeSet::from([Unknown]),
        "the default provenance covers exactly its default primary"
    );
    let bytes = serialize_native_verification_bundle(&envelope).expect("TMVB");
    let header_producer_byte = bytes[4 + 4 + 4];
    assert_eq!(header_producer_byte, 4, "TMVB producer tag byte");
    let back = deserialize_native_verification_bundle(&bytes).expect("decode");
    assert_eq!(back.producer, NativeBundleProducer::Clean);
    assert_eq!(back, envelope);
}

// ============================================================
// WS4.16 REVIEW — three adversarial inputs the increment's own
// tests did not reach
// ============================================================

/// ADVERSARIAL 1 (a false claim that WAS accepted): the package's Clean half
/// hidden behind an IMPORT.
///
/// A root module whose own functions are all `Producer::TRust`, but which
/// authenticates a Clean-produced dependency (`Module.imports`, the row an
/// `ExternRef` / `FunctionSummary.backed_by` / `InheritedFromCallee { external
/// }` edge cites), IS a two-language artifact: its discharges rest on the
/// Clean kernel. Before this review the coverage rule stopped at
/// `module.functions`, so such a bundle could declare `{Rust}` and validate —
/// exactly the claim F-080 exists to make impossible, restated one level up.
/// Now the import row must be covered too, and `producer: None` on an import
/// (UNRECORDED, never agreement with the importer) needs an explicit
/// `Unknown` just as an unstamped function does.
#[test]
fn bundle_language_set_covers_imported_dependency_producers() {
    let dependency_digest = ProofDigest::sha256_domain(
        "trust-ir.conformance.ws4-16.dependency",
        b"clean-produced dependency",
    );
    let with_import = |producer: Option<Producer>| -> Module {
        let mut module = generate::build_mixed_producer_module().expect("the fixture builds");
        // The root's OWN functions are entirely tRust-produced.
        for f in &mut module.functions {
            f.producer = Some(Producer::TRust);
        }
        let import = ModuleImport::new("clean_dependency", dependency_digest);
        module
            .intern_import(match producer {
                Some(producer) => import.with_producer(producer),
                None => import,
            })
            .expect("Module::intern_import: test fixture");
        module
    };

    // The false claim: all-Rust functions, a Clean dependency, `{Rust}`.
    let bundle = bundle_over(
        with_import(Some(Producer::Clean)),
        NativeBundleProducer::TRust,
        &[Rust],
    );
    assert!(
        bundle
            .provenance
            .uncovered_functions(&bundle.module)
            .is_empty(),
        "every FUNCTION is covered — the module half of the rule is silent here"
    );
    let errors = language_errors(&bundle);
    assert_eq!(
        errors,
        vec![
            NativeVerificationBundleError::BundleImportLanguageUncovered {
                import: ImportId::new(0),
                name: "clean_dependency".to_string(),
                producer: Some(Producer::Clean),
                source_languages: BTreeSet::from([Rust]),
            }
        ],
        "a Clean dependency behind an import is not covered by {{Rust}}"
    );
    let rendered = errors[0].to_string();
    assert!(
        rendered.contains("covers none of [Lean, Clean] for imported module \"clean_dependency\""),
        "{rendered}"
    );

    // Saying the second language is the fix, in either Clean-side spelling.
    for languages in [&[Rust, Lean][..], &[Rust, LangClean]] {
        let bundle = bundle_over(
            with_import(Some(Producer::Clean)),
            NativeBundleProducer::TRust,
            languages,
        );
        assert_eq!(bundle.validate(), Ok(()), "{languages:?}");
    }

    // None on an import row is UNRECORDED, not a wildcard: only an explicit
    // `Unknown` covers it, and `{Rust}` alone does not.
    let bundle = bundle_over(with_import(None), NativeBundleProducer::TRust, &[Rust]);
    let errors = language_errors(&bundle);
    assert_eq!(
        errors,
        vec![
            NativeVerificationBundleError::BundleImportLanguageUncovered {
                import: ImportId::new(0),
                name: "clean_dependency".to_string(),
                producer: None,
                source_languages: BTreeSet::from([Rust]),
            }
        ]
    );
    assert!(
        errors[0].to_string().contains(
            "has no Unknown member for imported module \"clean_dependency\" (import 0), whose \
             producer is UNRECORDED"
        ),
        "{}",
        errors[0]
    );
    let bundle = bundle_over(
        with_import(None),
        NativeBundleProducer::TRust,
        &[Rust, Unknown],
    );
    assert_eq!(bundle.validate(), Ok(()));

    // MUTATION CONTROL: a rule that stopped at `module.functions` — the
    // pre-review shape — ACCEPTS the false claim this test refuses.
    fn mutant_functions_only(bundle: &NativeVerificationBundle) -> bool {
        bundle
            .provenance
            .source_languages
            .contains(&bundle.provenance.source_language)
            && bundle
                .provenance
                .uncovered_functions(&bundle.module)
                .is_empty()
    }
    let false_claim = bundle_over(
        with_import(Some(Producer::Clean)),
        NativeBundleProducer::TRust,
        &[Rust],
    );
    assert!(
        mutant_functions_only(&false_claim),
        "the mutant accepts the {{Rust}} claim over a Clean dependency"
    );
    assert!(false_claim.validate().is_err(), "the real rule refuses it");
}

/// ADVERSARIAL 2 (is the rule blind to bodyless DECLARATIONS?): no.
///
/// A real tRust module names its C/runtime half through bodyless `External`
/// declarations, which carry no producer stamp. Those rows are `Function`s of
/// `module.functions`, so the coverage rule reaches them: a `{Rust}` bundle
/// over such a module is REFUSED, naming the declaration, and the producer
/// must say `Unknown` to state that a piece of the package came from
/// somewhere it cannot name. This pins the boundary in the strict direction —
/// a reading that exempted declarations would let any package launder an
/// unstamped function by dropping its body.
#[test]
fn bundle_language_set_unstamped_declaration_needs_unknown_too() {
    let mut module = generate::build_mixed_producer_module().expect("the fixture builds");
    for f in &mut module.functions {
        f.producer = Some(Producer::TRust);
    }
    // A bodyless External declaration of a runtime entry point: no body, no
    // producer stamp.
    let mut declaration = module.functions[0].clone();
    declaration.id = FuncId::new(u32::try_from(module.functions.len()).unwrap());
    declaration.name = "trust_bignum_nat_add".to_string();
    declaration.blocks.clear();
    declaration.linkage = Linkage::External;
    declaration.producer = None;
    let declaration_id = declaration.id;
    module.functions.push(declaration);

    let bundle = bundle_over(module.clone(), NativeBundleProducer::TRust, &[Rust]);
    assert_eq!(
        language_errors(&bundle),
        vec![NativeVerificationBundleError::BundleLanguageUncovered {
            producer: None,
            functions: vec![declaration_id],
            source_languages: BTreeSet::from([Rust]),
        }],
        "a bodyless declaration is a function row and is covered like one"
    );
    let bundle = bundle_over(module, NativeBundleProducer::TRust, &[Rust, Unknown]);
    assert_eq!(bundle.validate(), Ok(()));
}

/// ADVERSARIAL 3 (can a bundle be RE-LABELLED at the same identity?): no.
///
/// The set and the primary are bound to the bundle digest SEPARATELY, so
/// moving which member is primary — `{Rust, Lean}` primary `Rust` vs the same
/// set primary `Lean` — is a different bundle, and so is adding a language.
/// Without the separate binding a consumer pinning a bundle digest could be
/// handed a differently-labelled package under the pinned identity. The set
/// itself is order-insensitive (it is a `BTreeSet` written length-first), so
/// the two spellings of the SAME set collide on purpose.
#[test]
fn bundle_language_set_primary_and_membership_are_bound_separately() {
    let rust_primary = bundle_over(
        generate::build_mixed_producer_module().expect("the fixture builds"),
        NativeBundleProducer::TRust,
        &[Rust, Lean],
    );
    let lean_primary = bundle_over(
        generate::build_mixed_producer_module().expect("the fixture builds"),
        NativeBundleProducer::TRust,
        &[Lean, Rust],
    );
    assert_eq!(rust_primary.validate(), Ok(()));
    assert_eq!(lean_primary.validate(), Ok(()));
    assert_eq!(
        rust_primary.provenance.source_languages, lean_primary.provenance.source_languages,
        "the same SET, spelled in two orders"
    );
    assert_ne!(
        rust_primary.provenance.source_language, lean_primary.provenance.source_language,
        "different primaries"
    );
    assert_ne!(
        rust_primary.stable_digest(),
        lean_primary.stable_digest(),
        "the primary is bound to the digest independently of the set"
    );

    // A wider claim is a different bundle too.
    let wider = bundle_over(
        generate::build_mixed_producer_module().expect("the fixture builds"),
        NativeBundleProducer::TRust,
        &[Rust, Lean, Unknown],
    );
    assert_ne!(rust_primary.stable_digest(), wider.stable_digest());
}
