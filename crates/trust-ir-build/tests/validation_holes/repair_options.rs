// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! WS4.18 (F-081): fail-closed refusals carry structured repair options.
//!
//! v7 D3 makes the reader of a refusal an AI programmer: a refusal names the
//! rule, says why, and ENUMERATES concrete ways forward. Before this increment
//! `grep 'Options:'` returned 0 across `validate.rs`, `linked.rs` and
//! `imports.rs`; a handful of `Display` texts named one next step and none
//! enumerated any.
//!
//! The rule: `ValidationError::repair_options` (and
//! `ImportVerificationError::repair_options` for the edge checks under
//! `Module::verify_import`) returns one imperative line per option, filled
//! first for the fail-closed paths an AI programmer hits. The options are
//! ADVICE TEXT, NEVER AUTHORITY: nothing may branch on them, which
//! `repair_options_have_no_reader_outside_the_cli_printer` enforces by
//! scanning every `crates/*/src` file.
//!
//! Row ported: `spec-surface-0709/23-refusals-carry-repair-options` (archived
//! at `reports/2026-09-17-two-language-proof-program/evidence/understand.json`)
//! — GAP (no refusal enumerated a way forward) flips to PASS.

use std::path::{Path, PathBuf};

use trust_ir::ImportVerificationError;
use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, ProofFormula, RejectingModuleProofAuthority,
};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{FuncId, ProofId};
use trust_ir::{ExternRef, Function, FunctionSummary, Module, ModuleImport, Producer};
use trust_ir_build::validate::ValidationError;
use trust_ir_build::{
    ModuleBuilder, ModuleSet, validate_linked_module, validate_module_with_authority,
};

/// Signature of a repair-option table, so a mutant table can be substituted
/// for the real one (the mutation control below).
type Options = fn(&ValidationError) -> &'static [&'static str];

/// Every `ValidationError` shape the increment names, constructed directly —
/// one row per variant, and one per `UnauthenticatedImport` site, because
/// that variant's options depend on which edge was refused.
fn listed_variants() -> Vec<(&'static str, ValidationError)> {
    let unauthenticated = |site: &'static str| ValidationError::UnauthenticatedImport {
        import: 0,
        site,
        detail: "fixture".into(),
    };
    vec![
        (
            "DischargedWithoutCertificate",
            ValidationError::DischargedWithoutCertificate { obligation: 0 },
        ),
        ("UnauthenticatedImport(import)", unauthenticated("import")),
        ("UnauthenticatedImport(call)", unauthenticated("call")),
        (
            "UnauthenticatedImport(backed_by)",
            unauthenticated("backed_by"),
        ),
        (
            "UnauthenticatedImport(inherited)",
            unauthenticated("inherited"),
        ),
        (
            "ImportUnavailable",
            ValidationError::ImportUnavailable {
                import: 0,
                name: "dep".into(),
            },
        ),
        (
            "InvalidFunctionSummary",
            ValidationError::InvalidFunctionSummary {
                function: 0,
                detail: "fixture".into(),
            },
        ),
        (
            "UngatedBodyForCodegen",
            ValidationError::UngatedBodyForCodegen {
                function: 0,
                name: "f".into(),
            },
        ),
        (
            "UnlicensedBodyForCodegen",
            ValidationError::UnlicensedBodyForCodegen {
                function: 0,
                name: "f".into(),
            },
        ),
        (
            "GlobalAsmNotConsumable",
            ValidationError::GlobalAsmNotConsumable { blocks: 1 },
        ),
        (
            "HandleEntryPointDefinedLocally",
            ValidationError::HandleEntryPointDefinedLocally {
                function: 0,
                symbol: "trust_bignum_nat_add".into(),
            },
        ),
        (
            "TargetInfoRequired",
            ValidationError::TargetInfoRequired {
                boundary: "external declaration `ext`".into(),
            },
        ),
        (
            "UnpinnedCustomObligationNamespace",
            ValidationError::UnpinnedCustomObligationNamespace {
                obligation: 0,
                namespace: "vendor".into(),
                name: "x".into(),
            },
        ),
        (
            "HandleRuntimeSpelledStructurally",
            ValidationError::HandleRuntimeSpelledStructurally {
                def: "struct #0".into(),
                runtime: "trust_bignum::Nat".into(),
            },
        ),
        // WS4.17 (DG-54): a producer that renamed a retired row out of the
        // namespace is told how to drop it instead.
        (
            "SyntheticSymbolName",
            ValidationError::SyntheticSymbolName {
                function: 1,
                name: "m::cleanAdd::<shadowed-by-clean-origin:FuncId(1)>".into(),
            },
        ),
    ]
}

/// The option-shape contract the CLI printer relies on: at least one option,
/// each a single non-blank line that the printer's `"; "` join cannot split.
fn shape_defects(options: &[&str]) -> Option<String> {
    if options.is_empty() {
        return Some("no options".into());
    }
    for option in options {
        if option.trim().is_empty() {
            return Some("a blank option".into());
        }
        if option.contains('\n') || option.contains("; ") {
            return Some(format!("option {option:?} is not one unsplittable line"));
        }
        if option.contains("  ") {
            return Some(format!("option {option:?} carries a doubled space"));
        }
    }
    None
}

/// The names of the listed variants `table` leaves without well-shaped options.
fn variants_missing_options(table: Options) -> Vec<String> {
    listed_variants()
        .into_iter()
        .filter_map(|(name, error)| {
            shape_defects(table(&error)).map(|why| format!("{name}: {why}"))
        })
        .collect()
}

fn real_table(error: &ValidationError) -> &'static [&'static str] {
    error.repair_options()
}

/// Positive: every variant the increment names enumerates at least one way
/// forward, and each option is one imperative line.
#[test]
fn every_listed_refusal_enumerates_repair_options() {
    assert_eq!(variants_missing_options(real_table), Vec::<String>::new());
}

/// Positive, the edge half: `DigestMismatch` is an `ImportVerificationError`
/// (it reaches `validate_linked_module` wrapped in `UnauthenticatedImport`),
/// produced here by the real `Module::verify_import` against a rebuilt
/// dependency.
#[test]
fn digest_mismatch_enumerates_repair_options() {
    let dep = callee("dep", 1);
    let rebuilt = callee("dep", 2);
    assert_ne!(dep.stable_digest(), rebuilt.stable_digest());
    let mut importer = Module::new("importer");
    let id = importer
        .intern_import(ModuleImport::new("dep", dep.stable_digest()).with_producer(Producer::TRust))
        .expect("Module::intern_import: test fixture");
    let refused = importer
        .verify_import(id, &rebuilt)
        .expect_err("a rebuilt dependency is a different module");
    assert!(
        matches!(refused, ImportVerificationError::DigestMismatch { .. }),
        "{refused:?}"
    );
    assert_eq!(shape_defects(refused.repair_options()), None);
}

/// Negative twin: a variant outside the filled set enumerates nothing, so the
/// CLI prints no `options:` line for it (the empty default is the
/// "no enumerated options yet" state, never a fabricated one).
#[test]
fn a_refusal_outside_the_filled_set_enumerates_no_options() {
    assert!(ValidationError::EmptyFunction.repair_options().is_empty());
    let unresolved = ImportVerificationError::UnresolvedImport { import: 3 };
    assert!(unresolved.repair_options().is_empty());
}

/// Mutation control: a table that drops `UnauthenticatedImport`'s options is
/// caught by the positive check, by name — and the ONLY rows it names are the
/// mutated ones, so the check does not over-refuse.
#[test]
fn a_mutant_dropping_unauthenticated_import_options_is_caught() {
    fn mutant(error: &ValidationError) -> &'static [&'static str] {
        match error {
            ValidationError::UnauthenticatedImport { .. } => &[],
            other => other.repair_options(),
        }
    }
    let missing = variants_missing_options(mutant);
    assert_eq!(
        missing,
        vec![
            "UnauthenticatedImport(import): no options".to_string(),
            "UnauthenticatedImport(call): no options".to_string(),
            "UnauthenticatedImport(backed_by): no options".to_string(),
            "UnauthenticatedImport(inherited): no options".to_string(),
        ]
    );
}

/// Options are advice text, never authority: no code path may branch on
/// them. Every `repair_options` identifier in `crates/*/src` code (comments
/// excluded) must be a definition (`pub fn repair_options(&self)`) or the ONE
/// call in the `trust-ir` CLI printer.
#[test]
fn repair_options_have_no_reader_outside_the_cli_printer() {
    let crates = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates dir")
        .to_path_buf();
    let mut files = Vec::new();
    for entry in std::fs::read_dir(&crates).expect("read crates/") {
        let src = entry.expect("dir entry").path().join("src");
        if src.is_dir() {
            collect_rs(&src, &mut files);
        }
    }
    assert!(
        files.len() > 20,
        "the scan found too few sources: {files:?}"
    );
    let cli_main = crates.join("trust-ir-cli").join("src").join("main.rs");
    let sources: Vec<(PathBuf, String)> = files
        .into_iter()
        .map(|file| {
            let text = std::fs::read_to_string(&file).expect("read source");
            (file, text)
        })
        .collect();
    let scan = scan_readers(&sources, &cli_main);
    assert_eq!(
        scan.foreign,
        Vec::<String>::new(),
        "repair options are advice text; only the CLI printer may read them"
    );
    assert_eq!(
        scan.definitions, 2,
        "ValidationError and ImportVerificationError"
    );
    assert_eq!(
        scan.cli_calls, 1,
        "the CLI printer reads the options exactly once"
    );
}

/// Adversarial review: a reader need not spell `repair_options(`. A function
/// PATH (`.map(ValidationError::repair_options)`), a call split across lines,
/// or a space before the parenthesis each read the options without that
/// token; the scan matches the identifier, so each is named. A mention inside
/// a comment is not a reader, and the real printer line is not foreign.
#[test]
fn the_reader_scan_catches_readers_that_do_not_spell_a_call() {
    let cli_main = PathBuf::from("crates/trust-ir-cli/src/main.rs");
    let evasions = [
        "let all: Vec<_> = errors.iter().map(ValidationError::repair_options).collect();",
        "if err\n    .repair_options\n    ()\n    .is_empty() { return; }",
        "let n = err.repair_options ().len();",
        "let f: fn(&ValidationError) -> _ = ValidationError::repair_options;",
    ];
    for evasion in evasions {
        let scan = scan_readers(
            &[(
                PathBuf::from("crates/trust-ir-build/src/linked.rs"),
                evasion.to_string(),
            )],
            &cli_main,
        );
        assert_eq!(scan.foreign.len(), 1, "{evasion:?} was not named: {scan:?}");
    }
    let benign = "/// See `ValidationError::repair_options`.\n\
                  // repair_options is advice text\n\
                  pub fn repair_options(&self) -> &'static [&'static str] {\n";
    let scan = scan_readers(
        &[(
            PathBuf::from("crates/trust-ir/src/imports.rs"),
            benign.to_string(),
        )],
        &cli_main,
    );
    assert_eq!((scan.definitions, scan.foreign.len()), (1, 0), "{scan:?}");
    let printer = "    let options = err.repair_options();\n";
    let scan = scan_readers(&[(cli_main.clone(), printer.to_string())], &cli_main);
    assert_eq!((scan.cli_calls, scan.foreign.len()), (1, 0), "{scan:?}");
}

#[derive(Debug, Default)]
struct ReaderScan {
    definitions: usize,
    cli_calls: usize,
    foreign: Vec<String>,
}

/// Classify every `repair_options` identifier occurrence in the code part of
/// each line (text before a `//` comment).
fn scan_readers(sources: &[(PathBuf, String)], cli_main: &Path) -> ReaderScan {
    let mut scan = ReaderScan::default();
    for (file, text) in sources {
        for (line_no, line) in text.lines().enumerate() {
            let code = line.split("//").next().unwrap_or("");
            let hits = identifier_hits(code, "repair_options");
            if hits == 0 {
                continue;
            }
            if code
                .trim_start()
                .starts_with("pub fn repair_options(&self)")
                && hits == 1
            {
                scan.definitions += 1;
            } else if file == cli_main
                && code.trim() == "let options = err.repair_options();"
                && hits == 1
            {
                scan.cli_calls += 1;
            } else {
                scan.foreign.push(format!(
                    "{}:{}: {}",
                    file.display(),
                    line_no + 1,
                    line.trim()
                ));
            }
        }
    }
    scan
}

/// Occurrences of `ident` in `code` as a whole identifier.
fn identifier_hits(code: &str, ident: &str) -> usize {
    let is_ident = |c: char| c.is_ascii_alphanumeric() || c == '_';
    code.match_indices(ident)
        .filter(|(at, _)| {
            let before = code[..*at].chars().next_back();
            let after = code[at + ident.len()..].chars().next();
            !before.is_some_and(is_ident) && !after.is_some_and(is_ident)
        })
        .count()
}

fn collect_rs(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).expect("read dir") {
        let path = entry.expect("dir entry").path();
        if path.is_dir() {
            collect_rs(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            out.push(path);
        }
    }
}

/// Row `spec-surface-0709/23-refusals-carry-repair-options`, flipped GAP ->
/// PASS. The archived test idea, on the real validator: a `MutParamExit`
/// binding on a REQUIRES clause plus a proof-bearing import with no resolver.
/// The authority tier refuses both (`InvalidFunctionSummary`,
/// `UnauthenticatedImport` at the `backed_by` site), the linked walk with no
/// dependency supplied refuses the row (`ImportUnavailable`), and EVERY refusal
/// either path emits enumerates at least one way forward.
#[test]
fn spec_surface_0709_23_refusals_carry_repair_options() {
    let dep = callee("dep", 1);
    let mut importer = Module::new("importer");
    importer.target_info = dep.target_info.clone();
    let id = importer
        .intern_import(ModuleImport::new("dep", dep.stable_digest()).with_producer(Producer::TRust))
        .expect("Module::intern_import: test fixture");
    let ft = importer
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut requires = ProofFormula::smtlib2("(>= x 0)", "Bool");
    requires.bindings = vec![(
        "x".to_string(),
        ClauseBinding {
            sort: ClauseSort::Int,
            place: ClausePlace::MutParamExit { index: 0 },
        },
    )];
    let summary = FunctionSummary::new()
        .requiring(requires)
        .proved()
        .backed_by(ExternRef::new(id, "f").relying_on(ProofId::new(0)));
    let mut f = Function::declaration(FuncId::new(0), "f", ft, summary);
    f.producer = Some(Producer::TRust);
    importer
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");

    let authority = validate_module_with_authority(&importer, &RejectingModuleProofAuthority);
    assert!(
        authority.iter().any(|e| matches!(e,
            ValidationError::InvalidFunctionSummary { detail, .. } if detail.contains("MutParamExit"))),
        "{authority:?}"
    );
    assert!(
        authority.iter().any(|e| matches!(
            e,
            ValidationError::UnauthenticatedImport {
                site: "backed_by",
                ..
            }
        )),
        "{authority:?}"
    );

    let nothing: [&Module; 0] = [];
    let linked = validate_linked_module(
        &importer,
        &ModuleSet::new(nothing),
        &RejectingModuleProofAuthority,
    );
    let linked = linked.errors().to_vec();
    assert!(
        linked
            .iter()
            .any(|e| matches!(e, ValidationError::ImportUnavailable { .. })),
        "{linked:?}"
    );

    for error in authority.iter().chain(linked.iter()) {
        assert_eq!(
            shape_defects(error.repair_options()),
            None,
            "refusal without an enumerated way forward: {error}"
        );
    }
}

/// `fn f(x: u64) -> u64 { k }`, exported, target-pinned; `k` moves the digest.
fn callee(name: &str, k: u128) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info(
        name,
        trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        },
    );
    mb.set_default_producer(Producer::TRust);
    let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let _x = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let v = fb.uconst(Ty::U64, k);
    fb.ret(vec![v]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

// ---------------------------------------------------------------------------
// Adversarial review (WS4.18): options that point the reader the wrong way
// ---------------------------------------------------------------------------

/// Advice never grants authority: no option, on any filled variant, steers
/// the reader to a STRONGER status label, to the faith floor, or to an
/// affirmative non-license. Each phrase below is the shape such advice would
/// take ("mark it `Trusted`", "validate under `ImportPolicy::Structural`",
/// "grandfather the body", "record `BodyGate::Ungated`").
#[test]
fn no_repair_option_steers_toward_a_faith_tier() {
    const FAITH: &[&str] = &[
        "`Trusted`",
        "`Certified`",
        "Structural",
        "grandfather",
        "Ungated",
        "on faith",
        "faith-",
    ];
    let dep = callee("dep", 1);
    let mut importer = Module::new("importer");
    let id = importer
        .intern_import(ModuleImport::new("dep", dep.stable_digest()))
        .expect("Module::intern_import: test fixture");
    let digest_mismatch = importer
        .verify_import(id, &callee("dep", 2))
        .expect_err("a rebuilt dependency is a different module");
    let mut offending = Vec::new();
    let rows = listed_variants()
        .into_iter()
        .map(|(name, error)| (name, error.repair_options()))
        .chain(std::iter::once((
            "DigestMismatch",
            digest_mismatch.repair_options(),
        )));
    for (name, options) in rows {
        for option in options {
            for phrase in FAITH {
                if option.contains(phrase) {
                    offending.push(format!("{name}: {phrase:?} in {option:?}"));
                }
            }
        }
    }
    assert_eq!(offending, Vec::<String>::new());
}

/// A dependency that WAS supplied and authenticated, cited by a `backed_by`
/// whose local contract says more than the far one: the linked walk refuses
/// the site (`UnauthenticatedImport`, `backed_by`). Before the review the
/// options only said "supply the dependency" (already done) and "re-emit
/// against a rebuild" (it is not one) — neither is the repair. The options
/// must name the restatement.
#[cfg(feature = "clean-tv-anchor")]
#[test]
fn a_supplied_dependency_with_a_mis_restated_contract_is_told_to_restate_it() {
    use trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate;
    use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};

    let clause = || ProofFormula::smtlib2("(= 1 1)", "Bool");
    let contract = || {
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .ensuring(clause())
    };
    let mut dep = callee("dep", 1);
    let f = dep.functions[0].id;
    dep.functions[0].summary = Some(contract().proved());
    let obligation = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "ensures (= 1 1)",
    )
    .with_function(f)
    .with_formula(clause());
    let certificate = contract_clean_cic_certificate(&obligation, "contract-prover")
        .expect("(= 1 1) is kernel-provable");
    dep.proof_obligations.push(obligation);
    dep.proof_certificates.push(certificate);
    assert_eq!(trust_ir_build::validate_module(&dep), Vec::new());

    let mut root = Module::new("root");
    root.target_info = dep.target_info.clone();
    let id = root
        .intern_import(ModuleImport::new("dep", dep.stable_digest()).with_producer(Producer::TRust))
        .expect("Module::intern_import: test fixture");
    let ft = root
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let says_more = contract()
        .ensuring(ProofFormula::smtlib2("(= 2 2)", "Bool"))
        .proved()
        .backed_by(ExternRef::new(id, "f").relying_on(ProofId::new(0)));
    let mut decl = Function::declaration(FuncId::new(0), "f", ft, says_more);
    decl.producer = Some(Producer::TRust);
    root.try_add_function(decl)
        .expect("Module::try_add_function: test fixture");

    let errors = validate_linked_module(
        &root,
        &ModuleSet::new([&dep]),
        &RejectingModuleProofAuthority,
    )
    .into_errors();
    let refused = errors
        .iter()
        .find(|e| {
            matches!(e, ValidationError::UnauthenticatedImport { site: "backed_by", detail, .. }
                if detail.contains("`ensures` differ"))
        })
        .unwrap_or_else(|| panic!("the mis-restated citation must be refused: {errors:?}"));
    assert!(
        refused
            .repair_options()
            .iter()
            .any(|option| option.contains("restate the far function's contract exactly")),
        "{:?}",
        refused.repair_options()
    );
}

/// The real structural validator's `DischargedWithoutCertificate` (a
/// `Discharged` label with no certificate) enumerates the replaying
/// capability route, not only the kernel term and the honest retreat.
#[test]
fn a_real_discharged_label_names_the_replaying_authority_route() {
    use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};
    let mut m = callee("m", 1);
    let f = m.functions[0].id;
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::PanicFreedom,
            ProofStatus::Discharged,
            "no panic",
        )
        .with_function(f),
    );
    let errors = trust_ir_build::validate_module(&m);
    let refused = errors
        .iter()
        .find(|e| matches!(e, ValidationError::DischargedWithoutCertificate { .. }))
        .unwrap_or_else(|| panic!("a bare Discharged label must be refused: {errors:?}"));
    let options = refused.repair_options();
    assert_eq!(shape_defects(options), None);
    assert!(
        options
            .iter()
            .any(|option| option.contains("validate_module_with_authority")),
        "{options:?}"
    );
}

/// The codegen tier's OTHER refusal: a body with no license at all (the
/// pre-v41 grandfather state) is `UnlicensedBodyForCodegen`, the refusal an
/// AI programmer holding a legacy artifact hits first. It enumerates options
/// too, and none of them infers a license.
#[test]
fn a_real_unlicensed_body_enumerates_options() {
    let mut m = callee("legacy", 1);
    m.functions[0].body_gate = None;
    let errors = trust_ir_build::validate_module_for_codegen(&m);
    let refused = errors
        .iter()
        .find(|e| matches!(e, ValidationError::UnlicensedBodyForCodegen { .. }))
        .unwrap_or_else(|| panic!("an unlicensed body must be refused for codegen: {errors:?}"));
    assert_eq!(shape_defects(refused.repair_options()), None);
}
