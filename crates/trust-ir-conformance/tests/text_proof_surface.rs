// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Roadmap WS4.4 (F-064, F-070, F-071): text carries the proof surface —
// function summaries, clause bindings, certificate assurance, the `clean_cic`
// kernel re-check directive and the v41 obligation kinds.
//
// This file holds the text legs the roadmap places in `trust-ir-conformance`
// (standing gate 8, `wire-format-goldens`) and ports the proof-program rows
// that flip GAP -> PASS here and have no in-repo home elsewhere, each test
// named after its row (archived at reports/2026-09-17-two-language-proof-program/):
//
//   * `b2.uf02`  — the v41 obligation kinds parse from text;
//   * `b3.uf05`  — a kernel-Certified module survives text and re-certifies;
//   * `spec-surface-0709/06-clause-carriage-requires-ensures`;
//   * `a.rust.contracts.carry_experiment.text` — summaries survive 2/2;
//   * `design-0827/text-format-summary-loss` — bin -> text -> bin is exact.
//
// Each has a negative twin refused by the SPECIFIC named reason, and the
// roadmap's two parser-does-not-second-guess-the-validator twins
// (`mut_exit(0)` on a `requires` clause; `custom("", "x")`) live here too.

use trust_ir::format::{canonical_checked, canonicalize, text_losses};
use trust_ir::parser::parse_module;
use trust_ir::proof::{
    ClauseBinding, ClausePlace, ClauseSort, ObligationKind, ProofDigest, ProofEvidence,
    ProofFormula, ProofLineageId, ProofObligation, ProofStatus, ProofTransform,
    ProofTransformStage,
};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, ProofId};
use trust_ir::{ExternRef, FunctionSummary, Module, ModuleImport, Producer};
use trust_ir_build::{
    ModuleBuilder, ValidationError, certify_identity_lineage_rung, validate_module,
};

// The fixture generators (tests/generate.rs), compiled once as the library's
// `fixtures` module.
use trust_ir_conformance::fixtures as generate;

fn bound(text: &str, bindings: Vec<(&str, ClauseSort, ClausePlace)>) -> ProofFormula {
    let mut formula = ProofFormula::smtlib2(text, "Bool");
    formula.bindings = bindings
        .into_iter()
        .map(|(name, sort, place)| (name.to_string(), ClauseBinding { sort, place }))
        .collect();
    formula
}

/// `bin -> text -> bin`: the module text reads back, and returns the decoded
/// module (which must equal `canonicalize(m)`).
fn through_text(m: &Module) -> Module {
    assert_eq!(text_losses(m), vec![], "the module must be loss-free");
    let bin = trust_ir::binary::deserialize_module(
        &trust_ir::binary::serialize_module(m).expect("serialize_module: test fixture"),
    )
    .expect("binary");
    let text = canonical_checked(&bin).expect("loss-free text");
    let back = parse_module(&text).unwrap_or_else(|e| panic!("{e}\n{text}"));
    assert_eq!(back, canonicalize(&bin), "text is exact");
    back
}

/// `fn withdraw(balance: &mut u64, amount: u64)` with `requires amount <
/// 2^63` and `ensures balance' >= amount` — the test idea of
/// `spec-surface-0709/06-clause-carriage-requires-ensures`, every binding a
/// faithful reading of its place's IR type. (A `&mut u64` parameter's ENTRY
/// value has no clause place: `param(0)` is the reference itself, which no
/// `ClauseSort` reads, so the clauses bind the entry value of `amount` and the
/// exit value of `balance`.)
fn withdraw() -> Module {
    let mut mb = ModuleBuilder::new("withdraw");
    let balance = Ty::RefMut(Box::new(Ty::U64));
    let ft = mb.add_func_type(vec![balance.clone(), Ty::U64], vec![]);
    let mut fb = mb.function("withdraw", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.add_block_param(entry, balance);
    fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.functions[0].summary = Some(
        FunctionSummary::new()
            .with_params(vec!["balance".into(), "amount".into()])
            .requiring(bound(
                "(bvult amount #x8000000000000000)",
                vec![(
                    "amount",
                    ClauseSort::BitVec(64),
                    ClausePlace::Param { index: 1 },
                )],
            ))
            .ensuring(bound(
                "(bvuge balance_exit amount)",
                vec![
                    (
                        "balance_exit",
                        ClauseSort::BitVec(64),
                        ClausePlace::MutParamExit { index: 0 },
                    ),
                    (
                        "amount",
                        ClauseSort::BitVec(64),
                        ClausePlace::Param { index: 1 },
                    ),
                ],
            )),
    );
    m
}

/// Row `spec-surface-0709/06-clause-carriage-requires-ensures`, GAP -> PASS:
/// E1's multiple requires/ensures clauses per function survive serialization
/// in ALL FOUR formats — text included, which had no summary syntax before
/// WS4.4. The negative twin is the roadmap's: a `mut_exit(0)` binding moved
/// onto the `requires` clause PARSES (the grammar spells every place
/// everywhere) and the validator refuses it by name — the parser does not
/// second-guess the validator.
#[test]
fn spec_surface_0709_06_clause_carriage_requires_ensures() {
    let m = withdraw();
    assert_eq!(validate_module(&m), vec![]);
    let back = through_text(&m);
    let summary = back.functions[0].summary.as_ref().expect("carried");
    assert_eq!((summary.requires.len(), summary.ensures.len()), (1, 1));
    assert_eq!(back.functions[0].summary, m.functions[0].summary);
    let json: Module = serde_json::from_str(&serde_json::to_string(&m).unwrap()).unwrap();
    let msgpack: Module = rmp_serde::from_slice(&rmp_serde::to_vec(&m).unwrap()).unwrap();
    assert_eq!(json, m);
    assert_eq!(msgpack, m);

    // Negative twin: `mut_exit(0)` on the requires clause.
    let text = canonical_checked(&m).unwrap();
    let requires_line = text
        .lines()
        .find(|line| line.contains("; #requires:"))
        .expect("requires line")
        .to_owned();
    let twin = text.replacen(
        &requires_line,
        &requires_line.replacen(
            "bind \"amount\" bv(64) param(1)",
            "bind \"amount\" bv(64) mut_exit(0)",
            1,
        ),
        1,
    );
    assert_ne!(twin, text);
    let parsed = parse_module(&twin).expect("the grammar parses mut_exit anywhere");
    let errors = validate_module(&parsed);
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::InvalidFunctionSummary { function: 0, detail }]
                if detail.contains("uses MutParamExit") && detail.contains("requires clause")
        ),
        "{errors:?}"
    );
}

/// Row `b2.uf02` (F-071), GAP -> PASS: `termination`, `ownership` and
/// `custom("<ns>", "<name>")` parse from module text, and the text image
/// validates with the binary image's verdict. Negative twin (the roadmap's):
/// `custom("", "x")` PARSES, and the validator refuses it as
/// `UnpinnedCustomObligationNamespace` — namespace admission is the
/// validator's, never the parser's.
#[test]
fn b2_uf02_text_parses_the_v41_obligation_kinds() {
    let mut m = withdraw();
    let f = m.functions[0].id;
    for (id, kind) in [
        ObligationKind::Termination,
        ObligationKind::Ownership,
        ObligationKind::Custom {
            namespace: "trust.contract".into(),
            name: "frame".into(),
        },
    ]
    .into_iter()
    .enumerate()
    {
        m.proof_obligations.push(
            ProofObligation::new(ProofId::new(id as u32), kind, ProofStatus::Pending, "probe")
                .with_function(f),
        );
    }
    let bin_verdict = validate_module(&m);
    assert_eq!(bin_verdict, vec![]);
    let back = through_text(&m);
    assert_eq!(back.proof_obligations, m.proof_obligations);
    assert_eq!(validate_module(&back), bin_verdict);

    let text = canonical_checked(&m).unwrap();
    let twin = text.replacen(
        "custom(\"trust.contract\", \"frame\")",
        "custom(\"\", \"x\")",
        1,
    );
    assert_ne!(twin, text);
    let parsed = parse_module(&twin).expect("an empty namespace parses");
    let errors = validate_module(&parsed);
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::UnpinnedCustomObligationNamespace { obligation: 2, namespace, .. }]
                if namespace.is_empty()
        ),
        "{errors:?}"
    );
}

/// Row `b3.uf05` (F-070), GAP -> PASS: a kernel-Certified module (a
/// `clean_cic` certificate with its kernel re-check directive) survives text
/// and re-certifies in-process. Negative twin: the same text with the recheck
/// clause cut is refused as `CertifiedCleanCicKernelRecheckFailed`.
#[test]
fn b3_uf05_text_carries_the_kernel_recheck_directive() {
    let mut mb = ModuleBuilder::new("b3_uf05");
    let ft = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("addmul", ft);
    fb.set_producer(Producer::Clean);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, Ty::U64);
    let b = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let ab = fb.mul(Ty::U64, a, b);
    let out = fb.add(Ty::U64, ab, a);
    fb.ret(vec![out]);
    let f = fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let (_node, obligation, certificate) = certify_identity_lineage_rung(
        &m,
        ProofLineageId::new(0),
        ProofId::new(0),
        ProofTransform::new(ProofTransformStage::Frontend, "identity", "b3", "1.0.0"),
        f,
    )
    .expect("addmul is in the clean_backend_tv fragment");
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(certificate);
    assert_eq!(validate_module(&m), vec![]);
    let back = through_text(&m);
    assert!(matches!(
        &back.proof_certificates[0].evidence,
        ProofEvidence::CleanCic {
            kernel_recheck: Some(_),
            ..
        }
    ));
    assert_eq!(validate_module(&back), vec![], "re-certifies from text");

    let text = canonical_checked(&m).unwrap();
    let at = text.find(" recheck module ").expect("the recheck clause");
    let end = at + text[at..].find('\n').expect("line end");
    let cut = format!("{}{}", &text[..at], &text[end..]);
    let errors = validate_module(&parse_module(&cut).expect("parses"));
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::CertifiedCleanCicKernelRecheckFailed { reason, .. }]
                if reason.contains("carries no kernel-recheck directive")
        ),
        "{errors:?}"
    );
}

/// A producer-shaped module whose contracts ARE carried: two functions, each
/// with a summary (`requires` / `ensures` / `decreases`), one of them a
/// `backed_by` declaration of an import.
fn carried_contracts() -> Module {
    let mut m = withdraw();
    // The body-less `External` declaration below is a cross-object ABI
    // boundary, well-defined only against a pinned target.
    m.target_info = Some(trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: Default::default(),
    });
    let dep = m
        .intern_import(
            ModuleImport::new("contracts_dep", ProofDigest::sha256([0x37; 32]))
                .with_producer(Producer::TRust),
        )
        .expect("Module::intern_import: test fixture");
    let ft = m.functions[0].ty;
    m.functions[0].summary.as_mut().unwrap().decreases = vec![bound(
        "amount",
        vec![(
            "amount",
            ClauseSort::BitVec(64),
            ClausePlace::Param { index: 1 },
        )],
    )];
    m.try_add_function(trust_ir::Function::declaration(
        FuncId::new(1),
        "_ZN8contracts7deposit",
        ft,
        FunctionSummary::new()
            .with_params(vec!["balance".into(), "amount".into()])
            .ensuring(ProofFormula::smtlib2("true", "Bool"))
            .proved()
            .backed_by(ExternRef::new(dep, "_ZN8contracts7deposit").relying_on(ProofId::new(4))),
    ))
    .expect("Module::try_add_function: test fixture");
    m
}

/// Row `a.rust.contracts.carry_experiment.text` (F-064), GAP -> PASS. The
/// archived Part A run measured, on a real emitted module, that "once the
/// contract IS carried, the TEXT leg drops it (summaries surviving 0/2)". The
/// archive's module lives under the non-exported `reports/` tree, so the port
/// rebuilds its SHAPE — two functions, both carrying a summary — and asserts
/// 2/2 survive text. Negative twin: the text with its summary blocks deleted
/// (what the pre-WS4.4 grammar produced) keeps 0/2.
#[test]
fn a_rust_contracts_carry_experiment_text() {
    let m = carried_contracts();
    assert_eq!(validate_module(&m), vec![]);
    let back = through_text(&m);
    let surviving = back
        .functions
        .iter()
        .zip(&m.functions)
        .filter(|(b, o)| b.summary.is_some() && b.summary == o.summary)
        .count();
    assert_eq!(surviving, 2, "summaries surviving text");

    let text = canonical_checked(&m).unwrap();
    let stripped: String = text
        .lines()
        .filter(|line| {
            ![
                "; #summary:",
                "; #requires:",
                "; #ensures:",
                "; #decreases:",
                "; #backed-by:",
            ]
            .iter()
            .any(|word| line.contains(word))
        })
        .map(|line| format!("{line}\n"))
        .collect();
    let dropped = parse_module(&stripped).expect("parses");
    assert_eq!(
        dropped
            .functions
            .iter()
            .filter(|f| f.summary.is_some())
            .count(),
        0
    );
}

/// Row `design-0827/text-format-summary-loss` (F-064), GAP -> PASS: the test
/// idea verbatim — a function carrying a `proved` summary with bindings,
/// `decreases` and `backed_by`, converted bin -> text -> bin, is EQUAL
/// (the archive measured `summary: None` with no error). Negative twin: a
/// `; #requires:` line with no preceding `#summary` — the one construct the
/// block grammar cannot place — is a named `ParseError`, never a silently
/// attached clause.
#[test]
fn design_0827_text_format_summary_loss() {
    let m = carried_contracts();
    let bin = trust_ir::binary::serialize_module(&m).expect("serialize_module: test fixture");
    let text = canonical_checked(&trust_ir::binary::deserialize_module(&bin).unwrap()).unwrap();
    let rebin = trust_ir::binary::serialize_module(&parse_module(&text).unwrap())
        .expect("serialize_module: test fixture");
    assert_eq!(rebin, bin, "bin -> text -> bin is byte-identical");

    let header = text
        .lines()
        .find(|line| line.contains("; #summary: unproved"))
        .expect("withdraw's header")
        .to_owned();
    let err = parse_module(&text.replacen(&format!("{header}\n"), "", 1))
        .expect_err("a clause without its header is refused");
    assert!(
        err.message
            .contains("`#requires` without a preceding `#summary` directive"),
        "{err}"
    );
}

/// The roadmap's positive clause: the `proof_surface` corpus fixture (every
/// summary clause kind, every function place, a `backed_by` citation, one
/// obligation per v41 kind, one certificate per `CoverageBound`) re-validates
/// from its TEXT image with the same verdict as from its binary image — and
/// the `lean_library_envelope` fixture (a kernel-Certified `clean_cic` row
/// with its recheck directive and a `custom(..)` theorem reference) likewise.
#[test]
fn text_images_revalidate_with_the_binary_verdict() {
    for build in [
        generate::build_proof_surface,
        generate::build_lean_library_envelope,
        generate::build_composition,
        generate::build_spec_carrier,
    ] {
        let m = build().expect("the fixture builds");
        let bin = trust_ir::binary::deserialize_module(
            &trust_ir::binary::serialize_module(&m).expect("serialize_module: test fixture"),
        )
        .expect("binary");
        let back = through_text(&m);
        assert_eq!(
            validate_module(&back),
            validate_module(&canonicalize(&bin)),
            "{}",
            m.name
        );
        assert_eq!(validate_module(&back), vec![], "{}", m.name);
    }
}
