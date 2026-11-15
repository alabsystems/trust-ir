// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `trust-ir validate --link` — the SHIPPED-BINARY half
//! of import authentication.
//!
//! `trust_ir_build::validate_linked_module` has had its own suite since the
//! authority tier landed, but until this flag existed no shipped binary could
//! run it: `trust-ir validate` called `validate_module_report`, the faith
//! floor, which checks that a cross-crate row RESOLVES and nothing more. A
//! producer that writes an import row therefore had no consumer that re-earns
//! it, which is the gap these tests close.
//!
//! Every fixture below is REAL: the dependency's `Certified` obligation
//! carries a `CleanCic` certificate the in-process Clean kernel actually
//! re-checks, and the client's `Discharged` row is grounded by nothing except
//! the authenticated inheritance. So the positive test is a verdict the binary
//! earned, and each negative is a forgery that is spellable on the v41 wire.

mod common;

use std::fs;
use std::path::Path;
use std::process::Output;

use tempfile::tempdir;

use trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate;
use trust_ir::proof::{
    ObligationKind, ProofCertificate, ProofEvidence, ProofFormula, ProofObligation, ProofStatus,
};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{FuncId, ImportId, ProofId};
use trust_ir::{
    Endianness, ExternRef, Function, FunctionSummary, Module, ModuleImport, Producer, TargetInfo,
};
use trust_ir_build::{ModuleBuilder, validate_module};

use common::trust_ir_cmd;

// ---------------------------------------------------------------------------
// fixtures — the same pair `linked_import_authentication.rs` re-earns in-process
// ---------------------------------------------------------------------------

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

fn clause() -> ProofFormula {
    ProofFormula::smtlib2("(= 1 1)", "Bool")
}

fn contract() -> FunctionSummary {
    FunctionSummary::new()
        .with_params(vec!["x".to_string()])
        .ensuring(clause())
}

/// A dependency defining `fn f(x: i64) -> i64 { x + addend }` whose `proved`
/// contract is backed by a kernel-CERTIFIED Postcondition (#0). `addend` is
/// the knob the rebuilt-dependency negative turns: a different body is a
/// different module, whatever it is called.
fn dependency(name: &str, addend: i128) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info(name, target());
    mb.set_default_producer(Producer::TRust);
    let ft = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::I64);
    fb.switch_to_block(entry);
    let k = fb.iconst(Ty::I64, addend);
    let r = fb.add(Ty::I64, x, k);
    fb.ret(vec![r]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let f = module.functions[0].id;
    module.functions[0].summary = Some(contract().proved());
    let obligation = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "ensures (= 1 1)",
    )
    .with_function(f)
    .with_formula(clause());
    let certificate = contract_clean_cic_certificate(&obligation, "contract-prover")
        .expect("(= 1 1) is genuinely kernel-provable");
    module.proof_obligations.push(obligation);
    module.proof_certificates.push(certificate);
    assert!(
        validate_module(&module).is_empty(),
        "the dependency fixture must validate standalone: {:?}",
        validate_module(&module)
    );
    module
}

/// A client recording `dep` by MEASURED digest, declaring `f` body-less with
/// the far signature, and restating the far Postcondition as a local
/// `Discharged` row grounded by an `InheritedFromCallee { external: Some }`
/// certificate.
fn client(name: &str, dep: &Module) -> Module {
    let mut m = Module::new(name);
    m.target_info = Some(target());
    let id: ImportId = m
        .intern_import(
            // MEASURED, never asserted: the digest is computed over the exact
            // dependency module this client was built against.
            ModuleImport::new(dep.name.clone(), dep.stable_digest()).with_producer(Producer::TRust),
        )
        .expect("Module::intern_import: test fixture");
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = Function::declaration(FuncId::new(0), "f", ft, contract());
    f.producer = Some(Producer::TRust);
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
    let fid = m.functions[0].id;
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "inherited ensures (= 1 1)",
        )
        .with_function(fid)
        .with_formula(clause()),
    );
    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "compose".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee: fid,
            // The LOCAL restatement, equal to `certificate.obligation`; the FAR
            // id belongs only in `ExternRef.obligation`.
            obligation: ProofId::new(0),
            external: Some(ExternRef::new(id, "f").relying_on(ProofId::new(0))),
        },
        assurance: None,
    });
    m
}

fn write_bin(dir: &Path, stem: &str, module: &Module) -> std::path::PathBuf {
    let path = dir.join(format!("{stem}.tmbc"));
    fs::write(
        &path,
        trust_ir::binary::serialize_module(module).expect("serialize_module: test fixture"),
    )
    .expect("write module");
    path
}

fn validate(args: &[&std::path::Path]) -> Output {
    let mut cmd = trust_ir_cmd();
    cmd.arg("validate");
    // The subject is the LAST path; every earlier one is a `--link`.
    let (subject, deps) = args.split_last().expect("at least a subject");
    for dep in deps {
        cmd.arg("--link").arg(dep);
    }
    cmd.arg(subject).output().expect("run trust-ir")
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

// ---------------------------------------------------------------------------
// the round trip: a consumer BINARY re-earns the producer's rows
// ---------------------------------------------------------------------------

#[test]
fn link_re_earns_the_clients_cross_crate_row_against_the_dependency_it_measured() {
    let dir = tempdir().expect("tempdir");
    let dep = dependency("dep", 1);
    let client = client("client", &dep);
    let dep_path = write_bin(dir.path(), "dep", &dep);
    let client_path = write_bin(dir.path(), "client", &client);

    let out = validate(&[&dep_path, &client_path]);
    let text = format!("{}{}", stdout(&out), stderr(&out));
    assert!(out.status.success(), "the pair must re-earn: {text}");
    assert!(
        text.contains("re-earned"),
        "the linked verdict must be reported, not merely implied: {text}"
    );
    assert!(
        text.contains("re-earned"),
        "the verdict must say the claim was re-earned: {text}"
    );
    // The dependency was bound by the digest the CLIENT recorded, and the CLI
    // prints what it measured so an operator can compare the two.
    assert!(
        text.contains(&dep.stable_digest().to_string()),
        "the measured dependency digest must be reported: {text}"
    );
}

#[test]
fn the_client_alone_fails_the_faith_floor_because_a_cross_crate_row_grounds_nothing() {
    let dir = tempdir().expect("tempdir");
    let dep = dependency("dep", 1);
    let client = client("client", &dep);
    let client_path = write_bin(dir.path(), "client", &client);

    // No --link: the module still fails PLAIN validation, because a
    // cross-crate `Discharged` row is grounded only under the linked walk.
    // This is asserted, not worked around.
    let out = validate(&[&client_path]);
    assert!(
        !out.status.success(),
        "a client whose only grounding is an unauthenticated inheritance must fail alone"
    );
    let text = format!("{}{}", stdout(&out), stderr(&out));
    assert!(
        text.contains("DischargedWithoutCertificate") || text.contains("discharged"),
        "the refusal must name the ungrounded discharge: {text}"
    );
    // And the import row it carries is reported UNCHECKED — never as agreement.
    assert!(
        text.contains("UNCHECKED"),
        "an import row with no --link must be reported unchecked: {text}"
    );
    assert!(
        text.contains("not agreement"),
        "silence about an import row must not read as agreement: {text}"
    );
}

// ---------------------------------------------------------------------------
// negatives — each one is a wrong row a faith-floor consumer would have taken
// ---------------------------------------------------------------------------

#[test]
fn a_rebuilt_dependency_with_the_same_name_is_refused() {
    let dir = tempdir().expect("tempdir");
    let dep = dependency("dep", 1);
    let client = client("client", &dep);
    // REBUILT: same module name, same symbol, same signature, same contract,
    // different body. Identity is the digest, so this is a different module.
    let rebuilt = dependency("dep", 2);
    assert_ne!(
        dep.stable_digest(),
        rebuilt.stable_digest(),
        "the rebuild must actually move the digest, or this test proves nothing"
    );
    assert_eq!(dep.name, rebuilt.name, "the rebuild keeps the name");

    let client_path = write_bin(dir.path(), "client", &client);
    let rebuilt_path = write_bin(dir.path(), "dep", &rebuilt);

    let out = validate(&[&rebuilt_path, &client_path]);
    assert!(
        !out.status.success(),
        "the client's row cites the ORIGINAL dependency; the rebuild must not satisfy it"
    );
    let text = format!("{}{}", stdout(&out), stderr(&out));
    assert!(
        text.contains("linked validation failed"),
        "the refusal must come from the linked walk: {text}"
    );
    // Content-keyed lookup: a rebuilt dependency is not the cited one, so the
    // import resolves to nothing rather than to the wrong thing.
    assert!(
        text.to_lowercase().contains("unavailable") || text.to_lowercase().contains("digest"),
        "the refusal must name the unmet import, not a generic error: {text}"
    );
}

#[test]
fn a_dependency_nobody_supplied_is_unavailable_not_assumed() {
    let dir = tempdir().expect("tempdir");
    let dep = dependency("dep", 1);
    let client = client("client", &dep);
    // A THIRD module, well-formed and irrelevant: supplying something is not
    // supplying the cited thing.
    let decoy = dependency("dep", 7);
    let client_path = write_bin(dir.path(), "client", &client);
    let decoy_path = write_bin(dir.path(), "decoy", &decoy);

    let out = validate(&[&decoy_path, &client_path]);
    assert!(
        !out.status.success(),
        "an unmet import must never be a silent pass"
    );
    let text = format!("{}{}", stdout(&out), stderr(&out));
    assert!(
        text.contains("linked validation failed"),
        "the refusal must come from the linked walk: {text}"
    );
}

#[test]
fn a_module_with_no_import_rows_and_no_link_reports_nothing_either_way() {
    let dir = tempdir().expect("tempdir");
    let dep = dependency("dep", 1);
    let dep_path = write_bin(dir.path(), "dep", &dep);
    let out = validate(&[&dep_path]);
    assert!(out.status.success(), "{}", stderr(&out));
    let text = format!("{}{}", stdout(&out), stderr(&out));
    assert!(
        !text.contains("UNCHECKED") && !text.contains("linked"),
        "a module with no imports must produce no cross-crate finding: {text}"
    );
}

#[test]
fn the_dependency_is_bound_by_content_not_by_the_path_it_arrived_on() {
    let dir = tempdir().expect("tempdir");
    let dep = dependency("dep", 1);
    let client = client("client", &dep);
    let client_path = write_bin(dir.path(), "client", &client);
    // Same bytes, a filename that says nothing true about it.
    let odd_path = write_bin(dir.path(), "not-the-dependency-at-all", &dep);
    let out = validate(&[&odd_path, &client_path]);
    assert!(
        out.status.success(),
        "the digest is identity; the path is not: {}",
        stderr(&out)
    );
}

// ---------------------------------------------------------------------------
// WS1.7 = WS4.8 (DG-78): every import row and every call edge, through the
// shipped binary — the CLI twins of `linked_import_authentication.rs`
// ---------------------------------------------------------------------------

/// A call-only dependency `g(x: u64) -> u64 { x + k }`.
fn callee(name: &str, k: u128) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info(name, target());
    mb.set_default_producer(Producer::TRust);
    let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("g", ft);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let kk = fb.uconst(Ty::U64, k);
    let r = fb.add(Ty::U64, x, kk);
    fb.ret(vec![r]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// A call-only importer: one row recording `digest` under `dep_name`, a
/// body-less `g(param) -> u64`, and `program() -> u64 { g(1) }`.
fn call_only(dep_name: &str, digest: trust_ir::proof::ProofDigest, param: Ty) -> Module {
    let mut mb = ModuleBuilder::new_with_target_info("root", target());
    mb.set_default_producer(Producer::TRust);
    let gt = mb.add_func_type(vec![param.clone()], vec![Ty::U64]);
    let pt = mb.add_func_type(vec![], vec![Ty::U64]);
    let g = mb.declare_function("g", gt);
    let mut fb = mb.function("program", pt);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let one = fb.uconst(param, 1);
    let r = fb.call(g, vec![one]);
    fb.ret(vec![r]);
    // The import row makes this a v41+ blob, and a v41-or-later producer
    // MUST make a `body_gate` claim for every bodied function (`validate`
    // refuses a tag-0 body by name, `--link` included). No gate ran: say so.
    fb.set_body_gate(trust_ir::BodyGate::Ungated);
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.intern_import(ModuleImport::new(dep_name, digest).with_producer(Producer::TRust))
        .expect("Module::intern_import: test fixture");
    m
}

fn refused_with(out: &Output, needle: &str) -> String {
    let text = format!("{}{}", stdout(out), stderr(out));
    assert!(!out.status.success(), "must be refused: {text}");
    assert!(
        text.contains("linked validation failed"),
        "the refusal must come from the linked walk: {text}"
    );
    assert!(text.contains(needle), "expected {needle:?} in: {text}");
    text
}

#[test]
fn link_authenticates_a_call_only_importer_and_its_call_edge() {
    let dir = tempdir().expect("tempdir");
    let dep = callee("dep", 1);
    let root = call_only("dep", dep.stable_digest(), Ty::U64);
    let dep_path = write_bin(dir.path(), "dep", &dep);
    let root_path = write_bin(dir.path(), "root", &root);
    let out = validate(&[&dep_path, &root_path]);
    let text = format!("{}{}", stdout(&out), stderr(&out));
    assert!(out.status.success(), "{text}");
    assert!(text.contains("all 1 import row authenticated"), "{text}");
    assert!(
        text.contains("cross-crate call edges: 1 authenticated"),
        "{text}"
    );
}

#[test]
fn link_refuses_a_call_only_row_with_a_garbage_digest() {
    let dir = tempdir().expect("tempdir");
    let dep = callee("dep", 1);
    let root = call_only(
        "dep",
        trust_ir::proof::ProofDigest::sha256([0xEE; 32]),
        Ty::U64,
    );
    let dep_path = write_bin(dir.path(), "dep", &dep);
    let root_path = write_bin(dir.path(), "root", &root);
    refused_with(&validate(&[&dep_path, &root_path]), "ImportUnavailable");
}

#[test]
fn link_refuses_a_call_edge_whose_signature_skews() {
    let dir = tempdir().expect("tempdir");
    let dep = callee("dep", 1);
    let root = call_only("dep", dep.stable_digest(), Ty::U32);
    let dep_path = write_bin(dir.path(), "dep", &dep);
    let root_path = write_bin(dir.path(), "root", &root);
    let text = refused_with(&validate(&[&dep_path, &root_path]), "site: \"call\"");
    assert!(
        text.contains("signature mismatch — parameter 0 type u32 vs u64"),
        "{text}"
    );
}

#[test]
fn link_refuses_an_obligation_free_backed_by_to_a_missing_symbol() {
    let dir = tempdir().expect("tempdir");
    let dep = callee("dep", 1);
    let mut root = call_only("dep", dep.stable_digest(), Ty::U64);
    let g = root.function_by_name("g").unwrap().id;
    let decl = root.function_by_id_mut(g).unwrap();
    decl.name = "h".to_string();
    decl.summary = Some(
        FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .backed_by(ExternRef::new(ImportId::new(0), "h")),
    );
    let dep_path = write_bin(dir.path(), "dep", &dep);
    let root_path = write_bin(dir.path(), "root", &root);
    refused_with(
        &validate(&[&dep_path, &root_path]),
        "no function in the dependency carries symbol",
    );
}

#[test]
fn link_refuses_a_symbol_two_dependencies_export_as_ambiguous() {
    let dir = tempdir().expect("tempdir");
    let a = callee("dep_a", 1);
    let b = callee("dep_b", 2);
    let mut root = call_only("dep_a", a.stable_digest(), Ty::U64);
    root.intern_import(
        ModuleImport::new("dep_b", b.stable_digest()).with_producer(Producer::TRust),
    )
    .expect("Module::intern_import: test fixture");
    let a_path = write_bin(dir.path(), "dep_a", &a);
    let b_path = write_bin(dir.path(), "dep_b", &b);
    let root_path = write_bin(dir.path(), "root", &root);
    refused_with(
        &validate(&[&a_path, &b_path, &root_path]),
        "AmbiguousImportedSymbol",
    );
}

#[test]
fn link_refuses_an_uncited_row_whose_dependency_was_not_supplied() {
    let dir = tempdir().expect("tempdir");
    let dep = callee("dep", 1);
    let other = callee("other", 9);
    let mut root = call_only("dep", dep.stable_digest(), Ty::U64);
    root.intern_import(
        ModuleImport::new("other", other.stable_digest()).with_producer(Producer::TRust),
    )
    .expect("Module::intern_import: test fixture");
    let dep_path = write_bin(dir.path(), "dep", &dep);
    let root_path = write_bin(dir.path(), "root", &root);
    refused_with(&validate(&[&dep_path, &root_path]), "ImportUnavailable");
}

#[test]
fn link_reports_a_libc_declaration_as_unbound_without_refusing_it() {
    let dir = tempdir().expect("tempdir");
    let dep = callee("dep", 1);
    let mut root = call_only("dep", dep.stable_digest(), Ty::U64);
    let abs_ty = root
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let next = FuncId::new(u32::try_from(root.functions.len()).unwrap());
    root.try_add_function(Function::new(
        next,
        "abs",
        abs_ty,
        trust_ir::value::BlockId::new(0),
    ))
    .expect("Module::try_add_function: test fixture");
    let dep_path = write_bin(dir.path(), "dep", &dep);
    let root_path = write_bin(dir.path(), "root", &root);
    let out = validate(&[&dep_path, &root_path]);
    let text = format!("{}{}", stdout(&out), stderr(&out));
    assert!(out.status.success(), "{text}");
    assert!(
        text.contains("1 body-less declaration bound to NO supplied dependency")
            && text.contains("root::abs"),
        "the unbound residue must be named, never silent: {text}"
    );
}
