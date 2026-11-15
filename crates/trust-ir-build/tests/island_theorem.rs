// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! User-theorem certification through an island environment (roadmap WS1.13;
//! finding F-012, the check half of F-008).
//!
//! THE HOLES. A kernel-proved Lean theorem could travel only as an unchecked
//! claim: `Certified` demands `ProofEvidence::CleanCic`, and the re-checker
//! dispatched a CLOSED anchor list with no anchor meaning "this user theorem,
//! re-checked" (F-012). And a `clean_backend_tv` certificate proved "the
//! emitted function denotes the RECORDED comparand" — the comparand being the
//! minter's choice, a producer that miscompiled and then minted was
//! indistinguishable from an honest one (F-008).
//!
//! THE RULES.
//!
//! * `CertificateBinding.environment: Option<IslandEnvironment>` carries the
//!   island — the canonical, resource-bounded encoding of a Clean declaration
//!   closure plus its digest (`trust_ir.clean_cic.island.v1`). The validator
//!   recomputes the digest, decodes with the island's own bounded decoder,
//!   refuses a redeclared name or an axiom, and installs every declaration
//!   with the kernel's checked `add_decl`.
//! * The `clean_island` anchor (`Clean.Island`) certifies ONLY a
//!   `Custom { namespace: "lean.theorem", name }` row, and such a row is
//!   `Certified` through no other anchor. The cited island theorem passes
//!   the rooted audit and its type must be DEFINITIONALLY EQUAL to the
//!   statement the pinned grounder derives from the row's own formula.
//! * SYMBOL BRIDGE: every island constant the statement cites must be the
//!   `source.decl` of a function whose `clean_backend_tv` certificate carries
//!   the SAME island and passed the F-008 check.
//! * F-008: a `clean_backend_tv` certificate that carries an island must have
//!   a comparand definitionally equal to the value of `source.decl` there. An
//!   island-free one keeps its mint-time meaning, and is refused under
//!   `ValidationConfig::with_source_bound_certificates(true)`.
//!
//! Tests whose name starts `b3_gap_` / `lean_home_` are in-repo ports of the
//! two-language proof program's ratchet rows of the same id (dots spelled
//! `_`); the conformance ratchet table holds the b3 rows themselves.
//!
//! FEATURES. Everything here needs the default-ON `clean-tv-anchor` feature
//! (the island is a kernel object). Transport assertions are behind
//! `#[cfg(feature = "serde")]`, as in `certificate_binding.rs`.

use trust_ir::proof::{
    CertificateBinding, CleanCicKernelRecheck, IslandEnvironment, KERNEL_ANCHOR_CLEAN_BACKEND_TV,
    KERNEL_ANCHOR_CLEAN_ISLAND, KERNEL_ANCHOR_CLEAN_ISLAND_MODULE, ObligationKind,
    ProofCertificate, ProofDigest, ProofEvidence, ProofFormula, ProofLineageId, ProofObligation,
    ProofStatus, ProofTransform, ProofTransformStage, RejectingModuleProofAuthority,
    SourceDefinitionRef, clean_cic_lineage_digest_v8, encode_island_declarations_v1,
    module_symbol_resolver,
};
use trust_ir::ty::Ty;
use trust_ir::value::ProofId;
use trust_ir::{BodyGate, FuncId, Inst, Module, Producer};
use trust_ir_build::clean_kernel::env::Declaration;
use trust_ir_build::clean_kernel::{BinderInfo, Expr, Level, Name};
use trust_ir_build::{
    ModuleBuilder, ValidationConfig, ValidationError, certify_identity_lineage_rung_bound,
    certify_identity_lineage_rung_island_bound, certify_island_theorem,
    is_admitted_obligation_namespace, kernel_certified_theorems, validate_module,
    validate_module_for_codegen, validate_module_report, validate_module_with_authority,
    validate_module_with_config,
};

// ===========================================================================
// kernel vocabulary (the island side, built by hand — never read back from
// trust-ir's own denotation of the emitted functions)
// ===========================================================================

fn nat() -> Expr {
    Expr::const_str("Nat")
}

fn eq_nat(lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), lhs, rhs],
    )
}

fn refl_nat(e: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [nat(), e],
    )
}

fn lam_nat(arity: usize, body: Expr) -> Expr {
    (0..arity).fold(body, |acc, _| Expr::lam(BinderInfo::Default, nat(), acc))
}

fn pi_nat(arity: usize, body: Expr) -> Expr {
    (0..arity).fold(body, |acc, _| Expr::pi(BinderInfo::Default, nat(), acc))
}

fn app2(f: &str, a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_str(f), [a, b])
}

/// `e % 2^64`.
fn wmod64(e: Expr) -> Expr {
    app2("Nat.mod", e, Expr::nat_lit_u128(1u128 << 64))
}

/// `Lib.addmul a b := (a*b % 2^64 + a) % 2^64`.
fn addmul_source() -> Expr {
    lam_nat(
        2,
        wmod64(app2(
            "Nat.add",
            wmod64(app2("Nat.mul", Expr::bvar(1), Expr::bvar(0))),
            Expr::bvar(1),
        )),
    )
}

fn definition(name: &str, arity: usize, value: Expr) -> Declaration {
    Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: pi_nat(arity, nat()),
        value,
        is_reducible: true,
    }
}

fn theorem(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
    }
}

/// `Lib.fst3 a b c := a`.
fn fst3_def() -> Declaration {
    definition("Lib.fst3", 3, lam_nat(3, Expr::bvar(2)))
}

/// `Lib.fst3_eq : ∀ a b c, Lib.fst3 a b c = a := fun a b c => rfl` — Lib.lean's
/// kernel-only theorem.
fn fst3_eq() -> Declaration {
    let applied = Expr::apps(
        Expr::const_str("Lib.fst3"),
        [Expr::bvar(2), Expr::bvar(1), Expr::bvar(0)],
    );
    theorem(
        "Lib.fst3_eq",
        pi_nat(3, eq_nat(applied, Expr::bvar(2))),
        lam_nat(3, refl_nat(Expr::bvar(2))),
    )
}

/// `Lib.addmul_6_7 : Lib.addmul 6 7 = 48 := rfl` — a closed statement.
fn addmul_6_7() -> Declaration {
    theorem(
        "Lib.addmul_6_7",
        eq_nat(
            Expr::apps(
                Expr::const_str("Lib.addmul"),
                [Expr::nat_lit(6), Expr::nat_lit(7)],
            ),
            Expr::nat_lit(48),
        ),
        refl_nat(Expr::nat_lit(48)),
    )
}

fn island_of(declarations: &[Declaration]) -> IslandEnvironment {
    IslandEnvironment::new(encode_island_declarations_v1(declarations).expect("island encodes"))
}

/// The honest island: `Lib.fst3`, `Lib.fst3_eq`, `Lib.addmul`, `Lib.addmul_6_7`.
fn island() -> IslandEnvironment {
    island_of(&[
        fst3_def(),
        fst3_eq(),
        definition("Lib.addmul", 2, addmul_source()),
        addmul_6_7(),
    ])
}

const FST3_EQ: &str =
    "(forall ((a (_ BitVec 64)) (b (_ BitVec 64)) (c (_ BitVec 64))) (= (Lib.fst3 a b c) a))";
const ADDMUL_6_7: &str = "(= (Lib.addmul 6 7) 48)";

// ===========================================================================
// module fixtures
// ===========================================================================

const FST3: usize = 0;
const ADDMUL: usize = 1;

/// `[Clean] fst3(a,b,c) = a` and `[Clean] addmul(a,b) = a*b + a`, all U64,
/// licensed by the Clean kernel-TV authority.
fn base_module() -> Module {
    let mut mb = ModuleBuilder::new("island_theorem");
    mb.set_default_producer(Producer::Clean);
    let ternary = mb.add_func_type(vec![Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]);
    let binary = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    {
        let mut f = mb.function("fst3", ternary);
        let e = f.create_block();
        let a = f.add_block_param(e, Ty::U64);
        let _b = f.add_block_param(e, Ty::U64);
        let _c = f.add_block_param(e, Ty::U64);
        f.switch_to_block(e);
        f.ret(vec![a]);
        f.build();
    }
    {
        let mut f = mb.function("addmul", binary);
        let e = f.create_block();
        let a = f.add_block_param(e, Ty::U64);
        let b = f.add_block_param(e, Ty::U64);
        f.switch_to_block(e);
        let p = f.mul(Ty::U64, a, b);
        let r = f.add(Ty::U64, p, a);
        f.ret(vec![r]);
        f.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    for func in &mut m.functions {
        func.body_gate = Some(BodyGate::Gated {
            authority: "clean-kernel-tv".to_string(),
            evidence: None,
        });
    }
    m
}

fn transform() -> ProofTransform {
    ProofTransform::new(ProofTransformStage::Frontend, "identity", "island", "1.0.0")
}

fn source(decl: &str) -> SourceDefinitionRef {
    SourceDefinitionRef {
        decl: decl.to_string(),
        closure_digest: ProofDigest::sha256([0x13; 32]),
    }
}

fn next_id(m: &Module) -> u32 {
    u32::try_from(m.proof_obligations.len()).expect("small fixture")
}

/// Push `function`'s island-bound TV row (source `decl`); returns its id.
fn push_island_tv(m: &mut Module, function: usize, island: &IslandEnvironment, decl: &str) -> u32 {
    let id = next_id(m);
    let (_, obligation, certificate) = certify_identity_lineage_rung_island_bound(
        m,
        ProofLineageId::new(id),
        ProofId::new(id),
        transform(),
        m.functions[function].id,
        island,
        source(decl),
    )
    .expect("the fixture function denotes its island declaration");
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(certificate);
    id
}

/// Push `function`'s BOUND but island-free TV row; returns its id.
fn push_bound_tv(m: &mut Module, function: usize) -> u32 {
    let id = next_id(m);
    let (_, obligation, certificate) = certify_identity_lineage_rung_bound(
        m,
        ProofLineageId::new(id),
        ProofId::new(id),
        transform(),
        m.functions[function].id,
    )
    .expect("the fixture function is in the backend-TV fragment");
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(certificate);
    id
}

/// Push a Certified `lean.theorem` row; returns its id.
fn push_theorem(m: &mut Module, name: &str, text: &str, island: &IslandEnvironment) -> u32 {
    let id = next_id(m);
    let (obligation, certificate) = certify_island_theorem(
        ProofId::new(id),
        name,
        ProofFormula::smtlib2(text, "Bool"),
        island,
    )
    .expect("the island theorem states the formula");
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(certificate);
    id
}

/// The honest module: `fst3` (#0) and `addmul` (#1) island-bound TV rows,
/// `Lib.fst3_eq` (#2) and `Lib.addmul_6_7` (#3) Certified through the island.
fn honest() -> Module {
    let island = island();
    let mut m = base_module();
    push_island_tv(&mut m, FST3, &island, "Lib.fst3");
    push_island_tv(&mut m, ADDMUL, &island, "Lib.addmul");
    push_theorem(&mut m, "Lib.fst3_eq", FST3_EQ, &island);
    push_theorem(&mut m, "Lib.addmul_6_7", ADDMUL_6_7, &island);
    m
}

fn directive_mut(certificate: &mut ProofCertificate) -> &mut CleanCicKernelRecheck {
    let ProofEvidence::CleanCic {
        kernel_recheck: Some(recheck),
        ..
    } = &mut certificate.evidence
    else {
        panic!("fixture certificate carries a directive");
    };
    recheck
}

fn binding_mut(certificate: &mut ProofCertificate) -> &mut CertificateBinding {
    directive_mut(certificate)
        .binding
        .as_deref_mut()
        .expect("fixture certificate is bound")
}

/// Re-key a certificate's v8 lineage after an edit, so a test measures the
/// rule it names and not the lineage floor.
fn rekey_v8(m: &mut Module, obligation: u32) {
    let index = m
        .proof_certificates
        .iter()
        .position(|c| c.obligation == ProofId::new(obligation))
        .expect("certificate exists");
    let row = m
        .proof_obligations
        .iter()
        .find(|o| o.id == ProofId::new(obligation))
        .cloned()
        .expect("obligation exists");
    let lineage = {
        let resolve = module_symbol_resolver(m);
        let binding = m.proof_certificates[index]
            .evidence
            .clean_cic_kernel_recheck()
            .and_then(|r| r.binding.as_deref());
        clean_cic_lineage_digest_v8(&row, &resolve, binding).expect("keyable")
    };
    let ProofEvidence::CleanCic { lineage: slot, .. } = &mut m.proof_certificates[index].evidence
    else {
        unreachable!()
    };
    *slot = lineage;
}

fn certificate_of(m: &mut Module, obligation: u32) -> &mut ProofCertificate {
    m.proof_certificates
        .iter_mut()
        .find(|c| c.obligation == ProofId::new(obligation))
        .expect("certificate exists")
}

fn layers(m: &Module) -> Vec<(&'static str, Vec<ValidationError>)> {
    vec![
        ("validate_module", validate_module(m)),
        (
            "validate_module_report",
            validate_module_report(m).errors().to_vec(),
        ),
        (
            "validate_module_with_authority",
            validate_module_with_authority(m, &RejectingModuleProofAuthority),
        ),
        (
            "validate_module_for_codegen",
            validate_module_for_codegen(m),
        ),
    ]
}

fn strictest() -> ValidationConfig<'static> {
    ValidationConfig::pinned()
        .with_bound_certificates(true)
        .with_source_bound_certificates(true)
}

/// `Some(reason)` iff `errors` is EXACTLY ONE kernel-recheck refusal for
/// `obligation`.
fn sole_refusal(errors: &[ValidationError], obligation: u32) -> Option<&str> {
    match errors {
        [
            ValidationError::CertifiedCleanCicKernelRecheckFailed {
                obligation: got,
                reason,
            },
        ] if *got == obligation => Some(reason.as_str()),
        _ => None,
    }
}

fn assert_sole_refusal(m: &Module, obligation: u32, needle: &str) {
    let errors = validate_module(m);
    let reason = sole_refusal(&errors, obligation)
        .unwrap_or_else(|| panic!("expected ONE refusal of #{obligation}: {errors:?}"));
    assert!(
        reason.contains(needle),
        "refusal of #{obligation} must name `{needle}`: {reason}"
    );
}

// ===========================================================================
// the positive
// ===========================================================================

/// Lib.lean's `fst3_eq`, shipped with its island closure, is a `Certified`
/// `lean.theorem` row on every layer and under the strictest policy; the
/// kernel re-check witness a spec `CleanTheorem` binding resolves against now
/// contains it.
#[test]
fn fst3_eq_shipped_with_its_island_certifies_on_every_layer() {
    let m = honest();
    for (layer, errors) in layers(&m) {
        assert!(
            errors.is_empty(),
            "honest island module on {layer}: {errors:?}"
        );
    }
    let strict = validate_module_with_config(&m, &strictest()).into_errors();
    assert!(strict.is_empty(), "strictest policy: {strict:?}");
    let replayed = validate_module_report(&m)
        .replayed_certificate_refs()
        .map(|refs| refs.len());
    assert_eq!(replayed, Some(4), "all four rows are kernel-tier");
    let witness = kernel_certified_theorems(&m).expect("valid module");
    assert!(witness.contains("Lib.fst3_eq") && witness.contains("Lib.addmul_6_7"));
    // The emitted `addmul(6, 7)` really is 48: the theorem is about the code.
    let run = trust_ir::interpret::Interpreter::with_module(&m)
        .execute_func(
            m.functions[ADDMUL].id,
            vec![
                trust_ir::interpret::InterpretValue::int(Ty::U64, 6).unwrap(),
                trust_ir::interpret::InterpretValue::int(Ty::U64, 7).unwrap(),
            ],
        )
        .expect("addmul runs");
    assert_eq!(run.returns[0].as_int().unwrap().as_unsigned(), 48);
}

// ===========================================================================
// negative twins — each ONE mutation of the honest module, refused by name
// ===========================================================================

/// One declaration body in the theorem certificate's island is mutated (the
/// proof of `Lib.fst3_eq` proves `b`, not `a`): the Clean kernel refuses it
/// on insertion. The digest is recomputed and the lineage re-keyed, so the
/// ONLY thing wrong is the declaration.
#[test]
fn a_mutated_island_declaration_is_refused_by_the_kernel_on_insertion() {
    let mut m = honest();
    let wrong_proof = theorem(
        "Lib.fst3_eq",
        match fst3_eq() {
            Declaration::Theorem { type_, .. } => type_,
            _ => unreachable!(),
        },
        lam_nat(3, refl_nat(Expr::bvar(1))),
    );
    let mutated = island_of(&[
        fst3_def(),
        wrong_proof,
        definition("Lib.addmul", 2, addmul_source()),
        addmul_6_7(),
    ]);
    binding_mut(certificate_of(&mut m, 2)).environment = Some(mutated);
    rekey_v8(&mut m, 2);
    assert_sole_refusal(
        &m,
        2,
        "the Clean kernel REFUSED island declaration Lib.fst3_eq",
    );
}

/// The row's formula states something else (`= … b`) than the theorem
/// proves (`= … a`): definitional-equality refusal. The lineage is re-keyed
/// over the new formula so the defeq rule, not the lineage floor, refuses.
#[test]
fn a_theorem_that_does_not_state_the_formula_is_refused_by_defeq() {
    let mut m = honest();
    m.proof_obligations[2].formula = Some(ProofFormula::smtlib2(
        "(forall ((a (_ BitVec 64)) (b (_ BitVec 64)) (c (_ BitVec 64))) (= (Lib.fst3 a b c) b))",
        "Bool",
    ));
    rekey_v8(&mut m, 2);
    assert_sole_refusal(
        &m,
        2,
        "does not state the obligation's formula: its type is not definitionally equal",
    );
}

/// The island digest no longer names the bytes.
#[test]
fn an_island_digest_mismatch_is_refused() {
    let mut m = honest();
    binding_mut(certificate_of(&mut m, 2))
        .environment
        .as_mut()
        .expect("island")
        .digest
        .bytes[0] ^= 1;
    rekey_v8(&mut m, 2);
    assert_sole_refusal(&m, 2, "island digest mismatch");
}

/// An axiom in the closure is refused before the kernel sees it — even one
/// the theorem does not use (the island may add no assumption at all).
#[test]
fn an_undeclared_axiom_in_the_island_is_refused() {
    let mut m = honest();
    let with_axiom = island_of(&[
        Declaration::Axiom {
            name: Name::from_string("Lib.cheat"),
            level_params: vec![],
            type_: Expr::prop(),
        },
        fst3_def(),
        fst3_eq(),
        definition("Lib.addmul", 2, addmul_source()),
        addmul_6_7(),
    ]);
    binding_mut(certificate_of(&mut m, 2)).environment = Some(with_axiom);
    rekey_v8(&mut m, 2);
    assert_sole_refusal(&m, 2, "island declares axiom Lib.cheat");
}

/// A declaration may not shadow a constant the anchor environment already
/// has (`Nat.add`), nor one earlier in the island.
#[test]
fn a_closure_that_redeclares_a_bound_name_is_refused() {
    for (redeclared, needle) in [
        (
            definition("Nat.add", 2, lam_nat(2, Expr::bvar(1))),
            "island redeclares Nat.add",
        ),
        (
            definition("Lib.fst3", 3, lam_nat(3, Expr::bvar(0))),
            "island redeclares Lib.fst3",
        ),
    ] {
        let mut m = honest();
        let shadowing = island_of(&[
            fst3_def(),
            redeclared,
            fst3_eq(),
            definition("Lib.addmul", 2, addmul_source()),
            addmul_6_7(),
        ]);
        binding_mut(certificate_of(&mut m, 2)).environment = Some(shadowing);
        rekey_v8(&mut m, 2);
        assert_sole_refusal(&m, 2, needle);
    }
}

/// Review (WS1.13): the remaining `install` refusals, each by its own name —
/// an EMPTY island (nothing to install, so nothing to be checked in), an
/// `Opaque` declaration (slice 1 admits definitions and theorems only),
/// bytes that do not decode, and a canonical carrier with one trailing byte
/// (the decoder is whole-slice). The digest is recomputed over each carrier,
/// so the digest check is not what refuses.
#[test]
fn an_island_that_is_empty_opaque_or_undecodable_is_refused_by_name() {
    let mut suffixed = encode_island_declarations_v1(&[
        fst3_def(),
        fst3_eq(),
        definition("Lib.addmul", 2, addmul_source()),
        addmul_6_7(),
    ])
    .expect("island encodes");
    suffixed.push(0);
    let cases: [(IslandEnvironment, &str); 4] = [
        (island_of(&[]), "island declares nothing"),
        (
            island_of(&[
                Declaration::Opaque {
                    name: Name::from_string("Lib.hidden"),
                    level_params: vec![],
                    type_: nat(),
                    value: Expr::nat_lit(0),
                },
                fst3_def(),
                fst3_eq(),
                definition("Lib.addmul", 2, addmul_source()),
                addmul_6_7(),
            ]),
            "island declares opaque constant Lib.hidden",
        ),
        (
            IslandEnvironment::new(vec![0xff; 7]),
            "island declarations do not decode",
        ),
        (
            IslandEnvironment::new(suffixed),
            "island declarations do not decode",
        ),
    ];
    for (bad, needle) in cases {
        let mut m = honest();
        binding_mut(certificate_of(&mut m, 2)).environment = Some(bad);
        rekey_v8(&mut m, 2);
        assert_sole_refusal(&m, 2, needle);
    }
}

/// Review (WS1.13): the SHAPE of an island-bound TV certificate's source
/// reference, each refused by its own name — no `source` at all (an island
/// with nothing to bind the comparand to), a `source.decl` the island does not
/// declare (`Nat.add`, a prelude constant: the comparand must be the value of
/// an ISLAND declaration), and one naming an island THEOREM
/// (`Lib.fst3_eq`: the comparand is bound only to a monomorphic
/// `Definition`).
#[test]
fn an_island_bound_tv_source_must_name_an_island_definition() {
    type Edit = fn(&mut CertificateBinding);
    let cases: [(Edit, &str); 3] = [
        (
            |b| b.source = None,
            "an island-bound TV certificate must name the island declaration its comparand is",
        ),
        (
            |b| b.source.as_mut().expect("source").decl = "Nat.add".to_string(),
            "the certificate's source declaration `Nat.add` is not declared by its island",
        ),
        (
            |b| b.source.as_mut().expect("source").decl = "Lib.fst3_eq".to_string(),
            "the comparand is bound only to a monomorphic Definition",
        ),
    ];
    for (edit, needle) in cases {
        let mut m = base_module();
        let id = push_island_tv(&mut m, FST3, &island(), "Lib.fst3");
        edit(binding_mut(certificate_of(&mut m, id)));
        rekey_v8(&mut m, id);
        assert_sole_refusal(&m, id, needle);
    }
}

/// Step 7 for the one name the TV re-check declares AFTER the island — the
/// certificate's own equation theorem `CleanTV.<fn>.denotes`: an island that
/// takes it is refused by name, by the minter and by the validator, rather
/// than left to whatever the kernel does on a duplicate declaration. (Review:
/// the island now may declare nothing under the validator-owned `CleanTV`
/// root at all, so the refusal names that namespace.)
#[test]
fn an_island_that_takes_the_tv_theorem_name_is_refused() {
    let clashing = island_of(&[
        fst3_def(),
        Declaration::Definition {
            name: Name::from_string("CleanTV.fst3.denotes"),
            level_params: vec![],
            type_: nat(),
            value: Expr::nat_lit(0),
            is_reducible: true,
        },
    ]);
    let m = base_module();
    let error = certify_identity_lineage_rung_island_bound(
        &m,
        ProofLineageId::new(0),
        ProofId::new(0),
        transform(),
        m.functions[FST3].id,
        &clashing,
        source("Lib.fst3"),
    )
    .expect_err("the minter refuses the clash");
    assert!(
        error.contains("island declares CleanTV.fst3.denotes in the validator-owned `CleanTV`"),
        "{error}"
    );
    // Hand-built: the honest certificate's island swapped for the clashing one.
    let mut m = base_module();
    let id = push_island_tv(&mut m, FST3, &island(), "Lib.fst3");
    binding_mut(certificate_of(&mut m, id)).environment = Some(clashing);
    rekey_v8(&mut m, id);
    assert_sole_refusal(
        &m,
        id,
        "island declares CleanTV.fst3.denotes in the validator-owned `CleanTV`",
    );
}

/// Review (WS1.13): the kernel witness `kernel_certified_theorems` — what a
/// spec `ProofKind::CleanTheorem` binding resolves against — is keyed by
/// theorem NAME, and an island names its own declarations. So an island
/// theorem may not take a name under a validator-owned root: not the TV
/// equation of a function that HAS a TV certificate (`CleanTV.fst3.denotes`),
/// not that of a function with NONE (`CleanTV.ghost.denotes` — the witness
/// would claim a translation validation that never ran), and not a fixed law
/// library's (`NNVerify.farkas_combine_2_le_bound`, the example `ProofKind`
/// itself names). Each is the honest `Lib.fst3_eq` row renamed — same
/// statement, same proof — refused by the minter and, hand-built, by the
/// validator, before its binding is compared.
#[test]
fn an_island_theorem_may_not_take_a_validator_owned_theorem_name() {
    for forged in [
        "CleanTV.fst3.denotes",
        "CleanTV.ghost.denotes",
        "NNVerify.farkas_combine_2_le_bound",
    ] {
        let (type_, value) = match fst3_eq() {
            Declaration::Theorem { type_, value, .. } => (type_, value),
            _ => unreachable!(),
        };
        let renamed = island_of(&[
            fst3_def(),
            theorem(forged, type_, value),
            definition("Lib.addmul", 2, addmul_source()),
            addmul_6_7(),
        ]);
        let root = forged.split('.').next().expect("qualified");
        let needle = format!("island declares {forged} in the validator-owned `{root}` namespace");
        let error = certify_island_theorem(
            ProofId::new(0),
            forged,
            ProofFormula::smtlib2(FST3_EQ, "Bool"),
            &renamed,
        )
        .expect_err("the minter refuses a validator-owned theorem name");
        assert!(error.contains(&needle), "{forged}: {error}");

        // Hand-built from the honest module: row #2's theorem renamed, the
        // island carrying the renamed theorem, the lineage re-keyed.
        let mut m = honest();
        m.proof_obligations[2].kind = ObligationKind::Custom {
            namespace: "lean.theorem".to_string(),
            name: forged.to_string(),
        };
        {
            let certificate = certificate_of(&mut m, 2);
            let ProofEvidence::CleanCic { term, .. } = &mut certificate.evidence else {
                unreachable!()
            };
            *term = trust_ir::proof::encode_clean_expr_v1(&Expr::const_(
                Name::from_string(forged),
                vec![],
            ))
            .expect("reference encodes");
            directive_mut(certificate).theorems = vec![forged.to_string()];
            binding_mut(certificate).environment = Some(renamed);
        }
        rekey_v8(&mut m, 2);
        assert_sole_refusal(&m, 2, &needle);
        assert!(
            kernel_certified_theorems(&m).is_err(),
            "{forged}: no witness is minted for a module carrying the forgery"
        );
    }
    // Control: the SAME island theorem under its own name certifies.
    let witness = kernel_certified_theorems(&honest()).expect("honest module");
    assert!(witness.contains("Lib.fst3_eq"));
}

/// Review (WS1.13): ONE NAME, ONE THEOREM. The kernel witness is keyed by
/// theorem name and every island names its own declarations, so a second
/// `lean.theorem` row may not certify an already-certified name as a
/// different theorem — neither from ANOTHER island (`Lib.fst3_eq : 1 = 1`, a
/// closed statement citing nothing, so no bridge stands in its way) nor in the
/// SAME island under another grounded statement (`Lib.addmul_6_7` stated as
/// `(= 48 48)`, which its type `Lib.addmul 6 7 = 48` is definitionally equal
/// to). The later row is refused by name; the same theorem restated with
/// other binder names (the same grounded statement) stays admitted.
#[test]
fn one_lean_theorem_name_denotes_one_theorem() {
    // Another island, same name.
    let mut m = honest();
    let other = island_of(&[theorem(
        "Lib.fst3_eq",
        eq_nat(Expr::nat_lit(1), Expr::nat_lit(1)),
        refl_nat(Expr::nat_lit(1)),
    )]);
    let id = push_theorem(&mut m, "Lib.fst3_eq", "(= 1 1)", &other);
    assert_sole_refusal(
        &m,
        id,
        "lean.theorem `Lib.fst3_eq` is already certified by obligation 2 as a DIFFERENT theorem \
         (another island)",
    );
    // Same island, another grounded statement of the same theorem.
    let mut m = honest();
    let id = push_theorem(&mut m, "Lib.addmul_6_7", "(= 48 48)", &island());
    assert_sole_refusal(
        &m,
        id,
        "lean.theorem `Lib.addmul_6_7` is already certified by obligation 3 as a DIFFERENT \
         theorem (the same island, another grounded statement)",
    );
    // Control: the SAME theorem, restated with other binder names (the same
    // grounded statement, the same island), is one claim — admitted.
    let mut m = honest();
    push_theorem(
        &mut m,
        "Lib.fst3_eq",
        "(forall ((x (_ BitVec 64)) (y (_ BitVec 64)) (z (_ BitVec 64))) (= (Lib.fst3 x y z) x))",
        &island(),
    );
    let errors = validate_module(&m);
    assert!(errors.is_empty(), "{errors:?}");
}

/// Review (WS1.13): the grounder's theory-spelling rule reaches the anchor —
/// an island constant spelled like an SMT-LIB theory function symbol outside
/// Core/Ints/BV/Arrays (`ubv_to_int`, FloatingPoint's `fp.abs`, Strings'
/// `str.len`) is refused by name, so a `lean.theorem` row never reads, as
/// SMT-LIB, as a claim about a theory operator.
#[test]
fn an_island_constant_spelled_like_a_theory_operator_is_not_citable() {
    for spelled in ["ubv_to_int", "fp.abs", "str.len"] {
        let applied = Expr::app(Expr::const_str(spelled), Expr::nat_lit(5));
        let island = island_of(&[
            definition(spelled, 1, lam_nat(1, Expr::bvar(0))),
            theorem(
                "Lib.spelled_5",
                eq_nat(applied, Expr::nat_lit(5)),
                refl_nat(Expr::nat_lit(5)),
            ),
        ]);
        let error = certify_island_theorem(
            ProofId::new(0),
            "Lib.spelled_5",
            ProofFormula::smtlib2(format!("(= ({spelled} 5) 5)"), "Bool"),
            &island,
        )
        .expect_err("a theory spelling is not citable");
        assert!(
            error.contains(&format!(
                "`{spelled}` is not a citable island-constant spelling"
            )),
            "{spelled}: {error}"
        );
    }
}

/// F-008: the TV comparand must be the island declaration's VALUE. The
/// miscompiled `addmul` (`a+b+a`) is certified by a certificate re-minted
/// over its own (wrong) comparand — accepted before WS1.13 — and the island
/// it carries is the honest one: refused, because the comparand is not the
/// value of `Lib.addmul` there.
#[test]
fn a_tv_comparand_that_is_not_the_named_declarations_value_is_refused() {
    let honest_island = island();
    let mut m = base_module();
    // Miscompile, then mint over the miscompiled body with an island whose
    // `Lib.addmul` IS that body — the minter's own source check passes.
    for node in &mut m.functions[ADDMUL].blocks[0].body {
        if let Inst::BinOp { op, .. } = &mut node.inst
            && *op == trust_ir::inst::BinOp::Mul
        {
            *op = trust_ir::inst::BinOp::Add;
        }
    }
    let miscompiled_source = lam_nat(
        2,
        wmod64(app2(
            "Nat.add",
            wmod64(app2("Nat.add", Expr::bvar(1), Expr::bvar(0))),
            Expr::bvar(1),
        )),
    );
    let forged_island = island_of(&[
        fst3_def(),
        fst3_eq(),
        definition("Lib.addmul", 2, miscompiled_source),
    ]);
    let id = push_island_tv(&mut m, ADDMUL, &forged_island, "Lib.addmul");
    assert!(
        validate_module(&m).is_empty(),
        "control: a self-consistent island is ITS OWN source — the certificate proves the code \
         equals that island's Lib.addmul, which is what a theorem bridged to it would be about"
    );
    // The ONE mutation: the certificate's island is the honest source. The
    // environment digest is the honest island's (taken from an honest mint),
    // and the lineage is re-keyed.
    let honest_environment_digest = {
        let mut h = base_module();
        push_island_tv(&mut h, FST3, &honest_island, "Lib.fst3");
        binding_mut(&mut h.proof_certificates[0]).environment_digest
    };
    {
        let binding = binding_mut(certificate_of(&mut m, id));
        binding.environment = Some(honest_island);
        binding.environment_digest = honest_environment_digest;
    }
    rekey_v8(&mut m, id);
    assert_sole_refusal(
        &m,
        id,
        "the TV comparand is not the value of island declaration `Lib.addmul`",
    );
}

/// Step 6: the theorem cites `@Lib.fst3`, whose TV certificate carries NO
/// island (bound, but island-free): the theorem says nothing about `fst3`'s
/// code, so it is refused by the roadmap's message.
#[test]
fn a_theorem_citing_a_constant_whose_tv_certificate_carries_no_island_is_refused() {
    let island = island();
    let mut m = base_module();
    push_bound_tv(&mut m, FST3);
    push_island_tv(&mut m, ADDMUL, &island, "Lib.addmul");
    let id = push_theorem(&mut m, "Lib.fst3_eq", FST3_EQ, &island);
    assert_sole_refusal(
        &m,
        id,
        "theorem cites @Lib.fst3, whose TV certificate is not bound to island declaration \
         Lib.fst3 in this environment",
    );
}

/// Step 6: the TV certificate of `fst3` is island-bound — to ANOTHER island
/// (one extra definition, so another digest).
#[test]
fn a_theorem_citing_a_constant_bound_in_another_island_is_refused() {
    let island = island();
    let other = island_of(&[
        fst3_def(),
        definition("Lib.extra", 1, lam_nat(1, Expr::bvar(0))),
    ]);
    let mut m = base_module();
    push_island_tv(&mut m, FST3, &other, "Lib.fst3");
    push_island_tv(&mut m, ADDMUL, &island, "Lib.addmul");
    let id = push_theorem(&mut m, "Lib.fst3_eq", FST3_EQ, &island);
    assert_sole_refusal(
        &m,
        id,
        "theorem cites @Lib.fst3, whose TV certificate is not bound to island declaration \
         Lib.fst3 in this environment",
    );
}

/// Step 6, the name half: `fst3`'s TV certificate is bound to the right
/// island but names ANOTHER declaration as its source (here the comparand
/// check itself refuses: `fst3`'s code is not `Lib.addmul`'s value).
#[test]
fn a_tv_certificate_naming_another_source_is_refused() {
    let island = island();
    let mut m = base_module();
    let id = push_island_tv(&mut m, FST3, &island, "Lib.fst3");
    binding_mut(certificate_of(&mut m, id))
        .source
        .as_mut()
        .expect("source")
        .decl = "Lib.addmul".to_string();
    rekey_v8(&mut m, id);
    let errors = validate_module(&m);
    let reason = sole_refusal(&errors, id).unwrap_or_else(|| panic!("{errors:?}"));
    assert!(
        reason.contains("does not have the type of island declaration `Lib.addmul`")
            || reason.contains("is not the value of island declaration `Lib.addmul`"),
        "{reason}"
    );
}

// ===========================================================================
// mutation controls — the rule, not something else, refused; legal
// neighbours stay admitted
// ===========================================================================

/// The honest carrier: the SAME row at `Pending`, with its proof as a
/// `LeanProof` text, validates — and without the pinned namespace it would
/// not (`lean4.theorem`, the parta-lean twin, is refused by name).
#[test]
fn the_same_row_pending_with_lean_proof_still_validates() {
    let mut m = base_module();
    let row = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Custom {
            namespace: "lean.theorem".to_string(),
            name: "Lib.fst3_eq".to_string(),
        },
        ProofStatus::Pending,
        "Lean theorem Lib.fst3_eq",
    )
    .with_formula(ProofFormula::smtlib2(FST3_EQ, "Bool"));
    m.proof_obligations.push(row.clone());
    m.proof_certificates.push(ProofCertificate {
        obligation: ProofId::new(0),
        prover: "clean-kernel".to_string(),
        evidence: ProofEvidence::LeanProof("fun a b c => rfl".to_string()),
        assurance: None,
    });
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    let mut unpinned = m.clone();
    unpinned.proof_obligations[0].kind = ObligationKind::Custom {
        namespace: "lean4.theorem".to_string(),
        name: "Lib.fst3_eq".to_string(),
    };
    assert!(matches!(
        validate_module(&unpinned).as_slice(),
        [ValidationError::UnpinnedCustomObligationNamespace { .. }]
    ));
    // Certified WITHOUT a certificate is still refused (the tier is earned).
    let mut bare = m;
    bare.proof_obligations[0].status = ProofStatus::Certified;
    assert!(matches!(
        validate_module(&bare).as_slice(),
        [ValidationError::CertifiedWithoutCleanCic { obligation: 0 }]
    ));
}

#[test]
fn the_lean_theorem_namespace_is_byte_exact() {
    assert!(is_admitted_obligation_namespace("lean.theorem"));
    for forged in [
        "lean4.theorem",
        "lean.theorems",
        "LEAN.THEOREM",
        "clean.theorem",
        "lean.theorem.",
        "lean",
    ] {
        assert!(!is_admitted_obligation_namespace(forged), "{forged}");
    }
}

/// An island-free `clean_backend_tv` certificate keeps its MINT-TIME meaning
/// on the default lanes, and is refused under the source-bound knob by the
/// field it lacks; the island-bound honest module passes that knob.
#[test]
fn an_island_free_tv_certificate_keeps_its_mint_time_meaning() {
    let mut m = base_module();
    push_bound_tv(&mut m, FST3);
    assert!(validate_module(&m).is_empty());
    let strict = ValidationConfig::pinned().with_source_bound_certificates(true);
    let errors = validate_module_with_config(&m, &strict).into_errors();
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::CertificateBindingMismatch { obligation: 0, field, .. }]
                if field == "environment"
        ),
        "{errors:?}"
    );
    assert!(
        validate_module_with_config(&honest(), &strict)
            .into_errors()
            .is_empty()
    );
}

/// Anchor↔kind, both directions: a `lean.theorem` row cannot borrow the TV
/// anchor, the contract anchor, or a directive-less certificate; a
/// `Postcondition` cannot cite the island anchor (a contract clause over IR
/// places is slice 2).
#[test]
fn the_island_anchor_and_the_lean_theorem_kind_only_meet_each_other() {
    let honest = honest();
    for (anchor, module) in [
        (KERNEL_ANCHOR_CLEAN_BACKEND_TV, "CleanCompiler.BackendTV"),
        (
            trust_ir::proof::KERNEL_ANCHOR_TRUST_IR_CONTRACT,
            trust_ir::proof::KERNEL_ANCHOR_TRUST_IR_CONTRACT_MODULE,
        ),
    ] {
        let mut m = honest.clone();
        let directive = directive_mut(certificate_of(&mut m, 2));
        directive.anchor = anchor.to_string();
        directive.module = module.to_string();
        rekey_v8(&mut m, 2);
        assert_sole_refusal(
            &m,
            2,
            "may be Certified only through the 'clean_island' anchor",
        );
    }
    let mut m = honest.clone();
    {
        let ProofEvidence::CleanCic { kernel_recheck, .. } =
            &mut certificate_of(&mut m, 2).evidence
        else {
            unreachable!()
        };
        *kernel_recheck = None;
    }
    rekey_v8(&mut m, 2);
    assert_sole_refusal(
        &m,
        2,
        "a directive-less certificate establishes no user theorem",
    );

    let mut m = honest;
    m.proof_obligations[2].kind = ObligationKind::Postcondition;
    rekey_v8(&mut m, 2);
    assert_sole_refusal(&m, 2, "may certify only `lean.theorem` obligations");
}

/// The directive is exact: the island theorem certificate cites exactly the
/// row's theorem, admits no axiom, carries its island, names no source, and
/// its `term` is the reference to the theorem and `context` is empty.
#[test]
fn the_island_directive_is_exact() {
    type Edit = fn(&mut ProofCertificate);
    let cases: [(Edit, &str); 6] = [
        (
            |c| directive_mut(c).theorems = vec!["Lib.addmul_6_7".to_string()],
            "must cite exactly the row's theorem",
        ),
        (
            |c| directive_mut(c).allowed_axioms = vec!["Lib.cheat".to_string()],
            "admits no axiom",
        ),
        (
            |c| binding_mut(c).environment = None,
            "requires CertificateBinding.environment",
        ),
        (
            |c| binding_mut(c).source = Some(source("Lib.fst3")),
            "names no source declaration",
        ),
        (
            |c| {
                let ProofEvidence::CleanCic { term, .. } = &mut c.evidence else {
                    unreachable!()
                };
                *term = trust_ir::proof::encode_clean_expr_v1(&Expr::const_str("Lib.addmul_6_7"))
                    .unwrap();
            },
            "must be the constant `Lib.fst3_eq`",
        ),
        (
            |c| {
                let ProofEvidence::CleanCic { context, .. } = &mut c.evidence else {
                    unreachable!()
                };
                *context = vec![1];
            },
            "`context` must be empty",
        ),
    ];
    for (edit, needle) in cases {
        let mut m = honest();
        edit(certificate_of(&mut m, 2));
        rekey_v8(&mut m, 2);
        assert_sole_refusal(&m, 2, needle);
    }
}

/// A present binding is still compared field by field on the island anchor:
/// the statement digest of another statement is refused by name.
#[test]
fn the_island_binding_is_compared_field_by_field() {
    let mut m = honest();
    binding_mut(certificate_of(&mut m, 2))
        .statement_digest
        .bytes[0] ^= 1;
    rekey_v8(&mut m, 2);
    let errors = validate_module(&m);
    assert!(
        matches!(
            errors.as_slice(),
            [ValidationError::CertificateBindingMismatch { obligation: 2, field, .. }]
                if field == "statement_digest"
        ),
        "{errors:?}"
    );
}

/// The contract anchor installs no island, so a carried one is refused
/// rather than silently ignored.
#[test]
fn an_island_on_the_contract_anchor_is_refused() {
    use trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate_bound_in;
    let mut m = base_module();
    let obligation = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "literal contract",
    )
    .with_formula(ProofFormula::smtlib2("(= 1 1)", "Bool"));
    let mut certificate = contract_clean_cic_certificate_bound_in(&m, &obligation, "contract")
        .expect("a literal contract mints");
    m.proof_obligations.push(obligation);
    binding_mut(&mut certificate).environment = Some(island());
    m.proof_certificates.push(certificate);
    rekey_v8(&mut m, 0);
    let errors = validate_module(&m);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::CertificateBindingMismatch { obligation: 0, field, .. }
                if field == "environment"
        )),
        "{errors:?}"
    );
}

/// Slice 2 residual, pinned: an island-bound TV certificate over a CALLER is
/// refused by the minter and — hand-built — by the validator, by name.
#[test]
fn an_island_bound_caller_is_the_disclosed_slice_two_residual() {
    let mut mb = ModuleBuilder::new("island_caller");
    mb.set_default_producer(Producer::Clean);
    let ternary = mb.add_func_type(vec![Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]);
    let fst3 = {
        let mut f = mb.function("fst3", ternary);
        let e = f.create_block();
        let a = f.add_block_param(e, Ty::U64);
        let _ = f.add_block_param(e, Ty::U64);
        let _ = f.add_block_param(e, Ty::U64);
        f.switch_to_block(e);
        f.ret(vec![a]);
        f.build()
    };
    let mut f = mb.function("twice", ternary);
    let e = f.create_block();
    let a = f.add_block_param(e, Ty::U64);
    let b = f.add_block_param(e, Ty::U64);
    let c = f.add_block_param(e, Ty::U64);
    f.switch_to_block(e);
    let r = f.call(fst3, vec![a, b, c]);
    f.ret(vec![r]);
    let twice: FuncId = f.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let error = certify_identity_lineage_rung_island_bound(
        &m,
        ProofLineageId::new(0),
        ProofId::new(0),
        transform(),
        twice,
        &island(),
        source("Lib.fst3"),
    )
    .expect_err("slice 1 binds no caller to an island");
    assert!(error.contains("slice 2"), "{error}");
    // Hand-built: a bound certificate for `twice` given an island.
    let (_, obligation, mut certificate) = certify_identity_lineage_rung_bound(
        &m,
        ProofLineageId::new(0),
        ProofId::new(0),
        transform(),
        twice,
    )
    .expect("twice is in the Fragment-3b fragment");
    {
        let binding = binding_mut(&mut certificate);
        binding.environment = Some(island());
        binding.source = Some(source("Lib.fst3"));
    }
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(certificate);
    rekey_v8(&mut m, 0);
    assert_sole_refusal(&m, 0, "is not in slice 1");
}

#[cfg(feature = "serde")]
#[test]
fn an_island_bound_module_survives_json_and_messagepack_and_still_validates() {
    let m = honest();
    let json = serde_json::to_string(&m).expect("serializes");
    let back: Module = serde_json::from_str(&json).expect("deserializes");
    assert_eq!(back, m, "JSON is lossless for an island");
    assert!(validate_module(&back).is_empty());
    let msgpack = rmp_serde::to_vec(&m).expect("msgpack");
    let back: Module = rmp_serde::from_slice(&msgpack).expect("msgpack back");
    assert_eq!(back, m, "MessagePack is lossless for an island");
    assert!(validate_module(&back).is_empty());
}

/// The F-014 half WS1.13 supplies: a spec `ProofKind::CleanTheorem` binding
/// (v46) resolves against the kernel witness `kernel_certified_theorems`
/// mints, which now contains island theorems — and a name the island does
/// not certify stays unresolved.
#[test]
fn a_spec_clean_theorem_binding_resolves_against_an_island_theorem() {
    use trust_ir::{
        ProofKind, SpecInvariant, SpecLinkOptions, SpecLinkViolation, SpecModule, SpecProof,
        SpecVar, SpecWaiver, link_spec_modules_with_theorems,
    };
    let bind = |name: &str| {
        let mut m = honest();
        let mut ring = SpecModule::linked("ring");
        ring.vars = vec![SpecVar::new("seq", "Int")];
        ring.actions = vec!["Push".to_string()];
        ring.invariants = vec![SpecInvariant::new("BoundedSeq", "(<= seq 7)")];
        ring.waivers = vec![SpecWaiver {
            machine: "ring".to_string(),
            action: "Push".to_string(),
            reason: "island probe".to_string(),
        }];
        ring.proofs = vec![SpecProof {
            machine: "ring".to_string(),
            action: "Push".to_string(),
            proof_name: "ring_push_refines".to_string(),
            kind: ProofKind::CleanTheorem {
                name: name.to_string(),
            },
        }];
        m.spec_modules.push(ring);
        m
    };
    let m = bind("Lib.fst3_eq");
    let witness = kernel_certified_theorems(&m).expect("valid module");
    let report =
        link_spec_modules_with_theorems(&m, None, Some(&witness), SpecLinkOptions::default())
            .expect("links");
    assert!(report.is_certifying(), "{report:?}");
    let other = bind("Lib.snd32_eq");
    let witness = kernel_certified_theorems(&other).expect("valid module");
    let report =
        link_spec_modules_with_theorems(&other, None, Some(&witness), SpecLinkOptions::default())
            .expect("links");
    assert!(
        matches!(
            report.violations.as_slice(),
            [SpecLinkViolation::CleanTheoremUnresolved { theorem, .. }] if theorem == "Lib.snd32_eq"
        ),
        "{:?}",
        report.violations
    );
}

/// §8 amendment, and the tripwire for the certificate-binding wire batch: the
/// island reaches the canonical binary LOSSLESSLY or not at all. Since binary
/// v61 (`CERTIFICATE_BINDING_FORMAT_VERSION`, roadmap WS6.7) the binding HAS a
/// carrier, so the writer must now ENCODE an island-bound certificate — a
/// refusal would be a regression, not the old safe state — and the carrier
/// must round-trip `environment` byte for byte: a codec that writes the other
/// binding fields and drops the island fails HERE, instead of shipping
/// modules whose `lean.theorem` rows silently stop certifying after one
/// binary round trip (the re-read certificate would be island-free, so its v8
/// lineage no longer binds). (Written first as "refuse OR round-trip", while
/// the binding had no carrier; tightened when the carrier landed.)
#[cfg(feature = "binary")]
#[test]
fn the_binary_writer_never_narrows_an_island_bound_certificate() {
    let m = honest();
    let islands = |module: &Module| {
        module
            .proof_certificates
            .iter()
            .map(|c| {
                c.evidence
                    .clean_cic_kernel_recheck()
                    .and_then(|r| r.binding.as_deref())
                    .and_then(|b| b.environment.clone())
            })
            .collect::<Vec<_>>()
    };
    assert!(
        islands(&m).iter().any(Option::is_some),
        "control: the fixture carries at least one island"
    );
    // The blob entry never panics (D1b); a bound certificate is encodable.
    let bytes = trust_ir::binary::serialize_module(&m).expect("a bound certificate is encodable");
    assert_eq!(
        &bytes[8..12],
        &trust_ir::binary::CERTIFICATE_BINDING_FORMAT_VERSION.to_le_bytes(),
        "a bound certificate selects the carrier's version"
    );
    let back = trust_ir::binary::deserialize_module(&bytes)
        .expect("a module the writer encoded reads back");
    assert_eq!(
        islands(&back),
        islands(&m),
        "the binary carrier of CertificateBinding must carry `environment` (WS1.13)"
    );
    assert_eq!(back.proof_certificates, m.proof_certificates);
    let errors = validate_module(&back);
    assert!(errors.is_empty(), "{errors:?}");
}

// ===========================================================================
// ported ratchet rows
// ===========================================================================

/// `LEAN.home.theorem_certified_tier` (parta-lean/run.py:378), FLIPPED: the
/// well-formed Pending theorem row's single change to `Certified` is no
/// longer refused for want of an anchor — with its island certificate it IS
/// the kernel tier. Without one it is still refused
/// (`CertifiedWithoutCleanCic`), so the tier is earned, not stamped.
#[test]
fn lean_home_theorem_certified_tier() {
    let island = island();
    let mut m = base_module();
    push_island_tv(&mut m, FST3, &island, "Lib.fst3");
    let id = push_theorem(&mut m, "Lib.fst3_eq", FST3_EQ, &island);
    assert!(validate_module(&m).is_empty(), "{:?}", validate_module(&m));
    assert_eq!(
        m.proof_obligations[id as usize].status,
        ProofStatus::Certified
    );
    m.proof_certificates
        .retain(|c| c.obligation != ProofId::new(id));
    assert!(matches!(
        validate_module(&m).as_slice(),
        [ValidationError::CertifiedWithoutCleanCic { .. }]
    ));
}

/// `LEAN.home.kernel_only_theorems.populated` (the FORMAT half; populating it
/// is the producer's, WS5/WS6): Lib.lean's kernel-only theorems have an
/// in-format home that is not decoration — every one shipped with the
/// island closure is a `Certified` row, and the module's kernel witness
/// lists exactly them.
#[test]
fn lean_home_kernel_only_theorems_populated() {
    let m = honest();
    assert!(validate_module(&m).is_empty());
    let rows: Vec<&str> = m
        .proof_obligations
        .iter()
        .filter_map(|o| match &o.kind {
            ObligationKind::Custom { namespace, name } if namespace == "lean.theorem" => {
                Some(name.as_str())
            }
            _ => None,
        })
        .collect();
    assert_eq!(rows, ["Lib.fst3_eq", "Lib.addmul_6_7"]);
    let witness = kernel_certified_theorems(&m).expect("valid");
    for name in rows {
        assert!(witness.contains(name), "{name} is kernel-established");
    }
    // The anchor constants a producer names.
    assert_eq!(KERNEL_ANCHOR_CLEAN_ISLAND, "clean_island");
    assert_eq!(KERNEL_ANCHOR_CLEAN_ISLAND_MODULE, "Clean.Island");
}
