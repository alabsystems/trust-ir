// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof-surface identity, the non-wire half (roadmap WS1.12a / WS1.12b;
//! findings F-007, F-005 residual, F-008 carrier, the F-020 decision).
//!
//! THE HOLES. A `CleanCicKernelRecheck` named the kernel environment only by
//! its closed `anchor` string, so a certificate could not say WHICH kernel
//! closure it was checked in (F-007); a `clean_backend_tv` certificate
//! recorded no callee list, so a CONSISTENT retarget — the call AND the
//! `InheritedFromCallee` row moved to another certified callee of the same
//! arity and name rank — passed the WS1.4 composition rule (F-005
//! residual); and the lineage digest folded in the raw `ProofId` / `FuncId`
//! indices, so a merge that renumbered either refused every honest
//! certificate (F-020).
//!
//! THE RULES.
//!
//! * `CleanCicKernelRecheck.binding: Option<Box<CertificateBinding>>`
//!   (`environment_digest`, `statement_digest`, `origin_module`, `source`,
//!   `callees`). `None` is UNBOUND, the pre-binding meaning, admitted by the
//!   default lanes and refused as `UnboundCertificate` under
//!   `ValidationConfig::with_bound_certificates(true)`. A PRESENT binding is
//!   recomputed field by field and any difference is
//!   `CertificateBindingMismatch { field, .. }`.
//! * The contract path gains the named anchor `trust_ir_contract`
//!   (`TrustIr.Contract`; no theorems, no axioms), so a contract certificate
//!   can carry a binding too; the directive-less arm keeps its meaning.
//! * Lineage v8 (`trust_ir.proof.clean_cic.lineage.v8`) is keyed on content
//!   and LINK SYMBOL (the v46 `spec` backref included) and accepted beside
//!   v5/v6/v7; `DuplicateObligationContent` keeps it one-to-one within a
//!   function, scoped to v8-matched `CleanCic` rows only.
//!
//! WIRE STATUS. Binary v61 (`CERTIFICATE_BINDING_FORMAT_VERSION`, reserved
//! 07fb5515, roadmap WS6.7(b)) carries the binding: a bound module is written
//! at v61, decodes bound, has a module identity, and is admitted by the
//! linked walk and every fallible binary entry point; an explicit v38
//! projection refuses it by name. Before v61 the writer refused a bound
//! module rather than narrow the binding to `None`; no path ever narrowed it.
//!
//! Tests whose name starts `b2_gap_` / `b3_gap_` / `lean_home_` are the
//! in-repo ports of the two-language proof program's ratchet rows of the same
//! id (dots spelled `_`); the conformance ratchet table holds the b2/b3 rows.
//!
//! FEATURES. Gate 9 (`scripts/gates/validator-fail-closed.trust-ir-build.tests`)
//! runs `test -p trust-ir-build` without additional features (the default
//! `clean-tv-anchor` remains enabled), where `trust_ir::binary` is
//! not compiled and `Module` derives no serde impls. Every transport
//! assertion below is therefore behind `#[cfg(feature = "serde")]` /
//! `#[cfg(feature = "binary")]` — this crate's forwarding features, which the
//! train's test invocation turns on through `-p trust-ir-cli`
//! (`trust-ir-build/serde`) and `-p trust-ir-conformance`
//! (`trust-ir-build/{serde,binary}`), so they run there and the file still
//! compiles in that default-feature gate. Its replay fixtures require
//! `clean-tv-anchor`; the validator rules themselves are feature-free.

use std::collections::BTreeSet;

use trust_ir::clean_expr_lowering::contract::{
    contract_clean_cic_certificate_bound_in, contract_clean_cic_certificate_in,
};
use trust_ir::inst::BinOp;
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::proof::{
    CertificateBinding, CleanCicKernelRecheck, KERNEL_ANCHOR_TRUST_IR_CONTRACT,
    KERNEL_ANCHOR_TRUST_IR_CONTRACT_MODULE, ObligationKind, ProofCertificate, ProofDigest,
    ProofEvidence, ProofFormula, ProofLineageId, ProofObligation, ProofStatus, ProofTransform,
    ProofTransformStage, RejectingModuleProofAuthority, SourceDefinitionRef, SpecObligationRef,
    clean_cic_lineage_content_v8, clean_cic_lineage_digest, clean_cic_lineage_digest_v8,
    module_symbol_resolver,
};
use trust_ir::ty::Ty;
use trust_ir::value::ProofId;
use trust_ir::{BodyGate, FuncId, Inst, Module, ModuleImport, Producer};
use trust_ir_build::{
    ModuleBuilder, ValidationConfig, ValidationError, certify_identity_lineage_rung,
    certify_identity_lineage_rung_bound, validate_module, validate_module_for_codegen,
    validate_module_report, validate_module_with_authority, validate_module_with_config,
};

const PLUS: usize = 0;
const MINUS: usize = 1;
const TOP: usize = 2;

// ===========================================================================
// fixtures — the WS1.4 `plus` / `minus` / `top` module
// ===========================================================================

/// `plus(a,b) = a*b + a`, `minus(a,b) = a*b - a`, `top(a,b) = plus(a,b) + 7`;
/// all U64, Clean producer, gated by the Clean kernel-TV authority.
fn base_module() -> Module {
    let mut mb = ModuleBuilder::new("certificate_binding");
    mb.set_default_producer(Producer::Clean);
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let leaf = |mb: &mut ModuleBuilder, name: &str, op: BinOp| {
        let mut f = mb.function(name, sig);
        let e = f.create_block();
        let a = f.add_block_param(e, Ty::U64);
        let b = f.add_block_param(e, Ty::U64);
        f.switch_to_block(e);
        let p = f.mul(Ty::U64, a, b);
        let r = f.binop(op, Ty::U64, p, a);
        f.ret(vec![r]);
        f.build()
    };
    let plus = leaf(&mut mb, "plus", BinOp::Add);
    let _minus = leaf(&mut mb, "minus", BinOp::Sub);
    let mut f = mb.function("top", sig);
    let e = f.create_block();
    let a = f.add_block_param(e, Ty::U64);
    let b = f.add_block_param(e, Ty::U64);
    f.switch_to_block(e);
    let c = f.call(plus, vec![a, b]);
    let k = f.iconst(Ty::U64, 7);
    let r = f.add(Ty::U64, c, k);
    f.ret(vec![r]);
    f.build();
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
    ProofTransform::new(
        ProofTransformStage::Frontend,
        "identity",
        "certificate-binding",
        "1.0.0",
    )
}

/// Certify `functions` in order with the BOUND public minter (obligation `i`
/// belongs to `functions[i]`).
fn certify_bound(m: &mut Module, functions: &[usize]) {
    for (i, &function) in functions.iter().enumerate() {
        let id = u32::try_from(i).expect("small fixture");
        let (_, obligation, certificate) = certify_identity_lineage_rung_bound(
            m,
            ProofLineageId::new(id),
            ProofId::new(id),
            transform(),
            m.functions[function].id,
        )
        .expect("fixture function is in the backend-TV fragment");
        m.proof_obligations.push(obligation);
        m.proof_certificates.push(certificate);
    }
}

/// The same with the legacy (UNBOUND, v6-lineage) minter.
fn certify_unbound(m: &mut Module, functions: &[usize]) {
    for (i, &function) in functions.iter().enumerate() {
        let id = u32::try_from(i).expect("small fixture");
        let (_, obligation, certificate) = certify_identity_lineage_rung(
            m,
            ProofLineageId::new(id),
            ProofId::new(id),
            transform(),
            m.functions[function].id,
        )
        .expect("fixture function is in the backend-TV fragment");
        m.proof_obligations.push(obligation);
        m.proof_certificates.push(certificate);
    }
}

fn inherit(caller_obligation: u32, callee: FuncId, callee_obligation: u32) -> ProofCertificate {
    ProofCertificate {
        obligation: ProofId::new(caller_obligation),
        prover: "clean-backend-tv-compose".to_string(),
        evidence: ProofEvidence::InheritedFromCallee {
            callee,
            obligation: ProofId::new(callee_obligation),
            external: None,
        },
        assurance: None,
    }
}

/// The honest BOUND A0 module: `plus` #0, `minus` #1, `top` #2 grounded at
/// `plus`'s obligation.
fn bound_a0() -> Module {
    let mut m = base_module();
    certify_bound(&mut m, &[PLUS, MINUS, TOP]);
    let plus = m.functions[PLUS].id;
    m.proof_certificates.push(inherit(2, plus, 0));
    m
}

/// The honest UNBOUND A0 module (the WS1.4 fixture, byte for byte).
fn unbound_a0() -> Module {
    let mut m = base_module();
    certify_unbound(&mut m, &[PLUS, MINUS, TOP]);
    let plus = m.functions[PLUS].id;
    m.proof_certificates.push(inherit(2, plus, 0));
    m
}

fn binding_mut(certificate: &mut ProofCertificate) -> &mut CertificateBinding {
    let ProofEvidence::CleanCic {
        kernel_recheck: Some(recheck),
        ..
    } = &mut certificate.evidence
    else {
        panic!("fixture certificate carries a directive");
    };
    recheck
        .binding
        .as_deref_mut()
        .expect("fixture certificate is bound")
}

fn binding(certificate: &ProofCertificate) -> &CertificateBinding {
    certificate
        .evidence
        .clean_cic_kernel_recheck()
        .and_then(|recheck| recheck.binding.as_deref())
        .expect("fixture certificate is bound")
}

/// Re-key a bound certificate's v8 lineage after its binding was edited, so
/// a test measures the BINDING rule and not the lineage floor.
fn rekey_v8(m: &mut Module, certificate: usize) {
    let obligation = m.proof_certificates[certificate].obligation;
    let obligation = m
        .proof_obligations
        .iter()
        .find(|o| o.id == obligation)
        .cloned()
        .expect("obligation exists");
    let lineage = {
        let resolve = module_symbol_resolver(m);
        clean_cic_lineage_digest_v8(
            &obligation,
            &resolve,
            Some(binding(&m.proof_certificates[certificate])),
        )
        .expect("keyable")
    };
    let ProofEvidence::CleanCic { lineage: slot, .. } =
        &mut m.proof_certificates[certificate].evidence
    else {
        unreachable!()
    };
    *slot = lineage;
}

fn retarget_all_calls(m: &mut Module, caller: usize, to: FuncId) {
    let mut hits = 0;
    for node in &mut m.functions[caller].blocks[0].body {
        if let Inst::Call { callee, .. } = &mut node.inst {
            *callee = to;
            hits += 1;
        }
    }
    assert!(hits > 0, "fixture caller has a call to retarget");
}

fn run(m: &Module, entry: &str, a: u64, b: u64) -> u128 {
    let func = m.function_by_name(entry).expect("entry exists");
    let args = vec![
        InterpretValue::int(Ty::U64, i128::from(a)).expect("u64 arg"),
        InterpretValue::int(Ty::U64, i128::from(b)).expect("u64 arg"),
    ];
    let out = Interpreter::with_module(m)
        .execute_func(func.id, args)
        .expect("fixture runs")
        .returns;
    out[0].as_int().expect("integer result").as_unsigned()
}

/// Every in-process single-module layer (the linked walk hashes the root
/// through the binary plan, which a bound module refuses — see the module
/// docs).
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

fn binding_mismatches(errors: &[ValidationError], obligation: u32) -> Vec<String> {
    errors
        .iter()
        .filter_map(|error| match error {
            ValidationError::CertificateBindingMismatch {
                obligation: o,
                field,
                ..
            } if *o == obligation => Some(field.clone()),
            _ => None,
        })
        .collect()
}

fn strict() -> ValidationConfig<'static> {
    ValidationConfig::pinned().with_bound_certificates(true)
}

// ===========================================================================
// (a) the binding — positive, and every field's twin
// ===========================================================================

#[test]
fn bound_tv_module_certifies_on_every_layer_and_under_the_strict_policy() {
    let m = bound_a0();
    for (layer, errors) in layers(&m) {
        assert!(
            errors.is_empty(),
            "bound A0 must certify on {layer}: {errors:?}"
        );
    }
    let report = validate_module_with_config(&m, &strict());
    assert!(
        report.is_ok(),
        "bound A0 under require_bound_certificates: {:?}",
        report.errors()
    );
    assert_eq!(
        report.replayed_certificate_refs().map(BTreeSet::len),
        Some(3),
        "all three bound TV certificates are kernel-tier authority"
    );
    for certificate in &m.proof_certificates {
        if let Some(b) = certificate
            .evidence
            .clean_cic_kernel_recheck()
            .and_then(|r| r.binding.as_deref())
        {
            assert!(b.origin_module.is_none() && b.source.is_none());
        }
    }
    assert_eq!(
        binding(&m.proof_certificates[2]).callees,
        vec!["plus".to_string()],
        "top's binding lists the one callee its statement quantifies over"
    );
    assert!(binding(&m.proof_certificates[0]).callees.is_empty());
}

/// `b2.gap.no_kernel_environment_digest_on_clean_cic_recheck` (F-007),
/// FLIPPED: the directive carries `binding.environment_digest`, and a
/// certificate re-checks only in an environment of equal content. Twin: the
/// contract anchor's environment (the bare prelude, no heap vocabulary) on a
/// TV certificate is refused by name.
#[test]
fn b2_gap_no_kernel_environment_digest_on_clean_cic_recheck() {
    let mut m = bound_a0();
    assert!(validate_module(&m).is_empty(), "honest baseline certifies");
    // The environment of ANOTHER anchor: the contract path's bare prelude.
    let other = {
        let mut probe = contract_module("(= 1 1)");
        let certificate =
            contract_clean_cic_certificate_bound_in(&probe, &probe.proof_obligations[0], "probe")
                .expect("bound contract certificate mints");
        probe.proof_certificates.push(certificate);
        binding(&probe.proof_certificates[0]).environment_digest
    };
    assert_ne!(
        other,
        binding(&m.proof_certificates[0]).environment_digest,
        "the TV anchor environment (prelude + heap vocabulary) and the contract environment \
         (bare prelude) have different identities"
    );
    binding_mut(&mut m.proof_certificates[0]).environment_digest = other;
    rekey_v8(&mut m, 0);
    let errors = validate_module(&m);
    assert_eq!(
        binding_mismatches(&errors, 0),
        vec!["environment_digest".to_string()],
        "{errors:?}"
    );
}

#[test]
fn statement_digest_with_one_byte_mutated_is_refused() {
    let mut m = bound_a0();
    let mut digest = binding(&m.proof_certificates[1]).statement_digest;
    digest.bytes[0] ^= 1;
    binding_mut(&mut m.proof_certificates[1]).statement_digest = digest;
    rekey_v8(&mut m, 1);
    let errors = validate_module(&m);
    assert_eq!(
        binding_mismatches(&errors, 1),
        vec!["statement_digest".to_string()],
        "{errors:?}"
    );
    // Mutation control: the refusal empties the kernel-tier set, so the
    // caller grounded at `plus` is not admitted either (all-or-nothing).
    assert_eq!(validate_module_report(&m).replayed_certificate_refs(), None);
}

/// `b3.gap.composition.consistent_retarget_to_certified_callee` (the WS1.4
/// residual, F-005), FLIPPED: retarget every call in `top` from `plus` to
/// the honestly certified `minus` of the same arity and rank AND rewrite the
/// grounding row to `minus`. The statement is still callee-agnostic, but the
/// BOUND certificate lists `["plus"]`, the re-derived statement quantifies
/// over `["minus"]`, and the mismatch is refused by name. Twin: the honest
/// bound baseline certifies. The legacy UNBOUND form of the same edit is
/// still accepted by the default lanes (it records no callee list) and is
/// refused by `require_bound_certificates` — the disclosed residual.
#[test]
fn b3_gap_composition_consistent_retarget_to_certified_callee() {
    let mut m = bound_a0();
    let before = run(&m, "top", 20, 15);
    let minus = m.functions[MINUS].id;
    retarget_all_calls(&mut m, TOP, minus);
    let last = m.proof_certificates.len() - 1;
    m.proof_certificates[last] = inherit(2, minus, 1);
    let after = run(&m, "top", 20, 15);
    assert_eq!(
        (before, after),
        (327, 287),
        "the retarget changes behaviour"
    );
    let errors = validate_module(&m);
    assert_eq!(
        binding_mismatches(&errors, 2),
        vec!["callees".to_string()],
        "{errors:?}"
    );
    assert!(errors.iter().any(|e| matches!(
        e,
        ValidationError::CertificateBindingMismatch { obligation: 2, detail, .. }
            if detail.contains("[\"plus\"]") && detail.contains("[\"minus\"]")
    )));

    // The legacy unbound form: accepted by the default lane (no callee list
    // to compare), refused under the strict policy.
    let mut legacy = unbound_a0();
    retarget_all_calls(&mut legacy, TOP, minus);
    let last = legacy.proof_certificates.len() - 1;
    legacy.proof_certificates[last] = inherit(2, minus, 1);
    assert!(validate_module(&legacy).is_empty());
    let strict_errors = validate_module_with_config(&legacy, &strict()).into_errors();
    assert_eq!(
        strict_errors
            .iter()
            .filter(|e| matches!(e, ValidationError::UnboundCertificate { .. }))
            .count(),
        3,
        "{strict_errors:?}"
    );
}

/// ADVERSARIAL, and the answer is a DISCLOSED RESIDUAL, not a refusal.
///
/// `CertificateBinding.callees` is RECOMPUTED from the body and compared, so
/// it catches an edit that moves the call without moving the certificate.
/// It cannot catch an adversary who edits BOTH: the Fragment-3b statement is
/// callee-agnostic (both callees have the same arity and name rank, so
/// `tv_statement` is byte-identical and the old proof term still type-checks),
/// the environment is unchanged, and the v8 lineage is a digest the same
/// adversary recomputes. What is left unpinned is the comparand↔SOURCE link —
/// finding F-008. WS1.13 closed that link for an ISLAND-BOUND certificate
/// whose function has NO callees (`island_theorem.rs`,
/// `a_tv_comparand_that_is_not_the_named_declarations_value_is_refused`);
/// `top` is a CALLER, and binding each callee of a caller to its own island
/// declaration is WS1.13's slice 2 (an island-bound caller is refused by name,
/// `an_island_bound_caller_is_the_disclosed_slice_two_residual`). So this
/// residual stands for callers until slice 2 lands, and nobody may read the
/// flipped `b3.gap.composition.consistent_retarget_to_certified_callee` row
/// as covering a re-minter.
#[test]
fn consistent_retarget_with_a_reminted_binding_is_the_disclosed_residual() {
    let mut m = bound_a0();
    let minus = m.functions[MINUS].id;
    retarget_all_calls(&mut m, TOP, minus);
    let last = m.proof_certificates.len() - 1;
    m.proof_certificates[last] = inherit(2, minus, 1);
    // The adversary re-mints the ONE field its module edit invalidated, and
    // re-keys the lineage that covers it.
    binding_mut(&mut m.proof_certificates[2]).callees = vec!["minus".to_string()];
    rekey_v8(&mut m, 2);
    assert_eq!(
        run(&m, "top", 20, 15),
        287,
        "the retarget changed behaviour"
    );
    let errors = validate_module(&m);
    assert!(
        errors.is_empty(),
        "RESIDUAL (F-008 for CALLERS → WS1.13 slice 2): a re-minted binding is still \
         admitted; if this now refuses, the residual closed — update the b3 ratchet detail \
         and this test: {errors:?}"
    );
    let strict_errors = validate_module_with_config(&m, &strict()).into_errors();
    assert!(
        strict_errors.is_empty(),
        "require_bound_certificates does not close it either (every row IS bound): \
         {strict_errors:?}"
    );
}

/// ADVERSARIAL: the binding is OPTIONAL, so the cheapest evasion of the
/// callee rule is to DELETE it and re-key the certificate to the legacy
/// index-keyed lineage. The default lanes admit that (an unbound certificate
/// keeps its pre-binding meaning, by design); only
/// `with_bound_certificates(true)` refuses it, and then by the name that says
/// so. This is the exact reason the knob exists, and the reason the flipped
/// b3 row is conditional on producers minting BOUND certificates.
#[test]
fn stripping_the_binding_downgrades_to_the_unbound_lane() {
    let mut m = bound_a0();
    let minus = m.functions[MINUS].id;
    retarget_all_calls(&mut m, TOP, minus);
    let last = m.proof_certificates.len() - 1;
    m.proof_certificates[last] = inherit(2, minus, 1);
    let obligation = m.proof_obligations[2].clone();
    let ProofEvidence::CleanCic {
        lineage,
        kernel_recheck: Some(recheck),
        ..
    } = &mut m.proof_certificates[2].evidence
    else {
        unreachable!("fixture certificate carries a directive")
    };
    recheck.binding = None;
    *lineage = clean_cic_lineage_digest(&obligation);
    let errors = validate_module(&m);
    assert!(
        errors.is_empty(),
        "an unbound certificate keeps its pre-binding meaning on the default lanes: {errors:?}"
    );
    let strict_errors = validate_module_with_config(&m, &strict()).into_errors();
    assert_eq!(
        strict_errors
            .iter()
            .filter(|e| matches!(e, ValidationError::UnboundCertificate { obligation: 2 }))
            .count(),
        1,
        "the downgraded row, and only it, is named: {strict_errors:?}"
    );
}

/// `plus` / `minus` and a caller `both(a,b) = plus(a,b) - minus(a,b)` whose
/// CALL order (`plus`, `minus`) is the reverse of the canonical NAME order
/// (`minus`, `plus`), so the canonical order is actually measured.
fn two_callee_module() -> Module {
    let mut mb = ModuleBuilder::new("certificate_binding_two_callees");
    mb.set_default_producer(Producer::Clean);
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let leaf = |mb: &mut ModuleBuilder, name: &str, op: BinOp| {
        let mut f = mb.function(name, sig);
        let e = f.create_block();
        let a = f.add_block_param(e, Ty::U64);
        let b = f.add_block_param(e, Ty::U64);
        f.switch_to_block(e);
        let p = f.mul(Ty::U64, a, b);
        let r = f.binop(op, Ty::U64, p, a);
        f.ret(vec![r]);
        f.build()
    };
    let plus_id = leaf(&mut mb, "plus", BinOp::Add);
    let minus_id = leaf(&mut mb, "minus", BinOp::Sub);
    let mut f = mb.function("both", sig);
    let e = f.create_block();
    let a = f.add_block_param(e, Ty::U64);
    let b = f.add_block_param(e, Ty::U64);
    f.switch_to_block(e);
    // The same body shape as `tv_callee_binding.rs`'s `two`, which the WS1.4
    // suite already certifies, so the fragment is not what is under test here.
    let x = f.call(plus_id, vec![a, b]);
    let y = f.call(minus_id, vec![a, b]);
    let r = f.sub(Ty::U64, x, y);
    f.ret(vec![r]);
    f.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    for func in &mut m.functions {
        func.body_gate = Some(BodyGate::Gated {
            authority: "clean-kernel-tv".to_string(),
            evidence: None,
        });
    }
    certify_bound(&mut m, &[PLUS, MINUS, TOP]);
    let plus_id = m.functions[PLUS].id;
    let minus_id = m.functions[MINUS].id;
    m.proof_certificates.push(inherit(2, plus_id, 0));
    m.proof_certificates.push(inherit(2, minus_id, 1));
    m
}

/// ADVERSARIAL: the `callees` list is the CANONICAL (name-sorted) telescope
/// order, not the call order, and it must be COMPLETE. A permutation and a
/// truncation are each refused by name — the contract a producer's minter
/// (clean's `emit_trust_ir_tv.rs`) has to meet, measured on a caller whose
/// call order and name order differ.
#[test]
fn binding_callees_are_name_sorted_and_complete() {
    let m = two_callee_module();
    let errors = validate_module(&m);
    assert!(
        errors.is_empty(),
        "the two-callee baseline certifies: {errors:?}"
    );
    assert_eq!(
        binding(&m.proof_certificates[2]).callees,
        vec!["minus".to_string(), "plus".to_string()],
        "canonical order is name-sorted, not call order"
    );

    let mut permuted = m.clone();
    binding_mut(&mut permuted.proof_certificates[2]).callees =
        vec!["plus".to_string(), "minus".to_string()];
    rekey_v8(&mut permuted, 2);
    assert_eq!(
        binding_mismatches(&validate_module(&permuted), 2),
        vec!["callees".to_string()],
        "a permuted telescope is refused"
    );

    let mut truncated = m.clone();
    binding_mut(&mut truncated.proof_certificates[2]).callees = vec!["minus".to_string()];
    rekey_v8(&mut truncated, 2);
    assert_eq!(
        binding_mismatches(&validate_module(&truncated), 2),
        vec!["callees".to_string()],
        "an incomplete telescope is refused"
    );
}

#[test]
fn callees_on_a_non_tv_anchor_must_be_empty() {
    let mut m = contract_module("(= 1 1)");
    let certificate = contract_clean_cic_certificate_bound_in(&m, &m.proof_obligations[0], "probe")
        .expect("bound contract certificate mints");
    m.proof_certificates.push(certificate);
    assert!(
        validate_module(&m).is_empty(),
        "bound contract baseline certifies"
    );
    binding_mut(&mut m.proof_certificates[0]).callees = vec!["plus".to_string()];
    rekey_v8(&mut m, 0);
    let errors = validate_module(&m);
    assert_eq!(binding_mismatches(&errors, 0), vec!["callees".to_string()]);
}

#[test]
fn origin_module_must_name_a_declared_import_row() {
    let mut m = bound_a0();
    let origin = ProofDigest::sha256([0x5a; 32]);
    binding_mut(&mut m.proof_certificates[0]).origin_module = Some(origin);
    rekey_v8(&mut m, 0);
    let errors = validate_module(&m);
    assert_eq!(
        binding_mismatches(&errors, 0),
        vec!["origin_module".to_string()],
        "{errors:?}"
    );
    // Twin: the same digest declared as an import row is admitted at module
    // level (the linked walk additionally authenticates the row).
    m.imports.push(ModuleImport {
        name: "minting_crate".to_string(),
        digest: origin,
        producer: Some(Producer::Clean),
        scheme: trust_ir::IdentityScheme::CURRENT,
    });
    let errors = validate_module(&m);
    assert!(errors.is_empty(), "{errors:?}");
}

/// The certificate-binding half of `LEAN.home.source_digest`: a certificate
/// can name the source definition its comparand was derived from
/// (`SourceDefinitionRef { decl, closure_digest }`), the carrier survives a
/// validation pass and the JSON round trip, and it is part of the evidence
/// identity. Its CHECK against the comparand (WS1.13) runs only when the
/// certificate also carries an island — see `island_theorem.rs`; WITHOUT an
/// island, as here, the reference stays an unchecked carrier (the certificate
/// keeps its mint-time meaning), which is what this test pins.
#[test]
fn lean_home_source_digest_certificate_binding_half() {
    let mut m = bound_a0();
    let source = SourceDefinitionRef {
        decl: "Lib.plus".to_string(),
        closure_digest: ProofDigest::sha256([0x17; 32]),
    };
    let before = m.proof_certificates[0].evidence_digest();
    binding_mut(&mut m.proof_certificates[0]).source = Some(source.clone());
    rekey_v8(&mut m, 0);
    let errors = validate_module(&m);
    assert!(errors.is_empty(), "the carrier is admitted: {errors:?}");
    assert_ne!(
        before,
        m.proof_certificates[0].evidence_digest(),
        "the source reference is part of the evidence identity"
    );
    #[cfg(feature = "serde")]
    {
        let json = serde_json::to_string(&m).expect("serializes");
        let back: Module = serde_json::from_str(&json).expect("deserializes");
        assert_eq!(
            binding(&back.proof_certificates[0]).source.as_ref(),
            Some(&source)
        );
        let msgpack = rmp_serde::to_vec(&m).expect("msgpack");
        let back: Module = rmp_serde::from_slice(&msgpack).expect("msgpack back");
        assert_eq!(back, m);
    }
}

/// The whole binding survives both serde transports and still validates: the
/// v8 lineage folds the binding bytes in, so a transport that dropped or
/// reordered a field would leave the certificate bound to nothing and the
/// module refused. (`skip_serializing_if` on the sole trailing field is what
/// keeps positional MessagePack legal; this measures that it is also
/// lossless.)
#[cfg(feature = "serde")]
#[test]
fn a_bound_module_survives_json_and_messagepack_and_still_validates() {
    let m = bound_a0();
    assert!(validate_module(&m).is_empty(), "the fixture validates");
    let json = serde_json::to_string(&m).expect("serializes");
    let back: Module = serde_json::from_str(&json).expect("deserializes");
    assert_eq!(back, m, "JSON is lossless for a bound certificate");
    assert!(
        validate_module(&back).is_empty(),
        "a JSON round trip must not unbind the certificate: {:?}",
        validate_module(&back)
    );
    let msgpack = rmp_serde::to_vec(&m).expect("msgpack");
    let back: Module = rmp_serde::from_slice(&msgpack).expect("msgpack back");
    assert_eq!(back, m, "MessagePack is lossless for a bound certificate");
    assert!(
        validate_module(&back).is_empty(),
        "a MessagePack round trip must not unbind the certificate: {:?}",
        validate_module(&back)
    );
}

#[cfg(feature = "binary")]
#[test]
fn binary_writer_carries_a_bound_certificate_at_its_version() {
    use trust_ir::binary::{
        CERTIFICATE_BINDING_FORMAT_VERSION, deserialize_module, serialize_module,
    };
    let m = bound_a0();
    let bytes = serialize_module(&m).expect("a bound module is encodable");
    assert_eq!(
        &bytes[8..12],
        &CERTIFICATE_BINDING_FORMAT_VERSION.to_le_bytes(),
        "a bound module is written at the carrier's version"
    );
    let back = deserialize_module(&bytes).expect("a bound module decodes");
    assert_eq!(back, m, "the binding survives the binary round trip");
    assert!(
        validate_module(&back).is_empty(),
        "and still re-checks bound: {:?}",
        validate_module(&back)
    );
    // Control: the unbound twin keeps its pre-v61 version and bytes.
    let plain = serialize_module(&unbound_a0()).expect("the unbound twin is encodable");
    assert!(
        u32::from_le_bytes(plain[8..12].try_into().expect("header"))
            < CERTIFICATE_BINDING_FORMAT_VERSION
    );
    // The carrier is read-gated: a bound blob relabelled as the version
    // below it is malformed and refused — never read as an unbound twin.
    let mut forged = bytes.clone();
    forged[8..12].copy_from_slice(&(CERTIFICATE_BINDING_FORMAT_VERSION - 1).to_le_bytes());
    assert!(
        !matches!(deserialize_module(&forged), Ok(ref decoded) if *decoded == unbound_a0()),
        "a relabelled blob must never decode as the unbound module"
    );
    assert!(deserialize_module(&forged).is_err());
}

#[test]
fn certificate_binding_wire_location_is_the_first_source_table_row() {
    let mut module = bound_a0();
    assert_eq!(
        module.first_certificate_binding(),
        Some((0, ProofId::new(0)))
    );
    // A preceding UNBOUND row with the same ID must not mask a later binding.
    // The locator is a locator, not a certificate-validity claim.
    module
        .proof_certificates
        .insert(0, unbound_a0().proof_certificates.remove(0));
    let before = module.clone();
    assert_eq!(
        module.first_certificate_binding(),
        Some((1, ProofId::new(0)))
    );
    assert_eq!(
        module, before,
        "the locator never erases or rewrites evidence"
    );
    assert_eq!(unbound_a0().first_certificate_binding(), None);
    assert_eq!(Module::new("empty").first_certificate_binding(), None);
}

/// Since v61 a bound module HAS a wire identity: no identity path refuses it,
/// the linked walk validates it as a root, and an importer authenticates it
/// by its (bound) digest — while a wrong digest is still refused, as a
/// digest mismatch rather than as a module without identity.
#[test]
fn certificate_binding_has_a_wire_identity_on_every_identity_path() {
    use trust_ir_build::{ModuleSet, validate_linked_module};

    let module = bound_a0();
    let before = module.clone();
    assert!(
        validate_module(&module).is_empty(),
        "honest in-memory binding"
    );
    assert_eq!(trust_ir_build::wire_identity_blocker(&module), None);
    let none = ModuleSet::new(std::iter::empty::<&Module>());
    let report = validate_linked_module(&module, &none, &RejectingModuleProofAuthority);
    assert!(report.errors().is_empty(), "{:?}", report.errors());
    assert_ne!(
        module.stable_digest(),
        unbound_a0().stable_digest(),
        "the binding is part of the module identity"
    );

    for (digest, authenticated) in [
        (module.stable_digest(), true),
        (ProofDigest::sha256([7; 32]), false),
    ] {
        let mut importer = Module::new("binding_importer");
        importer.imports.push(ModuleImport {
            name: module.name.clone(),
            digest,
            // A recorded producer (an unrecorded one is refused before any
            // identity question is asked, which would test nothing here).
            producer: Some(Producer::Clean),
            scheme: trust_ir::IdentityScheme::CURRENT,
        });
        let resolver = |_import: &ModuleImport| Some(&module);
        let report = validate_linked_module(&importer, &resolver, &RejectingModuleProofAuthority);
        let refused: Vec<&str> = report
            .errors()
            .iter()
            .filter_map(|error| match error {
                ValidationError::UnauthenticatedImport {
                    import: 0, detail, ..
                } => Some(detail.as_str()),
                _ => None,
            })
            .collect();
        // Every refusal names why; none is a module WITHOUT identity.
        assert!(
            refused.iter().all(|d| !d.contains("no wire identity")),
            "{refused:?}"
        );
        if authenticated {
            // The bound module's digest AUTHENTICATES it (checks C1-C4 of
            // `Module::verify_import_hashed` hold). Neither fixture pins a
            // target, so the pair is still refused by the target rule (C6),
            // and by nothing about its identity.
            assert!(
                refused.iter().all(|d| !d.contains("stable digest")),
                "{refused:?}"
            );
            assert!(refused.iter().all(|d| d.contains("target")), "{refused:?}");
        } else {
            assert!(
                refused
                    .iter()
                    .any(|d| d.contains("stable digest") && d.contains("is not the")),
                "a wrong digest is refused as a digest mismatch: {refused:?}"
            );
        }
    }
    assert_eq!(module, before, "no identity path erases the binding");
}

#[cfg(feature = "binary")]
#[test]
fn certificate_binding_projection_carries_or_refuses_by_version() {
    use trust_ir::binary::{
        BinaryProjectionError, ModuleBinaryBody, ModuleBinaryOptions, ModuleSymbolProjection,
        ProjectedModuleBinaryPlan,
    };
    let module = bound_a0();
    let before = module.clone();
    for body in [ModuleBinaryBody::Raw, ModuleBinaryBody::Canonical] {
        let bytes = ProjectedModuleBinaryPlan::try_new(
            &module,
            ModuleBinaryOptions {
                body,
                symbols: ModuleSymbolProjection::Exact,
                ..ModuleBinaryOptions::default()
            },
        )
        .expect("a bound module projects at v61")
        .to_vec()
        .expect("a bound projection writes");
        let decoded = trust_ir::binary::deserialize_module(&bytes).expect("bound binary");
        assert_eq!(
            decoded.first_certificate_binding(),
            Some((0, ProofId::new(0))),
            "{body:?}: the projection keeps the binding"
        );
    }
    for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
        let error = ProjectedModuleBinaryPlan::try_new(
            &module,
            ModuleBinaryOptions {
                body,
                ..ModuleBinaryOptions::default()
            },
        )
        .err()
        .expect("a v38 projection cannot carry a binding");
        assert_eq!(error, BinaryProjectionError::CertificateBindingRequiresV61);
        assert!(error.to_string().contains("CleanCicKernelRecheck.binding"));
        // Control: the unbound twin is NOT refused for a binding. (It is still
        // refused by a v38 projection, for its v41 codegen license, which the
        // projection keeps exactly; the binding is what moves the refusal to
        // the carrier's version.)
        let control = ProjectedModuleBinaryPlan::try_new(
            &unbound_a0(),
            ModuleBinaryOptions {
                body,
                ..ModuleBinaryOptions::default()
            },
        )
        .err();
        assert_ne!(
            control,
            Some(BinaryProjectionError::CertificateBindingRequiresV61),
            "unbound v38 control"
        );
        assert!(
            control
                .as_ref()
                .is_none_or(|e| !e.to_string().contains("CleanCicKernelRecheck.binding")),
            "unbound v38 control: {control:?}"
        );
    }
    assert_eq!(module, before);
}

#[cfg(feature = "binary")]
#[test]
fn certificate_binding_native_binary_envelope_carries_the_bound_module() {
    use trust_ir::binary::{
        deserialize_native_verification_bundle, serialize_native_verification_bundle,
    };
    use trust_ir::proof::ProofLineageManifest;
    use trust_ir::request::{NativeAdapterInput, NativeBundleProducer, NativeVerificationBundle};
    let module = bound_a0();
    let bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TrustIr,
        NativeAdapterInput::TrustIrModule,
        module.stable_digest(),
        module,
        ProofLineageManifest::default(),
    );
    let bytes = serialize_native_verification_bundle(&bundle).expect("a bound bundle encodes");
    let back = deserialize_native_verification_bundle(&bytes).expect("and decodes");
    assert_eq!(
        back.module, bundle.module,
        "the binding survives the envelope"
    );
}

// ===========================================================================
// (a) the named contract anchor
// ===========================================================================

/// `fn f() -> u64 { 7 }` with one Certified Postcondition `(text)` scoped to
/// it (obligation #0).
fn contract_module(text: &str) -> Module {
    let mut mb = ModuleBuilder::new("certificate_binding_contract");
    let ft = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("f", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let v = fb.uconst(Ty::U64, 7);
    fb.ret(vec![v]);
    let f = fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    // A bodied function that makes NO licensing claim is refused by the
    // codegen layer (`UnlicensedBodyForCodegen`, the fail-closed v41 default),
    // and `layers` below runs that layer. The claim is `trust-verify` — the
    // Rust producer's authority — and not `clean-kernel-tv`, which is the one
    // EVIDENCE-BOUND authority and would demand a kernel-replayed
    // `TranslationValidation` row this contract fixture deliberately does not
    // have.
    m.function_by_id_mut(f).expect("just built").body_gate = Some(BodyGate::Gated {
        authority: "trust-verify".to_string(),
        evidence: None,
    });
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Certified,
            "ensures clause 0 of 'f'",
        )
        .with_function(f)
        .with_formula(ProofFormula::smtlib2(text, "Bool")),
    );
    m
}

#[test]
fn bound_contract_certificate_validates_and_its_statement_twin_is_refused() {
    let mut m = contract_module("(= 1 1)");
    let certificate = contract_clean_cic_certificate_bound_in(&m, &m.proof_obligations[0], "probe")
        .expect("bound contract certificate mints");
    let recheck = certificate
        .evidence
        .clean_cic_kernel_recheck()
        .expect("bound minter emits a directive");
    assert_eq!(recheck.anchor, KERNEL_ANCHOR_TRUST_IR_CONTRACT);
    assert_eq!(recheck.module, KERNEL_ANCHOR_TRUST_IR_CONTRACT_MODULE);
    assert!(recheck.theorems.is_empty() && recheck.allowed_axioms.is_empty());
    m.proof_certificates.push(certificate);
    for (layer, errors) in layers(&m) {
        assert!(errors.is_empty(), "bound contract on {layer}: {errors:?}");
    }
    assert!(validate_module_with_config(&m, &strict()).is_ok());

    // Twin: the statement of ANOTHER contract on the same certificate.
    let other = {
        let probe = contract_module("(= 2 2)");
        let certificate =
            contract_clean_cic_certificate_bound_in(&probe, &probe.proof_obligations[0], "p")
                .expect("mints");
        binding(&certificate).statement_digest
    };
    binding_mut(&mut m.proof_certificates[0]).statement_digest = other;
    rekey_v8(&mut m, 0);
    let errors = validate_module(&m);
    assert_eq!(
        binding_mismatches(&errors, 0),
        vec!["statement_digest".to_string()]
    );

    // A false contract mints nothing, bound or not.
    let bad = contract_module("(= 1 2)");
    assert!(
        contract_clean_cic_certificate_bound_in(&bad, &bad.proof_obligations[0], "p").is_none()
    );
}

#[test]
fn contract_anchor_directive_citing_a_theorem_is_refused() {
    let mut m = contract_module("(= 1 1)");
    let mut certificate =
        contract_clean_cic_certificate_bound_in(&m, &m.proof_obligations[0], "probe")
            .expect("mints");
    let ProofEvidence::CleanCic {
        kernel_recheck: Some(recheck),
        ..
    } = &mut certificate.evidence
    else {
        unreachable!()
    };
    recheck.theorems = vec!["Nat.le_refl".to_string()];
    m.proof_certificates.push(certificate);
    let errors = validate_module(&m);
    assert_eq!(
        binding_mismatches(&errors, 0),
        vec!["directive".to_string()]
    );
    // And the canonical module is enforced like every other anchor's.
    let ProofEvidence::CleanCic {
        kernel_recheck: Some(recheck),
        ..
    } = &mut m.proof_certificates[0].evidence
    else {
        unreachable!()
    };
    recheck.theorems.clear();
    recheck.module = "Crownproof.SlackCertZ".to_string();
    let errors = validate_module(&m);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, reason }
                if reason.contains("requires canonical module 'TrustIr.Contract'")
        )),
        "{errors:?}"
    );
}

#[test]
fn directive_less_contract_certificate_keeps_its_unbound_meaning() {
    let mut m = contract_module("(= 1 1)");
    let certificate = contract_clean_cic_certificate_in(&m, &m.proof_obligations[0], "legacy")
        .expect("legacy minter");
    assert!(certificate.evidence.clean_cic_kernel_recheck().is_none());
    m.proof_certificates.push(certificate);
    assert!(
        validate_module(&m).is_empty(),
        "admitted by the default lane"
    );
    let errors = validate_module_with_config(&m, &strict()).into_errors();
    assert_eq!(
        errors,
        vec![ValidationError::UnboundCertificate { obligation: 0 }],
        "refused by name under the strict policy"
    );
}

#[test]
fn a_bound_directive_on_the_tv_anchor_is_not_a_contract_directive() {
    // Kind/anchor guards still apply: a contract obligation citing the TV
    // anchor is refused before any binding is compared.
    let mut m = contract_module("(= 1 1)");
    let mut certificate =
        contract_clean_cic_certificate_bound_in(&m, &m.proof_obligations[0], "probe")
            .expect("mints");
    let ProofEvidence::CleanCic {
        kernel_recheck: Some(recheck),
        ..
    } = &mut certificate.evidence
    else {
        unreachable!()
    };
    recheck.anchor = trust_ir::proof::KERNEL_ANCHOR_CLEAN_BACKEND_TV.to_string();
    recheck.module = "CleanCompiler.BackendTV".to_string();
    m.proof_certificates.push(certificate);
    let errors = validate_module(&m);
    assert!(
        errors.iter().any(|e| matches!(
            e,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, reason }
                if reason.contains("may only certify TranslationValidation obligations")
        )),
        "{errors:?}"
    );
}

// ===========================================================================
// (b) lineage v8 and the duplicate-content guard
// ===========================================================================

/// Renumber the fixture's functions: reverse their ids (and storage order),
/// updating every `Call` target and obligation scope / site — the shape a
/// merge gives a module.
fn renumber_reversed(m: &mut Module) {
    let n = u32::try_from(m.functions.len()).expect("small");
    let map = |id: FuncId| FuncId::new(n - 1 - id.index());
    for function in &mut m.functions {
        function.id = map(function.id);
        for block in &mut function.blocks {
            for node in &mut block.body {
                if let Inst::Call { callee, .. } = &mut node.inst {
                    *callee = map(*callee);
                }
            }
        }
    }
    m.functions.reverse();
    for obligation in &mut m.proof_obligations {
        obligation.function = obligation.function.map(map);
        if let Some(site) = &mut obligation.site {
            site.function = map(site.function);
        }
    }
    for certificate in &mut m.proof_certificates {
        if let ProofEvidence::InheritedFromCallee { callee, .. } = &mut certificate.evidence {
            *callee = map(*callee);
        }
    }
}

/// The F-020 control pair: the v8 (symbol-keyed) certificate of `plus`
/// survives a FuncId renumbering (fn#0 becomes fn#2); the v6 (index-keyed)
/// certificate of the same obligation is refused as a lineage mismatch.
#[test]
fn v8_lineage_survives_funcid_renumbering_while_v6_is_refused() {
    let mut bound = base_module();
    certify_bound(&mut bound, &[PLUS]);
    let mut legacy = base_module();
    certify_unbound(&mut legacy, &[PLUS]);
    assert!(validate_module(&bound).is_empty());
    assert!(validate_module(&legacy).is_empty());
    let v6 = clean_cic_lineage_digest(&legacy.proof_obligations[0]);
    assert_eq!(
        legacy.proof_certificates[0].evidence.clean_cic_lineage(),
        Some(v6)
    );

    renumber_reversed(&mut bound);
    renumber_reversed(&mut legacy);
    assert_eq!(bound.function_by_name("plus").unwrap().id, FuncId::new(2));
    assert_eq!(
        bound.functions[2].name, "plus",
        "index and id agree after the renumbering"
    );

    let errors = validate_module(&bound);
    assert!(errors.is_empty(), "v8 survives the renumbering: {errors:?}");
    let errors = validate_module(&legacy);
    assert_eq!(
        errors,
        vec![ValidationError::CertifiedCleanCicLineageMismatch { obligation: 0 }],
        "the index-keyed v6 lineage names the old index"
    );
}

#[test]
fn v8_lineage_is_bound_to_the_certificate_binding() {
    // Editing the binding without re-keying the lineage is a lineage
    // mismatch: the binding bytes are part of the v8 preimage.
    let mut m = bound_a0();
    binding_mut(&mut m.proof_certificates[0]).source = Some(SourceDefinitionRef {
        decl: "x".to_string(),
        closure_digest: ProofDigest::zero(),
    });
    let errors = validate_module(&m);
    assert!(
        errors.contains(&ValidationError::CertifiedCleanCicLineageMismatch { obligation: 0 }),
        "{errors:?}"
    );
}

/// The v46 `spec` temporal backref is part of what an obligation MEANS — the
/// reason the index-keyed digest grew its `v7` domain (WS4.14) — so the
/// symbol-keyed v8 lineage binds it too. Two temporal rows of one function
/// differing ONLY in which property they discharge get distinct v8 lineages
/// (a bound certificate minted for one cannot replay on the other) and
/// distinct v8 content (so they are never `DuplicateObligationContent`).
/// Without it, v8 would re-open for bound certificates exactly the replay v7
/// closed for index-keyed ones.
#[test]
fn v8_lineage_binds_the_spec_temporal_backref() {
    let m = contract_module("(= 1 1)");
    let resolve = module_symbol_resolver(&m);
    let mut unset = m.proof_obligations[0].clone();
    unset.kind = ObligationKind::Liveness;
    let with_spec = |machine: &str, temporal: &str| {
        let mut row = unset.clone();
        row.spec = Some(SpecObligationRef::new(machine, temporal));
        row
    };
    let rows = [
        unset.clone(),
        with_spec("Machine", "P"),
        with_spec("Machine", "Q"),
        with_spec("Other", "P"),
        // Framing: the two names are length-prefixed, so moving a byte across
        // the machine/property boundary is a different backref.
        with_spec("MachineP", ""),
    ];
    let lineages: Vec<ProofDigest> = rows
        .iter()
        .map(|row| clean_cic_lineage_digest_v8(row, &resolve, None).expect("keyed"))
        .collect();
    let contents: Vec<Vec<u8>> = rows
        .iter()
        .map(|row| clean_cic_lineage_content_v8(row, &resolve).expect("keyed"))
        .collect();
    for i in 0..rows.len() {
        for j in (i + 1)..rows.len() {
            assert_ne!(
                lineages[i], lineages[j],
                "rows {i} and {j} differ only in `spec` yet share a v8 lineage"
            );
            assert_ne!(
                contents[i], contents[j],
                "rows {i} and {j} differ only in `spec` yet are duplicate v8 content"
            );
        }
    }
    // Control: the backref is the ONLY difference, and the digest is a
    // function of content — the same row keys to the same lineage.
    assert_eq!(
        clean_cic_lineage_digest_v8(&rows[1].clone(), &resolve, None),
        Some(lineages[1])
    );
    // Control: the index-keyed digest already separates them (v5 vs v7), so
    // v8 now agrees with it rather than being the weaker of the two.
    assert_ne!(
        clean_cic_lineage_digest(&rows[1]),
        clean_cic_lineage_digest(&rows[2])
    );
}

#[test]
fn duplicate_obligation_content_is_refused_for_v8_rows_only() {
    // Two content-identical Certified rows on `f`, each with a BOUND (v8)
    // contract certificate: refused by name.
    let mut m = contract_module("(= 1 1)");
    let mut twin = m.proof_obligations[0].clone();
    twin.id = ProofId::new(1);
    m.proof_obligations.push(twin);
    for i in 0..2 {
        let certificate =
            contract_clean_cic_certificate_bound_in(&m, &m.proof_obligations[i], "probe")
                .expect("mints");
        m.proof_certificates.push(certificate);
    }
    let errors = validate_module(&m);
    assert_eq!(
        errors,
        vec![ValidationError::DuplicateObligationContent {
            function: 0,
            obligations: vec![0, 1],
        }],
        "{errors:?}"
    );

    // Control: the same two rows with LEGACY (v6, index-keyed) certificates
    // are not in the guard's domain — their lineages already differ by id.
    let mut legacy = contract_module("(= 1 1)");
    let mut twin = legacy.proof_obligations[0].clone();
    twin.id = ProofId::new(1);
    legacy.proof_obligations.push(twin);
    for i in 0..2 {
        let certificate =
            contract_clean_cic_certificate_in(&legacy, &legacy.proof_obligations[i], "legacy")
                .expect("mints");
        legacy.proof_certificates.push(certificate);
    }
    assert!(validate_module(&legacy).is_empty());
}

/// Control: a WS1.6 same-module restatement beside its BOUND kernel row —
/// content-identical except for status, certified by an
/// `InheritedFromCallee` row — never trips `DuplicateObligationContent`.
#[test]
fn ws1_6_restatement_beside_a_bound_kernel_row_does_not_trip_the_guard() {
    use trust_ir::proof::{ClauseBinding, ClausePlace, ClauseSort};
    let mut mb = ModuleBuilder::new_with_target_info(
        "certificate_binding_ws1_6",
        trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        },
    );
    let ft = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("g", ft);
    fb.set_producer(Producer::Clean);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let v = fb.uconst(Ty::U64, 42);
    fb.ret(vec![v]);
    let g = fb.build();
    let mut fb = mb.function("f", ft);
    fb.set_producer(Producer::TRust);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let r = fb.call(g, vec![]);
    fb.ret(vec![r]);
    fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    let ensures = || {
        let mut formula = ProofFormula::smtlib2("(>= result 0)", "Bool");
        formula.bindings = vec![(
            "result".to_string(),
            ClauseBinding {
                sort: ClauseSort::Int,
                place: ClausePlace::ResultSlot { index: 0 },
            },
        )];
        formula
    };
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Certified,
            "ensures clause 0 of 'g'",
        )
        .with_function(g)
        .with_formula(ensures()),
    );
    let kernel = contract_clean_cic_certificate_bound_in(&m, &m.proof_obligations[0], "kernel")
        .expect("a bound nonneg clause over a u64 result is mintable, bound");
    m.proof_certificates.push(kernel);
    m.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(1),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "f relies on ensures clause 0 of 'g'",
        )
        .with_function(g)
        .with_formula(ensures()),
    );
    m.proof_certificates.push(inherit(1, g, 0));
    let errors = validate_module(&m);
    assert!(errors.is_empty(), "{errors:?}");
    assert!(validate_module_with_config(&m, &strict()).is_ok());
}

// ===========================================================================
// the strict policy
// ===========================================================================

#[test]
fn require_bound_certificates_refuses_every_unbound_certified_row() {
    let m = unbound_a0();
    assert!(
        validate_module(&m).is_empty(),
        "the default lane admits unbound rows"
    );
    let errors = validate_module_with_config(&m, &strict()).into_errors();
    assert_eq!(
        errors,
        vec![
            ValidationError::UnboundCertificate { obligation: 0 },
            ValidationError::UnboundCertificate { obligation: 1 },
            ValidationError::UnboundCertificate { obligation: 2 },
        ]
    );
    // The knob only decides unbound rows: a row that already fails its
    // lineage floor is named once, by the floor.
    let mut m = unbound_a0();
    let ProofEvidence::CleanCic { lineage, .. } = &mut m.proof_certificates[0].evidence else {
        unreachable!()
    };
    lineage.bytes[0] ^= 1;
    let errors = validate_module_with_config(&m, &strict()).into_errors();
    assert!(
        errors.contains(&ValidationError::CertifiedCleanCicLineageMismatch { obligation: 0 }),
        "{errors:?}"
    );
    assert!(!errors.contains(&ValidationError::UnboundCertificate { obligation: 0 }));
}

// ===========================================================================
// (z) WS1.12 × WS1.15 — the binding and the widened kernel-TV fragment
// ===========================================================================
//
// WS1.15 widened the `clean_backend_tv` fragment (S1-S5) and, to do it, put
// FOUR new definitions into the anchor environment: the signed carrier
// aliases `CleanTV.Int8..Int64 : Type := Nat`. WS1.12 binds a certificate to
// the digest of that environment and of the statement the re-check derives.
// The two rules meet in exactly one place — `clean_backend_tv::
// anchor_environment`, the single spelling the re-check judges in AND the
// bound minter digests — so the pair below pins both directions:
//
// * the binding must not NARROW the fragment (a signed S3 rung must still be
//   mintable and certifiable when bound), and
// * the widened fragment must not let a certificate SKIP the binding (a shape
//   WS1.15 admits, and whose carrier check it explicitly does not catch, is
//   still refused by its named binding field).

/// `widen8(a: u8) -> R = zext a` — the S5/S3 probe WS1.15 uses for the result
/// carrier, stamped like a Clean-certified body.
fn widen8_module(dst: Ty) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("certificate_binding_widen8");
    mb.set_default_producer(Producer::Clean);
    let sig = mb.add_func_type(vec![Ty::U8], vec![dst.clone()]);
    let mut fb = mb.function("widen8", sig);
    fb.set_body_gate(BodyGate::Gated {
        authority: "clean-kernel-tv".to_string(),
        evidence: None,
    });
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::U8);
    fb.switch_to_block(e);
    let r = fb.zext(Ty::U8, dst, a);
    fb.ret(vec![r]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

/// Rewrite every occurrence of `from` in `func`'s signature, block params and
/// instruction types to `to` (the WS1.15 `retype` tamper, narrowed to what
/// this fixture contains).
fn retype(m: &mut Module, func: FuncId, from: &Ty, to: &Ty) {
    let f = m.function_by_id_mut(func).expect("function");
    let sig = f.ty;
    for block in &mut f.blocks {
        for (_, ty) in &mut block.params {
            if ty == from {
                *ty = to.clone();
            }
        }
        for node in &mut block.body {
            if let Inst::Cast { src_ty, dst_ty, .. } = &mut node.inst {
                if src_ty == from {
                    *src_ty = to.clone();
                }
                if dst_ty == from {
                    *dst_ty = to.clone();
                }
            }
        }
    }
    let fty = &mut m.func_types[sig.as_usize()];
    for ty in fty.params.iter_mut().chain(fty.returns.iter_mut()) {
        if ty == from {
            *ty = to.clone();
        }
    }
}

/// Mint the BOUND certificate for `func` as obligation 0.
fn certify_bound_func(m: &mut Module, func: FuncId) -> Result<(), String> {
    let (_node, obligation, certificate) = certify_identity_lineage_rung_bound(
        m,
        ProofLineageId::new(0),
        ProofId::new(0),
        transform(),
        func,
    )?;
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(certificate);
    Ok(())
}

/// DIRECTION 1 — the binding does not narrow WS1.15's fragment.
///
/// A signed result is S3: the statement equates at `CleanTV.Int32`, a
/// constant that exists only because `anchor_environment` installs the four
/// carrier aliases. Were the binding's environment to be built any other way
/// — the pre-WS1.15 prelude-plus-heap-vocabulary, say — this rung could not
/// be minted at all (`add_decl` on an unknown constant) or, worse, would be
/// digested against an environment the re-check does not judge in, and every
/// honest S3 certificate would be refused as `environment_digest`. So this
/// test is the guard on the ONE composition point, not a duplicate of
/// WS1.15's own S3 positive.
#[test]
fn a_bound_rung_in_the_widened_signed_fragment_certifies_on_every_layer() {
    let (mut m, f) = widen8_module(Ty::I32);
    certify_bound_func(&mut m, f).expect("the signed rung is inside the widened S3 fragment");
    for (layer, errors) in layers(&m) {
        assert!(
            errors.is_empty(),
            "a bound S3 (signed-result) rung must certify on {layer}: {errors:?}"
        );
    }
    assert!(
        validate_module_with_config(&m, &strict()).is_ok(),
        "and under require_bound_certificates"
    );
    assert_eq!(
        validate_module_report(&m)
            .replayed_certificate_refs()
            .map(|refs| refs.len()),
        Some(1),
        "the bound signed certificate reaches the kernel tier"
    );
    // The unsigned twin certifies too, and its binding is a DIFFERENT
    // statement digest — the premise the refusal below rests on.
    let (mut u32_m, g) = widen8_module(Ty::U32);
    certify_bound_func(&mut u32_m, g).expect("the unsigned rung is in-fragment");
    assert!(validate_module(&u32_m).is_empty());
    assert_ne!(
        binding(&m.proof_certificates[0]).statement_digest,
        binding(&u32_m.proof_certificates[0]).statement_digest,
        "the statement's `Eq` type is the RESULT carrier, so the two digests differ"
    );
    assert_eq!(
        binding(&m.proof_certificates[0]).environment_digest,
        binding(&u32_m.proof_certificates[0]).environment_digest,
        "both are judged in the one anchor environment"
    );
}

/// DIRECTION 2 — the widened fragment does not let a certificate skip the
/// binding, ON THE ONE SHAPE WS1.15 DISCLOSES AS UNCAUGHT.
///
/// WS1.15's carrier check binds the comparand's PARAMETER binders only (the
/// comparand carries nothing for the result), and `CleanTV.Int32` is def-eq
/// to `Nat`, so a tamper that relabels ONLY the result's signedness states a
/// true equation the kernel cannot separate from its source — pinned there as
/// `adv_result_only_sign_relabel_is_not_bound_by_the_carrier_check`.
///
/// For a BOUND certificate that residue is closed here, and by a different
/// mechanism: the statement digest is taken over the WS1.15 SORTED statement,
/// whose `Eq` type IS the result carrier, so the `u32`-minted binding does
/// not name the `i32` statement the re-check derives. The refusal is the
/// named field `statement_digest` — not a kernel refusal, not the binder
/// check, not the lineage floor (the v8 key is re-derived first, so the
/// certificate still binds to its obligation).
#[test]
fn a_result_only_sign_relabel_inside_the_widened_fragment_is_refused_by_statement_digest() {
    // Honest, bound, unsigned result — and it certifies.
    let (mut m, f) = widen8_module(Ty::U32);
    certify_bound_func(&mut m, f).expect("honest u32 result");
    assert!(validate_module(&m).is_empty(), "the honest twin certifies");
    assert_eq!(
        Interpreter::with_module(&m)
            .execute_func(f, vec![InterpretValue::int(Ty::U8, 200).expect("u8 arg")])
            .expect("runs")
            .returns[0]
            .as_int()
            .expect("integer")
            .as_unsigned(),
        200
    );

    // The tamper WS1.15's carrier check cannot see: the RESULT alone becomes
    // `i32`. No bit changes; the single `u8` parameter binder is untouched.
    retype(&mut m, f, &Ty::U32, &Ty::I32);
    rekey_v8(&mut m, 0);
    assert_eq!(
        Interpreter::with_module(&m)
            .execute_func(f, vec![InterpretValue::int(Ty::U8, 200).expect("u8 arg")])
            .expect("runs")
            .returns[0]
            .as_int()
            .expect("integer")
            .as_signed(),
        200,
        "the relabel changes no value — this is the WS1.15 residue, not a miscompile"
    );

    for (layer, errors) in layers(&m) {
        assert_eq!(
            binding_mismatches(&errors, 0),
            vec!["statement_digest".to_string()],
            "{layer}: the result-only sign relabel must be refused by its named binding \
             field, and by nothing else: {errors:?}"
        );
    }
    assert_eq!(
        validate_module_report(&m).replayed_certificate_refs(),
        None,
        "and the refusal keeps it out of the kernel tier"
    );
    // The UNBOUND form of the same module is the disclosed residue it stays:
    // WS1.15's positive still holds, so this test measures the binding and
    // not a narrowing of the fragment.
    let (mut unbound, g) = widen8_module(Ty::U32);
    let (_node, obligation, certificate) = certify_identity_lineage_rung(
        &unbound,
        ProofLineageId::new(0),
        ProofId::new(0),
        transform(),
        g,
    )
    .expect("honest u32 result");
    unbound.proof_obligations.push(obligation);
    unbound.proof_certificates.push(certificate);
    retype(&mut unbound, g, &Ty::U32, &Ty::I32);
    assert!(
        validate_module(&unbound).is_empty(),
        "unbound, the result-only relabel is still admitted (WS1.15's honest scope)"
    );
    assert_eq!(
        validate_module_with_config(&unbound, &strict()).into_errors(),
        vec![ValidationError::UnboundCertificate { obligation: 0 }],
        "the strict knob is what refuses it there"
    );
}

#[test]
fn the_directive_struct_carries_the_binding_field() {
    // Compile-time: the exhaustive destructuring names the field, so a
    // renamed or dropped carrier is a build error here.
    let CleanCicKernelRecheck {
        module: _,
        theorems: _,
        anchor: _,
        allowed_axioms: _,
        binding,
    } = &bound_a0().proof_certificates[0]
        .evidence
        .clean_cic_kernel_recheck()
        .expect("directive")
        .clone();
    assert!(binding.is_some());
}
