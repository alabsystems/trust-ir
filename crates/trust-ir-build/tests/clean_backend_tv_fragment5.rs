// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fragment-5 (boxed `Nat`, `() -> Ptr`) is outside trust-ir's
//! `clean_backend_tv` re-checker, and a certificate for one is refused BY NAME.
//!
//! `docs/SPEC_RATIFICATIONS.md`, "A reference-counted cell is released by
//! `Release`, never by `Dealloc`", clause 4. Clean's Fragment-5 walker denotes
//! a parameter-free `() -> Ptr` body over the boxed-`Nat` runtime rows
//! (`clean_box_uint64`, `l_Nat_*`, ...) to a closed `Nat`, and until Clean
//! d9f760a4d it minted a `clean_backend_tv` certificate and a `Gated
//! {"clean-kernel-tv"}` license for it. trust-ir's re-checker has no
//! Fragment-5: its return sort is a machine integer or a `Bool`, so a `Ptr`
//! return is refused before the kernel is consulted, and `validate_module`
//! refused the certificate AND with it the whole module — including the
//! legitimately certified Fragment-2 roots beside it. Clean now decides
//! Fragment-5 in its kernel and does not mint it (`FRAGMENT5_NOT_MINTED`,
//! license `Ungated`).
//!
//! These tests pin TODAY's trust-ir side of that decision, so that the day the
//! re-checker grows a Fragment-5 (which the clause requires to land here
//! first, with the ownership balance) this file is where the refusal turns
//! into an admission, deliberately:
//!
//! * the refusal names the `Ptr` return type, and the SAME certificate on the
//!   scalar twin of the body (`() -> u64`, the value Clean's Fragment-5 map
//!   gives the boxed body) certifies — so the refusal is about the return
//!   sort, not a malformed certificate;
//! * trust-ir's own public minter refuses to mint for the `Ptr` body;
//! * a `Ptr` certificate beside a certified Fragment-2 root refuses the
//!   module, and the not-minted shape Clean emits since d9f760a4d (no
//!   obligation, `Ungated`) validates with the Fragment-2 root still
//!   certified.
//!
//! Evidence class: test, on `targo --unverified`. Nothing here is proved.

use trust_ir::proof::{ProofLineageId, ProofTransform, ProofTransformStage};
use trust_ir::ty::Ty;
use trust_ir::value::ProofId;
use trust_ir::{BodyGate, Endianness, FuncId, Module, Producer, StructPassingPolicy, TargetInfo};
use trust_ir_build::{
    ModuleBuilder, ValidationError, certify_identity_lineage_rung, validate_module,
    validate_module_for_codegen,
};

/// Clean's boxed-`Nat` constant `256` (the `UInt8.size` shape): `u64 256`
/// boxed by the runtime row `clean_box_uint64`, whose Fragment-5 denotation is
/// the value itself.
const BOXED_VALUE: i128 = 256;
const ROOT: &str = "UInt8.size";
const KERNEL_TV: &str = "clean-kernel-tv";
/// The re-checker's refusal of a non-fragment return sort (`sort_of_ty` in
/// `clean_backend_tv`), for the `Ptr` return.
const PTR_RETURN_REFUSAL: &str = "return type: type ptr is outside the TV fragment";

fn target() -> TargetInfo {
    TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    }
}

fn transform() -> ProofTransform {
    ProofTransform::new(
        ProofTransformStage::Frontend,
        "identity",
        "clean-backend-tv-fragment5",
        "1.0.0",
    )
}

/// The Fragment-2 root Clean certifies legitimately: `inc(x) = x + 1` over
/// `u64`. Built first, so it is `FuncId` 0.
fn add_fragment2_root(mb: &mut ModuleBuilder) -> FuncId {
    let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut f = mb.function("inc", sig);
    let e = f.create_block();
    let x = f.add_block_param(e, Ty::U64);
    f.switch_to_block(e);
    let one = f.iconst(Ty::U64, 1);
    let r = f.add(Ty::U64, x, one);
    f.ret(vec![r]);
    f.build()
}

/// The boxed-`Nat` constant as Clean emits it (`boxed = true`):
/// `UInt8.size() -> ptr { k = 256; r = clean_box_uint64(k); ret r }`, beside
/// the bodyless runtime import. With `boxed = false`, its SCALAR twin
/// `UInt8.size() -> u64 { k = 256; ret k }`: the same function name and id,
/// denoting the same `Nat`, inside trust-ir's Fragment-2.
fn add_boxed_constant(mb: &mut ModuleBuilder, boxed: bool) -> FuncId {
    let box_sig = mb.add_func_type(vec![Ty::U64], vec![Ty::Ptr]);
    let clean_box_uint64 = mb.declare_function("clean_box_uint64", box_sig);
    let ret = if boxed { Ty::Ptr } else { Ty::U64 };
    let sig = mb.add_func_type(vec![], vec![ret]);
    let mut f = mb.function(ROOT, sig);
    let e = f.create_block();
    f.switch_to_block(e);
    let k = f.iconst(Ty::U64, BOXED_VALUE);
    let r = if boxed {
        f.call(clean_box_uint64, vec![k])
    } else {
        k
    };
    f.ret(vec![r]);
    f.build()
}

/// A Clean-produced module: every body licensed `gate`, so a certificate is
/// what the license rests on.
fn module(fragment2: bool, boxed: bool, gate: &BodyGate) -> (Module, Option<FuncId>, FuncId) {
    let mut mb = ModuleBuilder::new_with_target_info("clean_backend_tv_fragment5", target());
    mb.set_default_producer(Producer::Clean);
    let inc = fragment2.then(|| add_fragment2_root(&mut mb));
    let root = add_boxed_constant(&mut mb, boxed);
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    for func in m.functions.iter_mut().filter(|f| !f.blocks.is_empty()) {
        func.body_gate = Some(gate.clone());
    }
    (m, inc, root)
}

fn gated() -> BodyGate {
    BodyGate::Gated {
        authority: KERNEL_TV.to_string(),
        evidence: None,
    }
}

/// Mint (with the PUBLIC minter) and attach the TV certificate of `function`
/// as obligation `id`.
fn certify(m: &mut Module, id: u32, function: FuncId) {
    let (_node, obligation, certificate) = certify_identity_lineage_rung(
        m,
        ProofLineageId::new(id),
        ProofId::new(id),
        transform(),
        function,
    )
    .expect("the fixture function is in the backend-TV fragment");
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(certificate);
}

/// The certificate Clean minted for a Fragment-5 constant before d9f760a4d,
/// as far as trust-ir can tell: the `clean_backend_tv` certificate whose
/// comparand is the boxed body's denotation (`256`). trust-ir cannot mint it
/// for the `Ptr` body (see below), so it is minted on the scalar twin, whose
/// denotation is that same `Nat`, and moved onto the boxed body — the same
/// function name, id and obligation.
fn graft_fragment5_certificate(boxed: &mut Module, fragment2: bool, id: u32) {
    let (mut twin, _, twin_root) = module(fragment2, false, &gated());
    certify(&mut twin, id, twin_root);
    let obligation = twin.proof_obligations.pop().expect("minted obligation");
    let certificate = twin.proof_certificates.pop().expect("minted certificate");
    boxed.proof_obligations.push(obligation);
    boxed.proof_certificates.push(certificate);
}

fn refused_by_name(errors: &[ValidationError], obligation: u32, needle: &str) -> bool {
    errors.iter().any(|error| {
        matches!(
            error,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: o, reason }
                if *o == obligation && reason.contains(needle)
        )
    })
}

fn names_obligation(error: &ValidationError, obligation: u32) -> bool {
    matches!(
        error,
        ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: o, .. } if *o == obligation
    )
}

#[test]
fn clean_backend_tv_refuses_a_boxed_nat_ptr_return() {
    // CONTROL: the certificate is honest. On the scalar twin it certifies,
    // under the same `Gated{"clean-kernel-tv"}` license.
    let (mut twin, _, twin_root) = module(false, false, &gated());
    certify(&mut twin, 0, twin_root);
    let errors = validate_module(&twin);
    assert!(
        errors.is_empty(),
        "the scalar twin's certificate must certify, got: {errors:?}"
    );

    // The boxed-Nat `() -> Ptr` body with that certificate: refused by name,
    // on the RETURN SORT, before any kernel judgment.
    let (mut boxed, _, root) = module(false, true, &gated());
    assert_eq!(
        boxed.function_by_id(root).map(|f| f.name.as_str()),
        Some(ROOT),
        "the certificate names the same function"
    );
    graft_fragment5_certificate(&mut boxed, false, 0);
    let errors = validate_module(&boxed);
    assert!(
        refused_by_name(&errors, 0, PTR_RETURN_REFUSAL),
        "a Fragment-5 `() -> Ptr` certificate must be refused on its Ptr return, got: {errors:?}"
    );

    // trust-ir's own minter refuses to mint for it, for the same reason.
    let (unminted, _, root) = module(false, true, &gated());
    let refusal = certify_identity_lineage_rung(
        &unminted,
        ProofLineageId::new(0),
        ProofId::new(0),
        transform(),
        root,
    )
    .expect_err("the public minter must not mint a Fragment-5 certificate");
    assert!(
        refusal.contains(PTR_RETURN_REFUSAL),
        "the minter's refusal must name the Ptr return, got: {refusal}"
    );
}

#[test]
fn a_fragment5_certificate_refuses_the_module_with_its_certified_fragment2_root() {
    // What Clean minted before d9f760a4d: a certified Fragment-2 root beside a
    // certified Fragment-5 constant, both `Gated`.
    let (mut m, inc, root) = module(true, true, &gated());
    let inc = inc.expect("the Fragment-2 root");
    certify(&mut m, 0, inc);
    graft_fragment5_certificate(&mut m, true, 1);
    assert_eq!(m.proof_obligations[1].function, Some(root));
    let errors = validate_module(&m);
    assert!(
        refused_by_name(&errors, 1, PTR_RETURN_REFUSAL),
        "the Fragment-5 certificate must be refused on its Ptr return, got: {errors:?}"
    );
    assert!(
        !errors.iter().any(|e| names_obligation(e, 0)),
        "the Fragment-2 root's own certificate is sound; the module is refused for the Ptr row \
         alone, got: {errors:?}"
    );

    // What Clean emits since d9f760a4d (`FRAGMENT5_NOT_MINTED`): the Fragment-5
    // constant carries no obligation and an `Ungated` license. The module
    // validates with the Fragment-2 root certified; codegen refuses the
    // constant alone, by name (Clean's recorded residual: Fragment-5 codegen
    // coverage is nil until trust-ir mirrors the fragment).
    let (mut m, inc, root) = module(true, true, &gated());
    certify(&mut m, 0, inc.expect("the Fragment-2 root"));
    m.function_by_id_mut(root)
        .expect("the Fragment-5 constant")
        .body_gate = Some(BodyGate::Ungated);
    let errors = validate_module(&m);
    assert!(
        errors.is_empty(),
        "the not-minted shape must validate, with the Fragment-2 root certified, got: {errors:?}"
    );
    let codegen = validate_module_for_codegen(&m);
    assert!(
        matches!(
            codegen.as_slice(),
            [ValidationError::UngatedBodyForCodegen { function, .. }] if *function == root.index()
        ),
        "codegen must refuse the Ungated Fragment-5 constant and nothing else, got: {codegen:?}"
    );

    // And a `Gated` license on the constant with NO certificate behind it is
    // not an escape: well-formedness does not read the license, but the
    // codegen license layer requires `clean-kernel-tv` to be backed by the
    // body's own re-checked certificate, which trust-ir cannot give a Ptr
    // return.
    let (mut m, inc, root) = module(true, true, &gated());
    certify(&mut m, 0, inc.expect("the Fragment-2 root"));
    assert_eq!(validate_module(&m), []);
    let codegen = validate_module_for_codegen(&m);
    assert!(
        matches!(
            codegen.as_slice(),
            [ValidationError::GatedWithoutEvidence { function, authority, .. }]
                if *function == root.index() && authority == KERNEL_TV
        ),
        "a Gated{{\"clean-kernel-tv\"}} Fragment-5 body without a certificate must be refused \
         for codegen, by name, got: {codegen:?}"
    );
}
