// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `clean_backend_tv` composition (roadmap WS1.4, finding F-005): every call
//! edge of a kernel-certified caller is bound to the callee ACTUALLY called.
//!
//! A Fragment-3b statement is parametric in its callees, so the kernel's
//! verdict on the caller says nothing about which function each `Call`
//! reaches. The composition post-pass of `validate_certified_evidence`
//! requires (a) one `InheritedFromCallee` row per called function and no row
//! for a function the body does not call, (b) each row to cite the callee's
//! OWN kernel-rechecked `clean_backend_tv` obligation, (c) no cross-crate row at
//! this tier, and (d) an acyclic composition graph.
//!
//! Fixtures are minted with the PUBLIC `certify_identity_lineage_rung`, the way
//! the c04 reproduction did:
//!
//! ```text
//! plus(a,b)  = a*b + a     fn#0
//! minus(a,b) = a*b - a     fn#1
//! top(a,b)   = plus(a,b) + 7   fn#2
//! ```
//!
//! Tests whose name starts `b3_` / `verify_c04_` are the in-repo ports of the
//! two-language proof program's ratchet rows of the same id (dots and dashes
//! spelled `_`); WS8.6 folds them into the conformance ratchet table.

use trust_ir::constant::Constant;
use trust_ir::inst::BinOp;
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::proof::{
    ObligationKind, ProofCertificate, ProofDigest, ProofEvidence, ProofFormula, ProofLineageId,
    ProofLineageManifest, ProofObligation, ProofStatus, ProofTransform, ProofTransformStage,
    RejectingModuleProofAuthority,
};
use trust_ir::ty::Ty;
use trust_ir::value::{ImportId, ProofId};
use trust_ir::{BodyGate, ExternRef, FuncId, Inst, Module, ModuleImport, Producer};
use trust_ir_build::{
    ModuleBuilder, ModuleSet, ValidationError, certify_identity_lineage_rung,
    lineage_closed_with_validated_authority, validate_changed, validate_linked_module,
    validate_module, validate_module_for_codegen, validate_module_report,
    validate_module_with_authority, validate_module_with_config,
};

const PLUS: usize = 0;
const MINUS: usize = 1;
const TOP: usize = 2;

/// `plus`, `minus`, and a caller built by `body` over them. All U64, Clean
/// producer, gated by the Clean kernel-TV authority.
fn module_with_caller(
    name: &str,
    caller: &str,
    body: impl FnOnce(
        &mut trust_ir_build::FunctionBuilder<'_>,
        FuncId,
        FuncId,
        [trust_ir::ValueId; 2],
    ) -> trust_ir::ValueId,
) -> Module {
    let mut mb = ModuleBuilder::new(name);
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
    let minus = leaf(&mut mb, "minus", BinOp::Sub);
    let mut f = mb.function(caller, sig);
    let e = f.create_block();
    let a = f.add_block_param(e, Ty::U64);
    let b = f.add_block_param(e, Ty::U64);
    f.switch_to_block(e);
    let r = body(&mut f, plus, minus, [a, b]);
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

/// `top(a,b) = plus(a,b) + 7`.
fn base_module() -> Module {
    module_with_caller("tv_callee_binding", "top", |f, plus, _minus, [a, b]| {
        let c = f.call(plus, vec![a, b]);
        let k = f.iconst(Ty::U64, 7);
        f.add(Ty::U64, c, k)
    })
}

/// `two(a,b) = plus(a,b) - minus(a,b)` — two distinct callees.
fn two_callee_module() -> Module {
    module_with_caller("tv_two_callees", "two", |f, plus, minus, [a, b]| {
        let p = f.call(plus, vec![a, b]);
        let q = f.call(minus, vec![a, b]);
        f.sub(Ty::U64, p, q)
    })
}

fn transform() -> ProofTransform {
    ProofTransform::new(
        ProofTransformStage::Frontend,
        "identity",
        "tv-callee-binding",
        "1.0.0",
    )
}

/// Certify every function in `functions` (in order) with the public minter;
/// obligation `i` belongs to `functions[i]`. Returns the lineage manifest.
fn certify(m: &mut Module, functions: &[usize]) -> ProofLineageManifest {
    let mut nodes = Vec::new();
    for (i, &function) in functions.iter().enumerate() {
        let id = u32::try_from(i).expect("small fixture");
        let (node, obligation, certificate) = certify_identity_lineage_rung(
            m,
            ProofLineageId::new(id),
            ProofId::new(id),
            transform(),
            m.functions[function].id,
        )
        .expect("fixture function is in the backend-TV fragment");
        m.proof_obligations.push(obligation);
        m.proof_certificates.push(certificate);
        nodes.push(node);
    }
    ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        roots: nodes.iter().map(|n| n.id).collect(),
        nodes,
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

/// The honest A0 module: `plus` certified (obligation 0), `top` certified
/// (obligation 1) and grounded by `InheritedFromCallee{plus, #0}`, and the
/// uncalled `minus` certified too (obligation 2): every body of the fixture
/// wears `Gated{"clean-kernel-tv"}`, and since WS1.5 that license must be
/// backed by the body's own kernel-rechecked TV certificate, as an honest
/// Clean producer stamps it.
fn a0() -> (Module, ProofLineageManifest) {
    let mut m = base_module();
    let manifest = certify(&mut m, &[PLUS, TOP, MINUS]);
    let plus = m.functions[PLUS].id;
    m.proof_certificates.push(inherit(1, plus, 0));
    (m, manifest)
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

/// The composition refusal on `obligation` whose reason contains `needle`.
fn has_refusal(errors: &[ValidationError], obligation: u32, needle: &str) -> bool {
    errors.iter().any(|error| {
        matches!(
            error,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: o, reason }
                if *o == obligation && reason.contains(needle)
        )
    })
}

/// Every in-process layer c04 probed, as `(layer, errors)`.
fn layers(m: &Module) -> Vec<(&'static str, Vec<ValidationError>)> {
    let ids: Vec<FuncId> = m.functions.iter().map(|f| f.id).collect();
    let empty = ModuleSet::new(Vec::<&Module>::new());
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
        ("validate_changed", validate_changed(m, &ids)),
        (
            "validate_linked_module",
            validate_linked_module(m, &empty, &RejectingModuleProofAuthority)
                .errors()
                .to_vec(),
        ),
    ]
}

// ---------------------------------------------------------------------------
// Positive
// ---------------------------------------------------------------------------

#[test]
fn a0_grounded_caller_certifies_on_every_layer() {
    let (m, manifest) = a0();
    for (layer, errors) in layers(&m) {
        assert!(errors.is_empty(), "A0 must certify on {layer}: {errors:?}");
    }
    assert_eq!(
        validate_module_report(&m)
            .replayed_certificate_refs()
            .map(|refs| refs.len()),
        Some(3),
        "all three TV certificates are kernel-tier authority"
    );
    lineage_closed_with_validated_authority(&m, &manifest).expect("A0 lineage closes");
    assert_eq!(run(&m, "top", 20, 15), 20 * 15 + 20 + 7);
}

#[test]
fn honest_two_callee_module_certifies() {
    let mut m = two_callee_module();
    certify(&mut m, &[PLUS, MINUS, TOP]);
    let (plus, minus) = (m.functions[PLUS].id, m.functions[MINUS].id);
    m.proof_certificates.push(inherit(2, plus, 0));
    m.proof_certificates.push(inherit(2, minus, 1));
    let errors = validate_module(&m);
    assert!(errors.is_empty(), "{errors:?}");
}

// ---------------------------------------------------------------------------
// Negative twins
// ---------------------------------------------------------------------------

/// A2 — the c04 face: the call is retargeted plus→minus and the inheritance
/// row is left alone. Every layer refuses, for the named reasons.
#[test]
fn a2_retargeted_call_is_refused_on_every_layer() {
    let (mut m, manifest) = a0();
    let minus = m.functions[MINUS].id;
    retarget_all_calls(&mut m, TOP, minus);
    assert_eq!(
        run(&m, "top", 20, 15),
        20 * 15 - 20 + 7,
        "the retarget changes behaviour"
    );
    for (layer, errors) in layers(&m) {
        assert!(
            has_refusal(
                &errors,
                1,
                "callee `minus` (fn#1) is called by `top` but no InheritedFromCallee row on \
                 obligation #1 names it"
            ),
            "{layer} must refuse the unrowed call edge: {errors:?}"
        );
        assert!(
            has_refusal(
                &errors,
                1,
                "InheritedFromCallee row names `plus` (fn#0), which `top` never calls"
            ),
            "{layer} must refuse the row naming an uncalled function: {errors:?}"
        );
    }
    // All-or-nothing: the kernel-tier authority set is emptied, so the lineage
    // no longer closes either.
    assert!(lineage_closed_with_validated_authority(&m, &manifest).is_err());
}

/// B0 — the caller is certified and the callee is not, with no inheritance row.
#[test]
fn b0_caller_without_inheritance_row_is_refused() {
    let mut m = base_module();
    certify(&mut m, &[TOP]);
    let errors = validate_module(&m);
    assert!(
        has_refusal(
            &errors,
            0,
            "callee `plus` (fn#0) is called by `top` but no InheritedFromCallee row on \
             obligation #0 names it"
        ),
        "{errors:?}"
    );
}

/// The row names the certified `minus`; the body calls `plus`.
#[test]
fn row_naming_a_certified_but_uncalled_callee_is_refused() {
    let mut m = base_module();
    certify(&mut m, &[PLUS, MINUS, TOP]);
    let minus = m.functions[MINUS].id;
    m.proof_certificates.push(inherit(2, minus, 1));
    let errors = validate_module(&m);
    assert!(
        has_refusal(
            &errors,
            2,
            "InheritedFromCallee row names `minus` (fn#1), which `top` never calls"
        ),
        "{errors:?}"
    );
    assert!(
        has_refusal(&errors, 2, "callee `plus` (fn#0) is called by `top` but no"),
        "{errors:?}"
    );
}

/// The callee is "certified", but by a contract anchor, not by its own
/// `clean_backend_tv` equation. Before WS1.4 the B5 validator accepted this row
/// (the cited obligation is kernel-ground and scoped to the callee).
#[test]
fn callee_certified_by_a_non_tv_anchor_does_not_ground_the_call() {
    let mut m = base_module();
    let plus = m.functions[PLUS].id;
    let contract = ProofObligation::new(
        ProofId::new(0),
        ObligationKind::Postcondition,
        ProofStatus::Certified,
        "a true contract about plus, not its translation",
    )
    .with_function(plus)
    .with_formula(ProofFormula::smtlib2("(= 1 1)", "Bool"));
    let certificate = trust_ir::clean_expr_lowering::contract::contract_clean_cic_certificate(
        &contract,
        "contract-prover",
    )
    .expect("the contract is kernel-provable");
    m.proof_obligations.push(contract);
    m.proof_certificates.push(certificate);
    // `top`'s TV is obligation #1.
    let (_node, obligation, certificate) = certify_identity_lineage_rung(
        &m,
        ProofLineageId::new(1),
        ProofId::new(1),
        transform(),
        m.functions[TOP].id,
    )
    .expect("top is in fragment");
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(certificate);
    m.proof_certificates.push(inherit(1, plus, 0));

    // Control: without the TV caller the contract itself validates, so the
    // refusal below is about composition, not the contract.
    let mut control = m.clone();
    control.proof_obligations.truncate(1);
    control.proof_certificates.truncate(1);
    assert!(validate_module(&control).is_empty());

    let errors = validate_module(&m);
    assert!(
        has_refusal(
            &errors,
            1,
            "callee `plus` (fn#0) has no kernel-rechecked clean_backend_tv obligation of its own"
        ),
        "{errors:?}"
    );
}

/// `f(a,b) = f(a,b) + 1` passes its own parametric recheck; grounding its call
/// at its own TV is circular and refused by the cycle rule.
#[test]
fn self_recursive_composition_is_refused_as_a_cycle() {
    let mut mb = ModuleBuilder::new("tv_self_recursive");
    mb.set_default_producer(Producer::Clean);
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let self_id = mb
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    let mut f = mb.function("f", sig);
    let e = f.create_block();
    let a = f.add_block_param(e, Ty::U64);
    let b = f.add_block_param(e, Ty::U64);
    f.switch_to_block(e);
    let c = f.call(self_id, vec![a, b]);
    let one = f.iconst(Ty::U64, 1);
    let r = f.add(Ty::U64, c, one);
    f.ret(vec![r]);
    f.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    certify(&mut m, &[0]);
    m.proof_certificates.push(inherit(0, self_id, 0));
    let errors = validate_module(&m);
    assert!(
        has_refusal(
            &errors,
            0,
            "clean_backend_tv composition cycle: f → f; recursive composition is not grounded"
        ),
        "{errors:?}"
    );
}

/// Mutual recursion `top → g → top`, each grounded at the other's TV.
#[test]
fn mutually_recursive_composition_is_refused_as_a_cycle() {
    let mut mb = ModuleBuilder::new("tv_mutual");
    mb.set_default_producer(Producer::Clean);
    let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let g_id = mb
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    let top_id = FuncId::new(g_id.index() + 1);
    let mut g = mb.function("g", sig);
    let e = g.create_block();
    let a = g.add_block_param(e, Ty::U64);
    g.switch_to_block(e);
    let c = g.call(top_id, vec![a]);
    g.ret(vec![c]);
    g.build();
    assert_eq!(
        mb.peek_next_func_id()
            .expect("peek_next_func_id: test fixture"),
        top_id
    );
    let mut top = mb.function("top", sig);
    let e = top.create_block();
    let a = top.add_block_param(e, Ty::U64);
    top.switch_to_block(e);
    let c = top.call(g_id, vec![a]);
    top.ret(vec![c]);
    top.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    certify(&mut m, &[0, 1]);
    m.proof_certificates.push(inherit(0, top_id, 1));
    m.proof_certificates.push(inherit(1, g_id, 0));
    let errors = validate_module(&m);
    assert!(
        has_refusal(
            &errors,
            1,
            "clean_backend_tv composition cycle: top → g → top; recursive composition is not \
             grounded"
        ),
        "{errors:?}"
    );
    assert!(
        has_refusal(
            &errors,
            0,
            "clean_backend_tv composition cycle: g → top → g"
        ),
        "{errors:?}"
    );
}

/// Two rows for one call edge.
#[test]
fn duplicate_rows_for_one_callee_are_refused() {
    let (mut m, _) = a0();
    let plus = m.functions[PLUS].id;
    m.proof_certificates.push(inherit(1, plus, 0));
    let errors = validate_module(&m);
    assert!(
        has_refusal(
            &errors,
            1,
            "two InheritedFromCallee rows on obligation #1 name callee `plus` (fn#0)"
        ),
        "{errors:?}"
    );
}

/// A cross-crate (`external: Some`) row never grounds a kernel-tier TV call
/// edge.
#[test]
fn cross_crate_row_on_a_tv_obligation_is_refused() {
    let (mut m, _) = a0();
    let plus = m.functions[PLUS].id;
    m.imports.push(ModuleImport {
        name: "dep".to_string(),
        digest: ProofDigest::sha256_domain("tv-callee-binding.test", b"dep"),
        producer: Some(Producer::Clean),
        scheme: trust_ir::IdentityScheme::V2,
    });
    let last = m.proof_certificates.len() - 1;
    m.proof_certificates[last].evidence = ProofEvidence::InheritedFromCallee {
        callee: plus,
        obligation: ProofId::new(0),
        external: Some(ExternRef {
            module: ImportId::new(0),
            symbol: "plus".to_string(),
            obligation: Some(ProofId::new(0)),
        }),
    };
    let errors = validate_module(&m);
    assert!(
        has_refusal(
            &errors,
            1,
            "cross-crate TV composition is authenticated only by validate_linked_module"
        ),
        "{errors:?}"
    );
}

// ---------------------------------------------------------------------------
// Mutation controls
// ---------------------------------------------------------------------------

/// D1 — retarget to a DIFFERENT-ARITY callee: the kernel refuses (unchanged).
#[test]
fn d1_different_arity_retarget_stays_refused_by_the_kernel() {
    let (mut m, _) = a0();
    let sig = m
        .add_func_type(trust_ir::FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let fid = FuncId::new(u32::try_from(m.functions.len()).expect("small"));
    let mut unary = trust_ir::Function::new(fid, "unary", sig, trust_ir::BlockId::new(0));
    unary.producer = Some(Producer::Clean);
    unary.body_gate = Some(BodyGate::Gated {
        authority: "clean-kernel-tv".into(),
        evidence: None,
    });
    let mut block = trust_ir::Block::new(trust_ir::BlockId::new(0));
    block.params.push((trust_ir::ValueId::new(0), Ty::U64));
    block.body.push(trust_ir::InstrNode::new(Inst::Return {
        values: vec![trust_ir::ValueId::new(0)],
    }));
    unary.blocks.push(block);
    m.try_add_function(unary)
        .expect("Module::try_add_function: test fixture");
    for node in &mut m.functions[TOP].blocks[0].body {
        if let Inst::Call { callee, args } = &mut node.inst {
            *callee = fid;
            args.truncate(1);
        }
    }
    let errors = validate_module(&m);
    assert!(
        has_refusal(&errors, 1, "in-process kernel REJECTED"),
        "{errors:?}"
    );
}

/// e2 — with two distinct callees, swapping which call goes where is refused
/// by the kernel (the rows are untouched and still cover both callees).
#[test]
fn e2_role_swap_between_two_callees_stays_refused_by_the_kernel() {
    let mut m = two_callee_module();
    certify(&mut m, &[PLUS, MINUS, TOP]);
    let (plus, minus) = (m.functions[PLUS].id, m.functions[MINUS].id);
    m.proof_certificates.push(inherit(2, plus, 0));
    m.proof_certificates.push(inherit(2, minus, 1));
    let mut swapped = 0;
    for node in &mut m.functions[TOP].blocks[0].body {
        if let Inst::Call { callee, .. } = &mut node.inst {
            *callee = if *callee == plus { minus } else { plus };
            swapped += 1;
        }
    }
    assert_eq!(swapped, 2);
    let errors = validate_module(&m);
    assert!(
        has_refusal(&errors, 2, "in-process kernel REJECTED"),
        "{errors:?}"
    );
    assert!(
        !has_refusal(&errors, 2, "InheritedFromCallee row"),
        "the rows still cover both callees; only the kernel refuses: {errors:?}"
    );
}

/// PINNED fail-closed limitation: a pure RENAME that changes the name-sorted
/// telescope order refuses an honest certificate (callee identity in the
/// statement is still only the name-sort rank). Program behaviour is
/// unchanged.
#[test]
fn rename_changing_callee_rank_is_still_refused() {
    let mut m = two_callee_module();
    certify(&mut m, &[PLUS, MINUS, TOP]);
    let (plus, minus) = (m.functions[PLUS].id, m.functions[MINUS].id);
    m.proof_certificates.push(inherit(2, plus, 0));
    m.proof_certificates.push(inherit(2, minus, 1));
    let before = run(&m, "two", 20, 15);
    m.functions[PLUS].name = "aa_plus".to_string();
    assert_eq!(
        run(&m, "two", 20, 15),
        before,
        "a rename changes no behaviour"
    );
    let errors = validate_module(&m);
    assert!(
        has_refusal(&errors, 2, "in-process kernel REJECTED"),
        "{errors:?}"
    );
}

/// FLIPPED (closed by WS1.12a, F-005 residual): the CONSISTENT edit — retarget
/// the call AND rewrite the inheritance row to an honestly certified `minus` of
/// the same arity and name rank — was ACCEPTED because the statement is
/// callee-agnostic and the certificate recorded no callee list. A BOUND
/// certificate (`CertificateBinding.callees`, minted by
/// `certify_identity_lineage_rung_bound`) lists `["plus"]`, the re-derived
/// statement quantifies over `["minus"]`, and the mismatch is refused by name
/// as `CertificateBindingMismatch { field: "callees" }`. The legacy UNBOUND
/// form stays accepted by the default lanes (nothing to compare) and is
/// refused under `ValidationConfig::with_bound_certificates(true)` — the
/// disclosed residual for pre-binding certificates. The full twin set lives
/// in `certificate_binding.rs`.
#[test]
fn b3_gap_composition_consistent_retarget_to_certified_callee() {
    use trust_ir_build::{ValidationConfig, certify_identity_lineage_rung_bound};
    let mut m = base_module();
    for (i, &function) in [PLUS, MINUS, TOP].iter().enumerate() {
        let id = u32::try_from(i).expect("small fixture");
        let (_, obligation, certificate) = certify_identity_lineage_rung_bound(
            &m,
            ProofLineageId::new(id),
            ProofId::new(id),
            transform(),
            m.functions[function].id,
        )
        .expect("fixture function is in the backend-TV fragment");
        m.proof_obligations.push(obligation);
        m.proof_certificates.push(certificate);
    }
    let (plus, minus) = (m.functions[PLUS].id, m.functions[MINUS].id);
    m.proof_certificates.push(inherit(2, plus, 0));
    assert!(
        validate_module(&m).is_empty(),
        "honest bound baseline certifies"
    );
    let before = run(&m, "top", 20, 15);

    retarget_all_calls(&mut m, TOP, minus);
    let last = m.proof_certificates.len() - 1;
    m.proof_certificates[last] = inherit(2, minus, 1);

    let errors = validate_module(&m);
    let strict = validate_module_with_authority(&m, &RejectingModuleProofAuthority);
    let after = run(&m, "top", 20, 15);
    assert_eq!((before, after), (327, 287));
    for errors in [&errors, &strict] {
        assert!(
            errors.iter().any(|e| matches!(
                e,
                ValidationError::CertificateBindingMismatch { obligation: 2, field, .. }
                    if field == "callees"
            )),
            "the consistent retarget is refused by the callee binding: {errors:?}"
        );
    }

    // The legacy unbound certificates: accepted by the default lane, refused
    // under the strict policy.
    let mut legacy = base_module();
    certify(&mut legacy, &[PLUS, MINUS, TOP]);
    legacy.proof_certificates.push(inherit(2, plus, 0));
    retarget_all_calls(&mut legacy, TOP, minus);
    let last = legacy.proof_certificates.len() - 1;
    legacy.proof_certificates[last] = inherit(2, minus, 1);
    assert!(validate_module(&legacy).is_empty());
    let refused = validate_module_with_config(
        &legacy,
        &ValidationConfig::pinned().with_bound_certificates(true),
    )
    .into_errors();
    assert!(
        refused
            .iter()
            .all(|e| matches!(e, ValidationError::UnboundCertificate { .. }))
            && refused.len() == 3,
        "{refused:?}"
    );
}

// ---------------------------------------------------------------------------
// Ported proof-program rows (now CLOSED)
// ---------------------------------------------------------------------------

/// `twice(a,b) = addmul(addmul(a,b), b)` beside the same-signature decoy
/// `submul` — the proof program's `composition_with_decoy` fixture.
/// Obligation 0 = `addmul` (when certified), the last = `twice`.
fn composition_with_decoy(certify_callee: bool) -> (Module, FuncId, FuncId, FuncId, u32) {
    let mut mb = ModuleBuilder::new("b3_compose_decoy");
    mb.set_default_producer(Producer::Clean);
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let leaf = |mb: &mut ModuleBuilder, name: &str, op: BinOp| {
        let mut f = mb.function(name, sig);
        let e = f.create_block();
        let a = f.add_block_param(e, Ty::U64);
        let b = f.add_block_param(e, Ty::U64);
        f.switch_to_block(e);
        let ab = f.mul(Ty::U64, a, b);
        let out = f.binop(op, Ty::U64, ab, a);
        f.ret(vec![out]);
        f.build()
    };
    let addmul = leaf(&mut mb, "addmul", BinOp::Add);
    let submul = leaf(&mut mb, "submul", BinOp::Sub);
    let twice = mb
        .peek_next_func_id()
        .expect("peek_next_func_id: test fixture");
    let mut f = mb.function("twice", sig);
    let e = f.create_block();
    let a = f.add_block_param(e, Ty::U64);
    let b = f.add_block_param(e, Ty::U64);
    f.switch_to_block(e);
    let inner = f.call(addmul, vec![a, b]);
    let outer = f.call(addmul, vec![inner, b]);
    f.ret(vec![outer]);
    f.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    for func in &mut m.functions {
        func.body_gate = Some(BodyGate::Gated {
            authority: "clean-kernel-tv".to_string(),
            evidence: None,
        });
    }
    let functions: &[usize] = if certify_callee { &[0, 2] } else { &[2] };
    certify(&mut m, functions);
    let twice_obligation = u32::try_from(functions.len() - 1).expect("small");
    (m, addmul, submul, twice, twice_obligation)
}

/// Row `b3.gap.composition.callee_need_not_be_certified` — CLOSED: a caller
/// whose callee carries no certificate and no inheritance row is refused.
#[test]
fn b3_gap_composition_callee_need_not_be_certified() {
    let (m, _, _, _, twice_obligation) = composition_with_decoy(false);
    let errors = validate_module(&m);
    let strict = validate_module_with_authority(&m, &RejectingModuleProofAuthority);
    let codegen = validate_module_for_codegen(&m);
    for (layer, errors) in [
        ("validate_module", &errors),
        ("with_authority", &strict),
        ("for_codegen", &codegen),
    ] {
        assert!(
            has_refusal(
                errors,
                twice_obligation,
                "callee `addmul` (fn#0) is called by `twice` but no InheritedFromCallee row"
            ),
            "{layer}: {errors:?}"
        );
    }
}

/// Row `b3.gap.composition.call_retargeting_not_detected` — CLOSED: with
/// `addmul` certified and `twice` minted, retargeting every call to `submul`
/// is refused (there is no row for the new callee).
#[test]
fn b3_gap_composition_call_retargeting_not_detected() {
    let (mut m, addmul, submul, _, twice_obligation) = composition_with_decoy(true);
    m.proof_certificates
        .push(inherit(twice_obligation, addmul, 0));
    assert!(
        validate_module(&m).is_empty(),
        "grounded baseline certifies"
    );
    assert_eq!(run(&m, "twice", 6, 7), 384);
    retarget_all_calls(&mut m, 2, submul);
    assert_eq!(run(&m, "twice", 6, 7), 216);
    let errors = validate_module(&m);
    let strict = validate_module_with_authority(&m, &RejectingModuleProofAuthority);
    let codegen = validate_module_for_codegen(&m);
    for (layer, errors) in [
        ("validate_module", &errors),
        ("with_authority", &strict),
        ("for_codegen", &codegen),
    ] {
        assert!(
            has_refusal(
                errors,
                twice_obligation,
                "callee `submul` (fn#1) is called by `twice` but no InheritedFromCallee row"
            ),
            "{layer}: {errors:?}"
        );
    }
}

/// Row `b3.gap.composition.inherited_callee_not_compared_with_called_callee`
/// — CLOSED: the inheritance row is compared with the callee actually called.
#[test]
fn b3_gap_composition_inherited_callee_not_compared_with_called_callee() {
    let (mut m, addmul, submul, _, twice_obligation) = composition_with_decoy(true);
    m.proof_certificates
        .push(inherit(twice_obligation, addmul, 0));
    retarget_all_calls(&mut m, 2, submul);
    let errors = validate_module(&m);
    assert!(
        has_refusal(
            &errors,
            twice_obligation,
            "InheritedFromCallee row names `addmul` (fn#0), which `twice` never calls"
        ),
        "{errors:?}"
    );
}

/// Rows `verify.c04.L1` / `verify.c04.L2` (both lenses) — CLOSED: the
/// single-callee retarget of c04 is refused on every in-process layer; the
/// CLI half lives in `trust-ir-cli/tests/cli_lineage.rs`.
#[test]
fn verify_c04_single_callee_retarget_is_refused() {
    let (mut m, _) = a0();
    let before_digest = m.stable_digest();
    let minus = m.functions[MINUS].id;
    retarget_all_calls(&mut m, TOP, minus);
    assert_ne!(m.stable_digest(), before_digest);
    for (layer, errors) in layers(&m) {
        assert!(
            errors.iter().any(|e| matches!(
                e,
                ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 1, .. }
            )),
            "{layer}: {errors:?}"
        );
    }
}

/// Row `b3.gap.tv_certificate_not_bound_to_producer` — re-labelled a
/// DOCUMENTED PROPERTY under the F-016 decision (A): the `clean_backend_tv`
/// anchor is producer-agnostic. The equation is about the emitted body, and
/// `Function.producer` is claim-style provenance; identity binding is the
/// call-edge rule above and WS1.13's job. Relabelling keeps Certified.
#[test]
fn b3_tv_certificate_not_bound_to_producer_is_a_documented_property() {
    let (mut m, _) = a0();
    for function in &mut m.functions {
        function.producer = Some(Producer::TRust);
    }
    let errors = validate_module(&m);
    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(
        validate_module_report(&m)
            .replayed_certificate_refs()
            .map(|refs| refs.len()),
        Some(3)
    );
}

#[test]
fn constant_fixture_sanity() {
    // Guards the fixture shape the tests index into.
    let m = base_module();
    assert_eq!(m.functions[PLUS].name, "plus");
    assert_eq!(m.functions[MINUS].name, "minus");
    assert_eq!(m.functions[TOP].name, "top");
    assert!(m.functions[TOP].blocks[0].body.iter().any(|node| matches!(
        node.inst,
        Inst::Const {
            value: Constant::Int(7),
            ..
        }
    )));
}

// ---------------------------------------------------------------------------
// Review adversaries (modules the rule's author did not write)
// ---------------------------------------------------------------------------

/// Legitimate DAG with a SHARED callee: `leaf(a,b) = a*b + a`,
/// `mid(a,b) = leaf(a,b) + 1`, `top(a,b) = mid(a,b) - leaf(a,b)`. `leaf` is
/// reached twice (directly and through `mid`); the cycle rule must not mistake
/// a re-convergent DAG for a cycle.
#[test]
fn review_shared_callee_dag_certifies() {
    let mut mb = ModuleBuilder::new("tv_dag");
    mb.set_default_producer(Producer::Clean);
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut f = mb.function("leaf", sig);
    let e = f.create_block();
    let a = f.add_block_param(e, Ty::U64);
    let b = f.add_block_param(e, Ty::U64);
    f.switch_to_block(e);
    let p = f.mul(Ty::U64, a, b);
    let r = f.add(Ty::U64, p, a);
    f.ret(vec![r]);
    let leaf = f.build();
    let mut f = mb.function("mid", sig);
    let e = f.create_block();
    let a = f.add_block_param(e, Ty::U64);
    let b = f.add_block_param(e, Ty::U64);
    f.switch_to_block(e);
    let c = f.call(leaf, vec![a, b]);
    let one = f.iconst(Ty::U64, 1);
    let r = f.add(Ty::U64, c, one);
    f.ret(vec![r]);
    let mid = f.build();
    let mut f = mb.function("top", sig);
    let e = f.create_block();
    let a = f.add_block_param(e, Ty::U64);
    let b = f.add_block_param(e, Ty::U64);
    f.switch_to_block(e);
    let x = f.call(mid, vec![a, b]);
    let y = f.call(leaf, vec![a, b]);
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
    certify(&mut m, &[0, 1, 2]);
    m.proof_certificates.push(inherit(1, leaf, 0));
    m.proof_certificates.push(inherit(2, mid, 1));
    m.proof_certificates.push(inherit(2, leaf, 0));
    for (layer, errors) in layers(&m) {
        assert!(
            errors.is_empty(),
            "shared-callee DAG on {layer}: {errors:?}"
        );
    }
    assert_eq!(run(&m, "top", 20, 15), 1);
    // Mutation control: drop `mid`'s own grounding row; the DAG no longer
    // bottoms out and `mid` (obligation #1) is refused by name.
    let position = m
        .proof_certificates
        .iter()
        .position(|c| {
            c.obligation == ProofId::new(1)
                && matches!(c.evidence, ProofEvidence::InheritedFromCallee { .. })
        })
        .expect("mid's row");
    m.proof_certificates.remove(position);
    assert!(
        has_refusal(
            &validate_module(&m),
            1,
            "callee `leaf` (fn#0) is called by `mid` but no InheritedFromCallee row"
        ),
        "dropping mid's row must be refused"
    );
}

/// The row names the called `plus` but cites the CALLER's own TV obligation
/// (which is in `K`, but is not about `plus`).
#[test]
fn review_row_citing_the_callers_own_obligation_is_refused() {
    let (mut m, _) = a0();
    let last = m.proof_certificates.len() - 1;
    m.proof_certificates[last] = inherit(1, m.functions[PLUS].id, 1);
    let errors = validate_module(&m);
    assert!(
        has_refusal(
            &errors,
            1,
            "callee `plus` (fn#0) has no kernel-rechecked clean_backend_tv obligation of its own: \
             the InheritedFromCallee row on obligation #1 cites obligation #1"
        ),
        "{errors:?}"
    );
}

/// The callee's TV obligation carries the honest CleanCic payload but is
/// labelled `Discharged`, not `Certified`: it was never kernel-rechecked, so it
/// is not in `K` and cannot ground a Certified caller.
#[test]
fn review_callee_tv_labelled_discharged_does_not_ground_the_call() {
    let (mut m, _) = a0();
    m.proof_obligations[0].status = ProofStatus::Discharged;
    let errors = validate_module_with_authority(&m, &RejectingModuleProofAuthority);
    assert!(
        has_refusal(
            &errors,
            1,
            "callee `plus` (fn#0) has no kernel-rechecked clean_backend_tv obligation of its own"
        ),
        "{errors:?}"
    );
}

/// The incremental entry point runs the composition rule even when the
/// caller's body is NOT listed as changed (the retarget sits in `top`, the
/// caller claims only `plus` changed, or nothing did).
#[test]
fn review_retarget_is_refused_by_validate_changed_with_any_changed_set() {
    let (mut m, _) = a0();
    let minus = m.functions[MINUS].id;
    retarget_all_calls(&mut m, TOP, minus);
    for changed in [Vec::new(), vec![m.functions[PLUS].id]] {
        let errors = validate_changed(&m, &changed);
        assert!(
            has_refusal(
                &errors,
                1,
                "callee `minus` (fn#1) is called by `top` but no InheritedFromCallee row"
            ),
            "validate_changed({changed:?}): {errors:?}"
        );
    }
}

/// Two DISTINCT called functions renamed onto one symbol name: the name-keyed
/// telescope would bind both calls to ONE `∀` symbol, so the pre-scan refuses
/// it before any row is consulted (rows for both callees are present).
#[test]
fn review_two_called_functions_sharing_a_name_are_refused() {
    let mut m = two_callee_module();
    certify(&mut m, &[PLUS, MINUS, TOP]);
    let (plus, minus) = (m.functions[PLUS].id, m.functions[MINUS].id);
    m.proof_certificates.push(inherit(2, plus, 0));
    m.proof_certificates.push(inherit(2, minus, 1));
    assert!(validate_module(&m).is_empty(), "honest baseline certifies");
    m.functions[MINUS].name = "plus".to_string();
    let errors = validate_module(&m);
    assert!(
        has_refusal(
            &errors,
            2,
            "callee symbol `plus` names two distinct called functions (fn#0 and fn#1)"
        ),
        "{errors:?}"
    );
}

/// WS1.6 scope split: the same-module inheritance restatement rule governs only
/// `InheritedFromCallee` rows on a `Discharged` obligation. A0's composition row
/// sits on the caller's `Certified` TV obligation, scoped to the CALLER, so it
/// would fail the rule's `local.function == Some(callee)` by construction; it
/// must never be routed there, on any layer.
#[test]
fn ws1_6_honest_a0_composition_raises_no_local_inheritance_mismatch() {
    let (m, _) = a0();
    assert_eq!(
        m.proof_obligations[1].function,
        Some(m.functions[TOP].id),
        "the composition row is scoped to the caller"
    );
    for (layer, errors) in layers(&m) {
        assert!(
            !errors.iter().any(|e| matches!(
                e,
                ValidationError::LocalInheritanceRestatementMismatch { .. }
            )),
            "{layer}: {errors:?}"
        );
        assert!(errors.is_empty(), "{layer}: {errors:?}");
    }
}
