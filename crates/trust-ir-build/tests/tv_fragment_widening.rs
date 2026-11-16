// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `clean_backend_tv` fragment widening (roadmap WS1.15, finding F-015): the
//! trusted mirror in `trust-ir-build` re-derives five more shapes, each
//! decided by the in-process Clean kernel, never faith-accepted.
//!
//! | slice | shapes |
//! |---|---|
//! | S1 | `Bool` results and params, `Bool` connectives, `Select`, `ICmp ne` |
//! | S2 | an entry `Switch` over `U8..U64`; fieldless enum params as a tag |
//! | S3 | `I8..I64` as two's complement over `Nat` mod `2^w`; `slt/sle/sgt/sge` |
//! | S4 | `udiv`/`urem` with a provably nonzero divisor; `and/or/xor`; `shl/lshr` by a provably in-range amount |
//! | S5 | `ZExt`/`Trunc` across mixed widths |
//!
//! Per slice, exactly the increment's three test kinds:
//! * **positive** — an honest certificate (minted with the public identity
//!   minter, re-checked by `validate_module` on every entry point);
//! * **negative twin** — a miscompile under the unchanged certificate
//!   (`slt`→`sle`, `and`→`or`, swapped arms, …) is REFUSED by the kernel's
//!   own judgment on the re-derived equation;
//! * **mutation control** — a retype is refused: a width retype (`u32`→`u64`)
//!   by the kernel (the wrap moduli differ), a sign-only retype (`u32`→`i32`,
//!   which changes no bit) by name (the emitted signed signature re-derives
//!   the carrier alias `CleanTV.Int32` the comparand does not spell); and an
//!   out-of-fragment shape is refused by the walker with its named reason.
//!
//! The honest fixtures are also EXECUTED by the reference interpreter, so the
//! denotation each certificate states is tied to what the program computes.

use trust_ir::constant::Constant;
use trust_ir::inst::{BinOp, CastOp, ICmpOp, Inst, SwitchCase};
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::proof::{
    ProofCertificate, ProofEvidence, ProofLineageId, ProofObligation, ProofTransform,
    ProofTransformStage, RejectingModuleProofAuthority, clean_cic_lineage_digest,
};
use trust_ir::ty::{EnumDef, EnumVariant, Ty};
use trust_ir::value::{EnumId, ProofId};
use trust_ir::{BodyGate, FuncId, Module, Producer};
use trust_ir_build::{
    FunctionBuilder, ModuleBuilder, ValidationError, certify_identity_lineage_rung,
    validate_module, validate_module_for_codegen, validate_module_report,
    validate_module_with_authority,
};

// ---------------------------------------------------------------------------
// Harness
// ---------------------------------------------------------------------------

fn builder(name: &str) -> ModuleBuilder {
    let mut mb = ModuleBuilder::new(name);
    mb.set_default_producer(Producer::Clean);
    mb
}

/// One Clean function, stamped `Gated{clean-kernel-tv}` the way the producer
/// stamps a body it certified.
fn function<'a>(
    mb: &'a mut ModuleBuilder,
    name: &str,
    sig: trust_ir::FuncTyId,
) -> FunctionBuilder<'a> {
    let mut fb = mb.function(name, sig);
    fb.set_body_gate(BodyGate::Gated {
        authority: "clean-kernel-tv".to_string(),
        evidence: None,
    });
    fb
}

fn transform() -> ProofTransform {
    ProofTransform::new(
        ProofTransformStage::Frontend,
        "identity",
        "tv-fragment-widening",
        "1.0.0",
    )
}

/// Mint the honest certificate for `func` (obligation 0) with the public
/// identity minter. `Err` = the walker refused the shape.
fn certify(m: &mut Module, func: FuncId) -> Result<(), String> {
    let (_node, obligation, certificate) = certify_identity_lineage_rung(
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

/// Every in-process entry point accepts `m`, and obligation 0 is kernel-tier.
fn assert_certified(m: &Module, what: &str) {
    let e = validate_module(m);
    assert!(e.is_empty(), "{what}: validate_module => {e:?}");
    let e = validate_module_with_authority(m, &RejectingModuleProofAuthority);
    assert!(
        e.is_empty(),
        "{what}: validate_module_with_authority => {e:?}"
    );
    let e = validate_module_for_codegen(m);
    assert!(e.is_empty(), "{what}: validate_module_for_codegen => {e:?}");
    let refs = validate_module_report(m)
        .replayed_certificate_refs()
        .map(|r| r.len());
    assert_eq!(
        refs,
        Some(1),
        "{what}: the certificate is kernel-tier authority"
    );
}

/// The SOLE error is the kernel's own refusal of the re-derived equation for
/// obligation 0 (not a decode / relevance / fragment refusal).
fn assert_kernel_refuses(m: &Module, what: &str) {
    let e = validate_module(m);
    assert!(
        matches!(
            e.as_slice(),
            [ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, reason }]
                if reason.contains("in-process kernel REJECTED the translation-validation equation")
        ),
        "{what}: expected the kernel's own refusal as the sole error, got {e:?}"
    );
    assert!(
        validate_module_report(m)
            .replayed_certificate_refs()
            .is_none(),
        "{what}: nothing reaches the kernel tier"
    );
}

/// A syntactically honest certificate object for `func`, minted from a
/// trivially in-fragment donor and re-pointed at `func` (owning function,
/// theorem name, lineage digest). Its comparand is meaningless for `func`;
/// what matters is that re-derivation of `func`'s LHS runs BEFORE any
/// comparison, so an out-of-fragment `func` is refused with the walker's
/// named reason.
fn forged_certificate(m: &Module, func: FuncId) -> (ProofObligation, ProofCertificate) {
    let mut mb = builder("forge");
    let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = function(&mut mb, "donor", sig);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::U64);
    fb.switch_to_block(e);
    fb.ret(vec![a]);
    let donor = fb.build();
    let donor_m = mb.build().expect("ModuleBuilder::build: test fixture");
    let (_node, mut obligation, mut certificate) = certify_identity_lineage_rung(
        &donor_m,
        ProofLineageId::new(0),
        ProofId::new(0),
        transform(),
        donor,
    )
    .expect("donor is in-fragment");
    let name = m.function_by_id(func).expect("func").name.clone();
    obligation.function = Some(func);
    if let ProofEvidence::CleanCic {
        lineage,
        kernel_recheck: Some(recheck),
        ..
    } = &mut certificate.evidence
    {
        recheck.theorems = vec![format!("CleanTV.{name}.denotes")];
        *lineage = clean_cic_lineage_digest(&obligation);
    } else {
        unreachable!("the minter produces a CleanCic recheck directive");
    }
    (obligation, certificate)
}

/// The walker refuses the shape — on the minter AND on a certificate that
/// claims it — with the named reason, and nothing reaches the kernel tier.
fn assert_fragment_refuses(mut m: Module, func: FuncId, needle: &str, what: &str) {
    let wellformed = validate_module(&m);
    assert!(
        wellformed.is_empty(),
        "{what}: the probe must be well-formed without a certificate: {wellformed:?}"
    );
    let minter = certify(&mut m.clone(), func);
    assert!(
        minter.as_ref().err().is_some_and(|r| r.contains(needle)),
        "{what}: the minter must refuse with `{needle}`, got {minter:?}"
    );
    let (obligation, certificate) = forged_certificate(&m, func);
    m.proof_obligations.push(obligation);
    m.proof_certificates.push(certificate);
    let e = validate_module(&m);
    assert!(
        matches!(
            e.as_slice(),
            [ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, reason }]
                if reason.contains(needle)
        ),
        "{what}: a certificate claiming the shape must be refused (sole error) with `{needle}`, \
         got {e:?}"
    );
    assert!(
        validate_module_report(&m)
            .replayed_certificate_refs()
            .is_none(),
        "{what}: nothing reaches the kernel tier"
    );
}

fn run(m: &Module, entry: &str, args: Vec<InterpretValue>) -> InterpretValue {
    let func = m.function_by_name(entry).expect("entry exists");
    let out = Interpreter::with_module(m)
        .execute_func(func.id, args)
        .unwrap_or_else(|e| panic!("{entry} runs: {e}"))
        .returns;
    out[0].clone()
}

fn u(ty: Ty, v: u128) -> InterpretValue {
    InterpretValue::int(ty, i128::try_from(v).expect("fits")).expect("int")
}

fn i(ty: Ty, v: i128) -> InterpretValue {
    InterpretValue::int(ty, v).expect("int")
}

fn unsigned(v: &InterpretValue) -> u128 {
    v.as_int().expect("integer").as_unsigned()
}

fn signed(v: &InterpretValue) -> i128 {
    v.as_int().expect("integer").as_signed()
}

/// Rewrite every instruction of `func` through `edit`; panics if nothing changed.
fn mutate(m: &mut Module, func: FuncId, edit: impl Fn(&mut Inst) -> bool) {
    let f = m.function_by_id_mut(func).expect("function");
    let mut hits = 0;
    for block in &mut f.blocks {
        for node in &mut block.body {
            if edit(&mut node.inst) {
                hits += 1;
            }
        }
    }
    assert!(hits > 0, "the mutation must hit the fixture");
}

fn set_binop(from: BinOp, to: BinOp) -> impl Fn(&mut Inst) -> bool {
    move |inst| match inst {
        Inst::BinOp { op, .. } if *op == from => {
            *op = to;
            true
        }
        _ => false,
    }
}

fn set_icmp(from: ICmpOp, to: ICmpOp) -> impl Fn(&mut Inst) -> bool {
    move |inst| match inst {
        Inst::ICmp { op, .. } if *op == from => {
            *op = to;
            true
        }
        _ => false,
    }
}

/// Retype every `from`-typed position of `func` (signature, block params,
/// instruction types) to `to`.
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
            match &mut node.inst {
                Inst::BinOp { ty, .. }
                | Inst::ICmp { ty, .. }
                | Inst::Const { ty, .. }
                | Inst::Select { ty, .. } => {
                    if ty == from {
                        *ty = to.clone();
                    }
                }
                Inst::Cast { src_ty, dst_ty, .. } => {
                    if src_ty == from {
                        *src_ty = to.clone();
                    }
                    if dst_ty == from {
                        *dst_ty = to.clone();
                    }
                }
                _ => {}
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

// ---------------------------------------------------------------------------
// S1 — Bool results, connectives, Select, ne
// ---------------------------------------------------------------------------

/// `ult(a, b: u64) -> bool = a < b`
fn ult_module() -> (Module, FuncId) {
    let mut mb = builder("s1_ult");
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::Bool]);
    let mut fb = function(&mut mb, "ult", sig);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::U64);
    let b = fb.add_block_param(e, Ty::U64);
    fb.switch_to_block(e);
    let c = fb.icmp(ICmpOp::Ult, Ty::U64, a, b);
    fb.ret(vec![c]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

/// `band(p, q: bool) -> bool = p && q`
fn band_module(op: BinOp) -> (Module, FuncId) {
    let mut mb = builder("s1_band");
    let sig = mb.add_func_type(vec![Ty::Bool, Ty::Bool], vec![Ty::Bool]);
    let mut fb = function(&mut mb, "band", sig);
    let e = fb.create_block();
    let p = fb.add_block_param(e, Ty::Bool);
    let q = fb.add_block_param(e, Ty::Bool);
    fb.switch_to_block(e);
    let r = fb.binop(op, Ty::Bool, p, q);
    fb.ret(vec![r]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

/// `umin(a, b: u64) -> u64 = select (a < b) a b`
fn umin_select_module() -> (Module, FuncId) {
    let mut mb = builder("s1_umin");
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = function(&mut mb, "umin", sig);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::U64);
    let b = fb.add_block_param(e, Ty::U64);
    fb.switch_to_block(e);
    let c = fb.icmp(ICmpOp::Ult, Ty::U64, a, b);
    let s = fb.select(Ty::U64, c, a, b);
    fb.ret(vec![s]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

/// `pick(p: bool, a, b: u64) -> u64 = if p then a else b` — a Bool PARAM as
/// the branch condition (no ICmp feeds the CondBr).
fn pick_module() -> (Module, FuncId) {
    let mut mb = builder("s1_pick");
    let sig = mb.add_func_type(vec![Ty::Bool, Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = function(&mut mb, "pick", sig);
    let e = fb.create_block();
    let t = fb.create_block();
    let x = fb.create_block();
    let p = fb.add_block_param(e, Ty::Bool);
    let a = fb.add_block_param(e, Ty::U64);
    let b = fb.add_block_param(e, Ty::U64);
    fb.switch_to_block(e);
    fb.condbr(p, t, vec![], x, vec![]);
    fb.switch_to_block(t);
    fb.ret(vec![a]);
    fb.switch_to_block(x);
    fb.ret(vec![b]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

#[test]
fn s1_positive_bool_result_certifies() {
    let (mut m, f) = ult_module();
    assert_eq!(
        run(&m, "ult", vec![u(Ty::U64, 3), u(Ty::U64, 9)]).as_bool(),
        Some(true)
    );
    assert_eq!(
        run(&m, "ult", vec![u(Ty::U64, 9), u(Ty::U64, 3)]).as_bool(),
        Some(false)
    );
    certify(&mut m, f).expect("ult is in the widened fragment");
    assert_certified(&m, "ult");
}

#[test]
fn s1_positive_bool_connective_certifies() {
    for op in [
        BinOp::And,
        BinOp::Or,
        BinOp::Xor,
        BinOp::BAnd,
        BinOp::BOr,
        BinOp::BXor,
    ] {
        let (mut m, f) = band_module(op);
        certify(&mut m, f).unwrap_or_else(|e| panic!("{op:?} at Bool is in the fragment: {e}"));
        assert_certified(&m, &format!("band({op:?})"));
    }
    let (m, _) = band_module(BinOp::And);
    let t = InterpretValue::bool(true);
    let fl = InterpretValue::bool(false);
    assert_eq!(
        run(&m, "band", vec![t.clone(), t.clone()]).as_bool(),
        Some(true)
    );
    assert_eq!(run(&m, "band", vec![t, fl]).as_bool(), Some(false));
}

#[test]
fn s1_positive_select_certifies() {
    let (mut m, f) = umin_select_module();
    assert_eq!(
        unsigned(&run(&m, "umin", vec![u(Ty::U64, 9), u(Ty::U64, 3)])),
        3
    );
    certify(&mut m, f).expect("select is in the widened fragment");
    assert_certified(&m, "umin(select)");
}

#[test]
fn s1_positive_bool_param_condbr_certifies() {
    let (mut m, f) = pick_module();
    assert_eq!(
        unsigned(&run(
            &m,
            "pick",
            vec![InterpretValue::bool(false), u(Ty::U64, 1), u(Ty::U64, 2)]
        )),
        2
    );
    certify(&mut m, f).expect("a Bool param as the CondBr condition is in the fragment");
    assert_certified(&m, "pick");
}

#[test]
fn s1_positive_ne_certifies() {
    let (mut m, f) = ult_module();
    mutate(&mut m, f, set_icmp(ICmpOp::Ult, ICmpOp::Ne));
    assert_eq!(
        run(&m, "ult", vec![u(Ty::U64, 3), u(Ty::U64, 3)]).as_bool(),
        Some(false)
    );
    certify(&mut m, f).expect("ne is in the widened fragment");
    assert_certified(&m, "ne");
}

#[test]
fn s1_negative_twin_ult_to_ule_is_refused() {
    let (mut m, f) = ult_module();
    certify(&mut m, f).expect("honest");
    mutate(&mut m, f, set_icmp(ICmpOp::Ult, ICmpOp::Ule));
    assert_kernel_refuses(&m, "ult->ule");
}

#[test]
fn s1_negative_twin_ne_to_eq_is_refused() {
    let (mut m, f) = ult_module();
    mutate(&mut m, f, set_icmp(ICmpOp::Ult, ICmpOp::Ne));
    certify(&mut m, f).expect("honest");
    mutate(&mut m, f, set_icmp(ICmpOp::Ne, ICmpOp::Eq));
    assert_kernel_refuses(&m, "ne->eq");
}

#[test]
fn s1_negative_twin_and_to_or_is_refused() {
    let (mut m, f) = band_module(BinOp::And);
    certify(&mut m, f).expect("honest");
    mutate(&mut m, f, set_binop(BinOp::And, BinOp::Or));
    assert_kernel_refuses(&m, "and->or at Bool");
}

#[test]
fn s1_negative_twin_swapped_select_arms_is_refused() {
    let (mut m, f) = umin_select_module();
    certify(&mut m, f).expect("honest");
    mutate(&mut m, f, |inst| match inst {
        Inst::Select {
            then_val, else_val, ..
        } => {
            core::mem::swap(then_val, else_val);
            true
        }
        _ => false,
    });
    assert_kernel_refuses(&m, "swapped select arms");
}

#[test]
fn s1_negative_twin_swapped_bool_param_arms_is_refused() {
    let (mut m, f) = pick_module();
    certify(&mut m, f).expect("honest");
    mutate(&mut m, f, |inst| match inst {
        Inst::CondBr {
            then_target,
            else_target,
            ..
        } => {
            core::mem::swap(then_target, else_target);
            true
        }
        _ => false,
    });
    assert_kernel_refuses(&m, "swapped CondBr arms on a Bool param");
}

#[test]
fn s1_mutation_control_bool_result_retyped_to_u8_is_refused() {
    // The Bool result retyped to U8 at the signature only: the body still
    // returns the ICmp's Bool, so the sort disagrees — refused by the walker.
    let (mut m, f) = ult_module();
    certify(&mut m, f).expect("honest");
    let sig = m.function_by_id(f).expect("f").ty;
    m.func_types[sig.as_usize()].returns = vec![Ty::U8];
    let e = validate_module(&m);
    assert!(
        e.iter().any(|x| matches!(
            x,
            ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, reason }
                if reason.contains("has sort Bool where Nat8 is required")
        )),
        "a Bool body under a U8 signature is refused by sort: {e:?}"
    );
}

#[test]
fn s1_mutation_control_ordered_icmp_at_bool_is_refused() {
    // Equality/inequality now have a checked Bool model (the complete truth
    // table is held by scalar_source_value_equation). Ordered comparisons
    // remain outside this TV fragment on both minting and replay paths.
    for op in [
        ICmpOp::Ult,
        ICmpOp::Ule,
        ICmpOp::Ugt,
        ICmpOp::Uge,
        ICmpOp::Slt,
        ICmpOp::Sle,
        ICmpOp::Sgt,
        ICmpOp::Sge,
    ] {
        let mut mb = builder("s1_ordered_bool");
        let sig = mb.add_func_type(vec![Ty::Bool, Ty::Bool], vec![Ty::Bool]);
        let mut fb = function(&mut mb, "ordered", sig);
        let e = fb.create_block();
        let p = fb.add_block_param(e, Ty::Bool);
        let q = fb.add_block_param(e, Ty::Bool);
        fb.switch_to_block(e);
        let r = fb.icmp(op, Ty::Bool, p, q);
        fb.ret(vec![r]);
        let f = fb.build();
        assert_fragment_refuses(
            mb.build().expect("ModuleBuilder::build: test fixture"),
            f,
            &format!("ordered ICmp {op:?} at Bool requires its own model"),
            "ordered Bool comparison",
        );
    }
}

// ---------------------------------------------------------------------------
// S2 — Switch and fieldless enum params
// ---------------------------------------------------------------------------

/// `is_zero(t: u64) -> u64 = switch t { 0 => 1, _ => t - 1 }` (the default
/// arm wraps, so the width is observable to the certificate)
fn is_zero_switch_module() -> (Module, FuncId) {
    let mut mb = builder("s2_is_zero");
    let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = function(&mut mb, "is_zero", sig);
    let e = fb.create_block();
    let z = fb.create_block();
    let d = fb.create_block();
    let t = fb.add_block_param(e, Ty::U64);
    fb.switch_to_block(e);
    fb.switch(
        t,
        vec![SwitchCase {
            value: Constant::Int(0),
            target: z,
            args: vec![],
        }],
        d,
        vec![],
    );
    fb.switch_to_block(z);
    let one = fb.uconst(Ty::U64, 1);
    fb.ret(vec![one]);
    fb.switch_to_block(d);
    let one2 = fb.uconst(Ty::U64, 1);
    let pred = fb.sub(Ty::U64, t, one2);
    fb.ret(vec![pred]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

const LVL_VARIANTS: [&str; 5] = ["zero", "succ", "max", "imax", "param"];

fn lvl_def() -> EnumDef {
    EnumDef::new(
        EnumId::new(0),
        "Lvl",
        LVL_VARIANTS
            .into_iter()
            .map(|n| EnumVariant {
                name: n.into(),
                fields: vec![],
                field_names: vec![],
            })
            .collect(),
    )
}

/// `lvl_code(l: Lvl) -> u64 = match l { zero => 10, succ => 11, max => 12,
/// imax => 13, param => 14 }` as a `Switch` over the tag lane with the dead
/// `[Unreachable]` default, plus nullary probes calling it with a constant.
/// `cases` selects which discriminants get a case (all five = exhaustive).
fn lvl_module(cases: &[i128], default_returns: Option<u64>) -> (Module, FuncId) {
    let mut mb = builder("s2_lvl");
    let lvl = Ty::Enum(EnumId::new(0));
    let sig = mb.add_func_type(vec![lvl.clone()], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let f = {
        let mut fb = function(&mut mb, "lvl_code", sig);
        let e = fb.create_block();
        let arms: Vec<_> = cases.iter().map(|_| fb.create_block()).collect();
        let d = fb.create_block();
        let l = fb.add_block_param(e, lvl.clone());
        fb.switch_to_block(e);
        let tag = fb.extract_field(Ty::U8, l, 0);
        fb.switch(
            tag,
            cases
                .iter()
                .zip(&arms)
                .map(|(k, arm)| SwitchCase {
                    value: Constant::Int(*k),
                    target: *arm,
                    args: vec![],
                })
                .collect(),
            d,
            vec![],
        );
        for (k, arm) in cases.iter().zip(&arms) {
            fb.switch_to_block(*arm);
            let v = fb.uconst(Ty::U64, 10 + u128::try_from(*k).expect("nonneg"));
            fb.ret(vec![v]);
        }
        fb.switch_to_block(d);
        match default_returns {
            Some(v) => {
                let v = fb.uconst(Ty::U64, u128::from(v));
                fb.ret(vec![v]);
            }
            None => fb.unreachable(),
        }
        fb.build()
    };
    for (name, tag) in [("probe_zero", 0i128), ("probe_max", 2), ("probe_param", 4)] {
        // A Rust caller of the certified Clean body, licensed by its own
        // authority (the b3 two-language shape).
        let mut fb = mb.function(name, nullary);
        fb.set_producer(Producer::TRust);
        fb.set_body_gate(BodyGate::Gated {
            authority: "trust-verify".to_string(),
            evidence: None,
        });
        let e = fb.create_block();
        fb.switch_to_block(e);
        let v = fb.const_value(lvl.clone(), Constant::Aggregate(vec![Constant::Int(tag)]));
        let out = fb.call(f, vec![v]);
        fb.ret(vec![out]);
        fb.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.add_enum(lvl_def());
    (m, f)
}

fn run_nullary(m: &Module, name: &str) -> u128 {
    unsigned(&run(m, name, vec![]))
}

#[test]
fn s2_positive_switch_certifies() {
    let (mut m, f) = is_zero_switch_module();
    assert_eq!(unsigned(&run(&m, "is_zero", vec![u(Ty::U64, 0)])), 1);
    assert_eq!(unsigned(&run(&m, "is_zero", vec![u(Ty::U64, 5)])), 4);
    assert_eq!(unsigned(&run(&m, "is_zero", vec![u(Ty::U64, 0)])), 1);
    certify(&mut m, f).expect("a Switch over U64 with a return default is in the fragment");
    assert_certified(&m, "is_zero(switch)");
}

#[test]
fn s2_positive_exhaustive_enum_switch_certifies() {
    let (mut m, f) = lvl_module(&[0, 1, 2, 3, 4], None);
    assert_eq!(run_nullary(&m, "probe_zero"), 10);
    assert_eq!(run_nullary(&m, "probe_max"), 12);
    assert_eq!(run_nullary(&m, "probe_param"), 14);
    certify(&mut m, f).expect("an exhaustive tag Switch with a dead default is in the fragment");
    assert_certified(&m, "lvl_code(exhaustive)");
}

#[test]
fn s2_positive_enum_switch_with_return_default_certifies() {
    let (mut m, f) = lvl_module(&[0, 2], Some(99));
    assert_eq!(run_nullary(&m, "probe_param"), 99);
    certify(&mut m, f).expect("a partial tag Switch with a return default is in the fragment");
    assert_certified(&m, "lvl_code(partial)");
}

#[test]
fn s2_negative_twin_swapped_switch_arms_is_refused() {
    let (mut m, f) = is_zero_switch_module();
    certify(&mut m, f).expect("honest");
    mutate(&mut m, f, |inst| match inst {
        Inst::Switch { default, cases, .. } => {
            core::mem::swap(default, &mut cases[0].target);
            true
        }
        _ => false,
    });
    assert_kernel_refuses(&m, "swapped switch arms");
}

#[test]
fn s2_negative_twin_retagged_enum_case_is_refused() {
    // The `max` and `param` cases exchange targets: the tag→code map is wrong.
    let (mut m, f) = lvl_module(&[0, 1, 2, 3, 4], None);
    certify(&mut m, f).expect("honest");
    mutate(&mut m, f, |inst| match inst {
        Inst::Switch { cases, .. } => {
            let (a, b) = (cases[2].target, cases[4].target);
            cases[2].target = b;
            cases[4].target = a;
            true
        }
        _ => false,
    });
    assert_kernel_refuses(&m, "retagged enum cases");
}

/// `sign_code(t: i8) -> u64 = switch t { -1 => 1, 0 => 2, _ => 3 }`. A
/// signed selector's case is its signed VALUE (`docs/SPEC_RATIFICATIONS.md`
/// §3.3; `switch i8 [ 255: .. ]` is refused by the validator), and it denotes
/// the selector's bit pattern in the S3 carrier (`Nat` mod `2^8`: `255`).
fn signed_switch_module() -> (Module, FuncId) {
    let mut mb = builder("s2_signed_switch");
    let sig = mb.add_func_type(vec![Ty::I8], vec![Ty::U64]);
    let mut fb = function(&mut mb, "sign_code", sig);
    let e = fb.create_block();
    let arms = [fb.create_block(), fb.create_block(), fb.create_block()];
    let t = fb.add_block_param(e, Ty::I8);
    fb.switch_to_block(e);
    fb.switch(
        t,
        [-1, 0]
            .into_iter()
            .zip(arms)
            .map(|(k, target)| SwitchCase {
                value: Constant::Int(k),
                target,
                args: vec![],
            })
            .collect(),
        arms[2],
        vec![],
    );
    for (arm, code) in arms.into_iter().zip(1..) {
        fb.switch_to_block(arm);
        let v = fb.uconst(Ty::U64, code);
        fb.ret(vec![v]);
    }
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

#[test]
fn s2_positive_signed_switch_with_a_negative_case_certifies() {
    let (mut m, f) = signed_switch_module();
    for (t, code) in [(-1, 1), (0, 2), (1, 3), (-128, 3), (127, 3)] {
        assert_eq!(
            unsigned(&run(&m, "sign_code", vec![i(Ty::I8, t)])),
            code,
            "sign_code({t})"
        );
    }
    certify(&mut m, f).expect("a signed selector's canonical negative case is in the fragment");
    assert_certified(&m, "sign_code(switch i8)");
}

#[test]
fn s2_negative_twin_signed_switch_swapped_case_arms_is_refused() {
    // The `-1` and `0` cases exchange targets: the kernel tells the case whose
    // bit pattern is `255` from the case `0`.
    let (mut m, f) = signed_switch_module();
    certify(&mut m, f).expect("honest");
    mutate(&mut m, f, |inst| match inst {
        Inst::Switch { cases, .. } => {
            let (a, b) = (cases[0].target, cases[1].target);
            cases[0].target = b;
            cases[1].target = a;
            true
        }
        _ => false,
    });
    assert_kernel_refuses(&m, "swapped signed switch case arms");
}

#[test]
fn s2_mutation_control_dead_default_without_full_coverage_is_refused() {
    // Four of five discriminants with an `[Unreachable]` default: nothing
    // bounds the fifth tag away, so the dead default cannot be denoted.
    let (m, f) = lvl_module(&[0, 1, 2, 3], None);
    assert_fragment_refuses(
        m,
        f,
        "Switch default is Unreachable but the cases",
        "non-exhaustive dead default",
    );
}

#[test]
fn s2_mutation_control_dead_default_over_plain_integer_is_refused() {
    let (mut m, f) = is_zero_switch_module();
    // Replace the return default with the dead shape: a plain u64 selector
    // has no range to make it dead.
    let func = m.function_by_id_mut(f).expect("f");
    assert_eq!(func.blocks.len(), 3, "entry, case arm, default arm");
    func.blocks[2].body = vec![trust_ir::InstrNode::new(Inst::Unreachable)];
    assert_fragment_refuses(
        m,
        f,
        "is not a fieldless-enum tag-lane read",
        "dead default over u64",
    );
}

#[test]
fn s2_mutation_control_width_retype_is_refused() {
    let (mut m, f) = is_zero_switch_module();
    certify(&mut m, f).expect("honest");
    retype(&mut m, f, &Ty::U64, &Ty::U32);
    assert_kernel_refuses(&m, "u64->u32 retype of the switch");
}

// ---------------------------------------------------------------------------
// S3 — signed widths and comparisons
// ---------------------------------------------------------------------------

/// `addmul(a, b: T) -> T = a * b + a`
fn addmul_module(ty: Ty) -> (Module, FuncId) {
    let mut mb = builder("s3_addmul");
    let sig = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
    let mut fb = function(&mut mb, "addmul", sig);
    let e = fb.create_block();
    let a = fb.add_block_param(e, ty.clone());
    let b = fb.add_block_param(e, ty.clone());
    fb.switch_to_block(e);
    let ab = fb.mul(ty.clone(), a, b);
    let r = fb.add(ty, ab, a);
    fb.ret(vec![r]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

/// `smin(a, b: i32) -> i32 = if a <s b then a else b`
fn smin_module(op: ICmpOp) -> (Module, FuncId) {
    let mut mb = builder("s3_smin");
    let sig = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = function(&mut mb, "smin", sig);
    let e = fb.create_block();
    let t = fb.create_block();
    let x = fb.create_block();
    let a = fb.add_block_param(e, Ty::I32);
    let b = fb.add_block_param(e, Ty::I32);
    fb.switch_to_block(e);
    let c = fb.icmp(op, Ty::I32, a, b);
    fb.condbr(c, t, vec![], x, vec![]);
    fb.switch_to_block(t);
    fb.ret(vec![a]);
    fb.switch_to_block(x);
    fb.ret(vec![b]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

#[test]
fn s3_positive_signed_widths_certify() {
    for ty in [Ty::I64, Ty::I32, Ty::I8] {
        let (mut m, f) = addmul_module(ty.clone());
        certify(&mut m, f).unwrap_or_else(|e| panic!("addmul at {ty} is in the fragment: {e}"));
        assert_certified(&m, &format!("addmul({ty})"));
    }
    let (m, _) = addmul_module(Ty::I8);
    // i8 wraps: (-100 * 2) + (-100) = -300 ≡ -44 (mod 256)
    assert_eq!(
        signed(&run(&m, "addmul", vec![i(Ty::I8, -100), i(Ty::I8, 2)])),
        -44
    );
}

#[test]
fn s3_positive_negative_constant_certifies() {
    // `neg_one() -> i32 = -1` : the literal denotes as its bit pattern.
    let mut mb = builder("s3_neg");
    let sig = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = function(&mut mb, "dec", sig);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I32);
    fb.switch_to_block(e);
    let k = fb.iconst(Ty::I32, -1);
    let r = fb.add(Ty::I32, a, k);
    fb.ret(vec![r]);
    let f = fb.build();
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(signed(&run(&m, "dec", vec![i(Ty::I32, 0)])), -1);
    certify(&mut m, f).expect("a negative literal is in the fragment");
    assert_certified(&m, "dec");
}

#[test]
fn s3_positive_signed_comparison_certifies() {
    for op in [ICmpOp::Slt, ICmpOp::Sle, ICmpOp::Sgt, ICmpOp::Sge] {
        let (mut m, f) = smin_module(op);
        certify(&mut m, f).unwrap_or_else(|e| panic!("{op:?} is in the fragment: {e}"));
        assert_certified(&m, &format!("smin({op:?})"));
    }
    let (m, _) = smin_module(ICmpOp::Slt);
    assert_eq!(
        signed(&run(&m, "smin", vec![i(Ty::I32, -5), i(Ty::I32, 3)])),
        -5
    );
    assert_eq!(
        signed(&run(&m, "smin", vec![i(Ty::I32, 3), i(Ty::I32, -5)])),
        -5
    );
}

#[test]
fn s3_negative_twin_slt_to_sle_is_refused() {
    let (mut m, f) = smin_module(ICmpOp::Slt);
    certify(&mut m, f).expect("honest");
    mutate(&mut m, f, set_icmp(ICmpOp::Slt, ICmpOp::Sle));
    assert_kernel_refuses(&m, "slt->sle");
}

#[test]
fn s3_negative_twin_slt_to_ult_is_refused() {
    // The unsigned comparison on the same bit patterns is a different
    // function (smin(-5, 3) would be 3): the bias makes it non-def-eq.
    let (mut m, f) = smin_module(ICmpOp::Slt);
    certify(&mut m, f).expect("honest");
    mutate(&mut m, f, set_icmp(ICmpOp::Slt, ICmpOp::Ult));
    assert_eq!(
        signed(&run(&m, "smin", vec![i(Ty::I32, -5), i(Ty::I32, 3)])),
        3
    );
    assert_kernel_refuses(&m, "slt->ult");
}

#[test]
fn s3_mutation_control_sdiv_is_refused() {
    let (mut m, f) = addmul_module(Ty::I32);
    mutate(&mut m, f, set_binop(BinOp::Mul, BinOp::SDiv));
    assert_fragment_refuses(m, f, "BinOp SDiv is outside the TV fragment", "sdiv");
}

/// The SOLE error is the walker's refusal of the comparand's param binder
/// spelling for obligation 0 — the S3 signed-carrier name check, which runs
/// BEFORE the kernel is consulted.
fn assert_binder_refuses(m: &Module, binder: usize, want: &str, what: &str) {
    let needle = format!("comparand param binder {binder} is not `{want}`-typed");
    let e = validate_module(m);
    assert!(
        matches!(
            e.as_slice(),
            [ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, reason }]
                if reason.contains(&needle)
        ),
        "{what}: expected the binder-name refusal `{needle}` as the sole error, got {e:?}"
    );
    assert!(
        validate_module_report(m)
            .replayed_certificate_refs()
            .is_none(),
        "{what}: nothing reaches the kernel tier"
    );
}

/// Rewrite every `from`-named param-binder type of the certificate's
/// comparand lambda to `to` — the RELABELLING producer, who spells the
/// carrier the emitted signature demands so that the equation reaches the
/// kernel. What the kernel then decides is the point of the caller.
fn relabel_comparand_binders(m: &mut Module, from: &str, to: &str) {
    use trust_ir::proof::{decode_clean_expr_v1, encode_clean_expr_v1};
    use trust_ir_build::clean_kernel::{Expr, ExprKind};
    fn go(e: &Expr, from: &str, to: &str) -> Expr {
        match e.kind() {
            ExprKind::Lam(bd, ty, body) => {
                let ty = match ty.kind() {
                    ExprKind::Const(n, _) if n.to_string() == from => Expr::const_str(to),
                    _ => (**ty).clone(),
                };
                Expr::lam(*bd, ty, go(body, from, to))
            }
            _ => e.clone(),
        }
    }
    let ProofEvidence::CleanCic { context, .. } = &mut m.proof_certificates[0].evidence else {
        unreachable!("the minter produces CleanCic evidence");
    };
    let lambda = decode_clean_expr_v1(context).expect("the comparand decodes");
    let relabelled = go(&lambda, from, to);
    assert_ne!(lambda, relabelled, "the relabelling must hit a binder");
    *context = encode_clean_expr_v1(&relabelled).expect("the comparand re-encodes");
}

/// A signed width retype (`i32` → `i64`) is refused: first BY NAME, because
/// the comparand still binds at `CleanTV.Int32` where the emitted signature
/// now demands `CleanTV.Int64` …
#[test]
fn s3_mutation_control_width_retype_i32_to_i64_is_refused() {
    let (mut m, f) = addmul_module(Ty::I32);
    certify(&mut m, f).expect("honest");
    retype(&mut m, f, &Ty::I32, &Ty::I64);
    assert_binder_refuses(&m, 0, "CleanTV.Int64", "i32->i64 retype");
}

/// … and, for the producer who RELABELS the comparand's binders to match,
/// by the kernel: `Nat.mod _ 2^64` and `Nat.mod _ 2^32` are not def-eq.
#[test]
fn s3_mutation_control_width_retype_i32_to_i64_with_relabelled_binders_is_kernel_refused() {
    let (mut m, f) = addmul_module(Ty::I32);
    certify(&mut m, f).expect("honest");
    retype(&mut m, f, &Ty::I32, &Ty::I64);
    relabel_comparand_binders(&mut m, "CleanTV.Int32", "CleanTV.Int64");
    assert_kernel_refuses(&m, "i32->i64 retype, binders relabelled to Int64");
}

/// THE INCREMENT'S MUTATION CONTROL: a sign-only retype (`u32` → `i32`) of a
/// body whose ops are sign-agnostic (`Add`/`Mul`) changes NO bit — the
/// reference interpreter computes the same 32-bit pattern before and after —
/// so the two's-complement-over-`Nat` denotations coincide and the kernel
/// alone could not tell the emitted `i32` function from its `u32` source.
/// The certificate therefore binds the CARRIER: the emitted `I32` signature
/// re-derives the sort `Int32`, whose binder spelling is the alias
/// `CleanTV.Int32`, and the comparand (minted at `u32`, binding at `Nat`) is
/// refused BY NAME.
#[test]
fn s3_mutation_control_sign_only_retype_u32_to_i32_is_refused() {
    let (mut m, f) = addmul_module(Ty::U32);
    certify(&mut m, f).expect("honest");
    retype(&mut m, f, &Ty::U32, &Ty::I32);
    // 0xFFFF_FFF0 is -16 as i32: (-16 * 3) + -16 = -64, and 4 * 0xFFFF_FFF0
    // mod 2^32 = 0xFFFF_FFC0 = 2^32 - 64 — the same 32-bit pattern, so the
    // refusal cannot come from a value disagreement.
    let before = unsigned(&run(
        &addmul_module(Ty::U32).0,
        "addmul",
        vec![u(Ty::U32, 0xFFFF_FFF0), u(Ty::U32, 3)],
    ));
    let after = signed(&run(&m, "addmul", vec![i(Ty::I32, -16), i(Ty::I32, 3)]));
    assert_eq!(before, (1u128 << 32) - 64);
    assert_eq!(after, -64);
    assert_binder_refuses(&m, 0, "CleanTV.Int32", "u32->i32 sign-only retype");
}

/// The reverse relabel (`i32` → `u32`) is refused the same way: the comparand
/// binds at `CleanTV.Int32`, the emitted `U32` signature demands `Nat`.
#[test]
fn s3_mutation_control_sign_only_retype_i32_to_u32_is_refused() {
    let (mut m, f) = addmul_module(Ty::I32);
    certify(&mut m, f).expect("honest");
    retype(&mut m, f, &Ty::I32, &Ty::U32);
    assert_binder_refuses(&m, 0, "Nat", "i32->u32 sign-only retype");
}

/// A relabelled sign-only retype (the comparand rewritten to bind at `Nat`
/// after the `i32` → `u32` retype) DOES reach the kernel and checks: the
/// certificate now honestly states an unsigned source for an unsigned
/// emission, and the bit-level meaning is the same. This pins the boundary —
/// the alias binds the carrier LABEL; the values are one `Nat` vocabulary.
#[test]
fn s3_relabelled_sign_only_retype_states_the_unsigned_source_and_checks() {
    let (mut m, f) = addmul_module(Ty::I32);
    certify(&mut m, f).expect("honest");
    retype(&mut m, f, &Ty::I32, &Ty::U32);
    relabel_comparand_binders(&mut m, "CleanTV.Int32", "Nat");
    assert_certified(&m, "i32->u32 retype with the comparand restated at Nat");
}

/// The signed carrier alias is a NAME the kernel environment owns: a
/// comparand binding at an unknown `CleanTV.Int*` constant (or at the alias of
/// a width the emitted signature does not have) is refused by name before
/// the kernel, and one binding a signed position at a width-mismatched alias
/// never certifies.
#[test]
fn s3_mutation_control_foreign_carrier_alias_is_refused() {
    let (mut m, f) = addmul_module(Ty::I32);
    certify(&mut m, f).expect("honest");
    relabel_comparand_binders(&mut m, "CleanTV.Int32", "CleanTV.Int128");
    assert_binder_refuses(&m, 0, "CleanTV.Int32", "comparand bound at CleanTV.Int128");
}

// ---------------------------------------------------------------------------
// S4 — udiv/urem, bitwise, shifts
// ---------------------------------------------------------------------------

/// `quot(a, b: u64) -> u64 = if b == 0 then 0 else a / b` — the WS6.6 item-3
/// diamond (Lean's total `x / 0 = 0`), with the `udiv` in the arm the branch
/// dominates. `zero_on_left` spells the test as `0 == b`.
fn quot_module(zero_on_left: bool, test: ICmpOp) -> (Module, FuncId) {
    let mut mb = builder("s4_quot");
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = function(&mut mb, "quot", sig);
    let e = fb.create_block();
    let z = fb.create_block();
    let d = fb.create_block();
    let a = fb.add_block_param(e, Ty::U64);
    let b = fb.add_block_param(e, Ty::U64);
    fb.switch_to_block(e);
    let zero = fb.uconst(Ty::U64, 0);
    let c = if zero_on_left {
        fb.icmp(test, Ty::U64, zero, b)
    } else {
        fb.icmp(test, Ty::U64, b, zero)
    };
    // `Eq`: then = zero arm; `Ne`: then = divide arm.
    if test == ICmpOp::Eq {
        fb.condbr(c, z, vec![], d, vec![]);
    } else {
        fb.condbr(c, d, vec![], z, vec![]);
    }
    fb.switch_to_block(z);
    let zero2 = fb.uconst(Ty::U64, 0);
    fb.ret(vec![zero2]);
    fb.switch_to_block(d);
    let q = fb.udiv(Ty::U64, a, b);
    fb.ret(vec![q]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

/// `op_k(a: u64) -> u64 = a <op> k`
fn binop_const_module(op: BinOp, k: u128) -> (Module, FuncId) {
    let mut mb = builder("s4_binop_k");
    let sig = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = function(&mut mb, "op_k", sig);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::U64);
    fb.switch_to_block(e);
    let kk = fb.uconst(Ty::U64, k);
    let r = fb.binop(op, Ty::U64, a, kk);
    fb.ret(vec![r]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

/// `op(a, b: u64) -> u64 = a <op> b`
fn binop_module(op: BinOp) -> (Module, FuncId) {
    let mut mb = builder("s4_binop");
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = function(&mut mb, "op", sig);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::U64);
    let b = fb.add_block_param(e, Ty::U64);
    fb.switch_to_block(e);
    let r = fb.binop(op, Ty::U64, a, b);
    fb.ret(vec![r]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

/// `shl_masked(a, s: u64) -> u64 = a << (s % 64)` — the WS6.3 step-2b shape.
fn shl_masked_module(modulus: u128) -> (Module, FuncId) {
    let mut mb = builder("s4_shl_masked");
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = function(&mut mb, "shl_masked", sig);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::U64);
    let s = fb.add_block_param(e, Ty::U64);
    fb.switch_to_block(e);
    let w = fb.uconst(Ty::U64, modulus);
    let amt = fb.binop(BinOp::URem, Ty::U64, s, w);
    let r = fb.binop(BinOp::Shl, Ty::U64, a, amt);
    fb.ret(vec![r]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

#[test]
fn s4_positive_guarded_udiv_certifies() {
    for (left, test) in [
        (false, ICmpOp::Eq),
        (true, ICmpOp::Eq),
        (false, ICmpOp::Ne),
        (true, ICmpOp::Ne),
    ] {
        let (mut m, f) = quot_module(left, test);
        assert_eq!(
            unsigned(&run(&m, "quot", vec![u(Ty::U64, 7), u(Ty::U64, 0)])),
            0
        );
        assert_eq!(
            unsigned(&run(&m, "quot", vec![u(Ty::U64, 7), u(Ty::U64, 2)])),
            3
        );
        certify(&mut m, f).unwrap_or_else(|e| panic!("guarded udiv ({left}, {test:?}): {e}"));
        assert_certified(&m, "quot");
    }
}

#[test]
fn s4_positive_udiv_urem_by_nonzero_constant_certify() {
    for (op, k, a, want) in [(BinOp::UDiv, 3, 10, 3), (BinOp::URem, 3, 10, 1)] {
        let (mut m, f) = binop_const_module(op, k);
        assert_eq!(unsigned(&run(&m, "op_k", vec![u(Ty::U64, a)])), want);
        certify(&mut m, f).unwrap_or_else(|e| panic!("{op:?} by {k}: {e}"));
        assert_certified(&m, &format!("{op:?} by {k}"));
    }
}

#[test]
fn s4_positive_bitwise_certify() {
    for (op, want) in [
        (BinOp::And, 0b1000),
        (BinOp::Or, 0b1110),
        (BinOp::Xor, 0b0110),
    ] {
        let (mut m, f) = binop_module(op);
        assert_eq!(
            unsigned(&run(&m, "op", vec![u(Ty::U64, 0b1100), u(Ty::U64, 0b1010)])),
            want
        );
        certify(&mut m, f).unwrap_or_else(|e| panic!("{op:?}: {e}"));
        assert_certified(&m, &format!("{op:?}"));
    }
}

#[test]
fn s4_positive_shifts_by_constant_certify() {
    for (op, k, a, want) in [
        (BinOp::Shl, 3, 5, 40),
        (BinOp::LShr, 2, 40, 10),
        (BinOp::Shl, 63, 3, 1u128 << 63),
    ] {
        let (mut m, f) = binop_const_module(op, k);
        assert_eq!(unsigned(&run(&m, "op_k", vec![u(Ty::U64, a)])), want);
        certify(&mut m, f).unwrap_or_else(|e| panic!("{op:?} by {k}: {e}"));
        assert_certified(&m, &format!("{op:?} by {k}"));
    }
}

#[test]
fn s4_positive_shift_by_masked_amount_certifies() {
    let (mut m, f) = shl_masked_module(64);
    assert_eq!(
        unsigned(&run(&m, "shl_masked", vec![u(Ty::U64, 1), u(Ty::U64, 67)])),
        8
    );
    certify(&mut m, f).expect("`shl a, (urem s, 64)` is in the fragment");
    assert_certified(&m, "shl_masked");
}

#[test]
fn s4_negative_twin_and_to_or_is_refused() {
    let (mut m, f) = binop_module(BinOp::And);
    certify(&mut m, f).expect("honest");
    mutate(&mut m, f, set_binop(BinOp::And, BinOp::Or));
    assert_kernel_refuses(&m, "and->or");
}

#[test]
fn s4_negative_twin_xor_to_and_is_refused() {
    let (mut m, f) = binop_module(BinOp::Xor);
    certify(&mut m, f).expect("honest");
    mutate(&mut m, f, set_binop(BinOp::Xor, BinOp::And));
    assert_kernel_refuses(&m, "xor->and");
}

#[test]
fn s4_negative_twin_swapped_div_diamond_arms_is_refused() {
    // Swapping the diamond's targets moves the `udiv` under `b == 0`: the
    // walker refuses it BEFORE the kernel (nothing proves the divisor nonzero
    // on that path) — the WS6.6 REVIEW fix, fail-closed.
    let (mut m, f) = quot_module(false, ICmpOp::Eq);
    certify(&mut m, f).expect("honest");
    mutate(&mut m, f, |inst| match inst {
        Inst::CondBr {
            then_target,
            else_target,
            ..
        } => {
            core::mem::swap(then_target, else_target);
            true
        }
        _ => false,
    });
    let e = validate_module(&m);
    assert!(
        matches!(
            e.as_slice(),
            [ValidationError::CertifiedCleanCicKernelRecheckFailed { obligation: 0, reason }]
                if reason.contains("is not provably nonzero")
        ),
        "swapped div diamond: {e:?}"
    );
}

#[test]
fn s4_negative_twin_shift_amount_edited_is_refused() {
    let (mut m, f) = binop_const_module(BinOp::Shl, 3);
    certify(&mut m, f).expect("honest");
    mutate(&mut m, f, |inst| match inst {
        Inst::Const { value, .. } if *value == Constant::Int(3) => {
            *value = Constant::Int(4);
            true
        }
        _ => false,
    });
    assert_kernel_refuses(&m, "shl by 3 -> shl by 4");
}

#[test]
fn s4_mutation_control_eager_select_udiv_is_refused() {
    // `select (b == 0) 0 (udiv a b)`: the udiv EXECUTES at b = 0 (UB) — the
    // WS6.6 item-3 shape that must never be minted, refused by name.
    let mut mb = builder("s4_select_div");
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = function(&mut mb, "quot", sig);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::U64);
    let b = fb.add_block_param(e, Ty::U64);
    fb.switch_to_block(e);
    let zero = fb.uconst(Ty::U64, 0);
    let c = fb.icmp(ICmpOp::Eq, Ty::U64, b, zero);
    let q = fb.udiv(Ty::U64, a, b);
    let s = fb.select(Ty::U64, c, zero, q);
    fb.ret(vec![s]);
    let f = fb.build();
    assert_fragment_refuses(
        mb.build().expect("ModuleBuilder::build: test fixture"),
        f,
        "is not provably nonzero",
        "select-guarded udiv",
    );
}

#[test]
fn s4_mutation_control_unguarded_udiv_is_refused() {
    let (m, f) = binop_module(BinOp::UDiv);
    assert_fragment_refuses(m, f, "is not provably nonzero", "udiv a b");
}

#[test]
fn s4_mutation_control_udiv_by_zero_constant_is_refused() {
    let (m, f) = binop_const_module(BinOp::UDiv, 0);
    assert_fragment_refuses(m, f, "is not provably nonzero", "udiv a 0");
}

#[test]
fn s4_mutation_control_out_of_range_shift_is_refused() {
    let (m, f) = binop_const_module(BinOp::Shl, 64);
    assert_fragment_refuses(m, f, "is not provably below the width 64", "shl a 64");
    let (m, f) = shl_masked_module(65);
    assert_fragment_refuses(
        m,
        f,
        "is not provably below the width 64",
        "shl a (urem s 65)",
    );
    let (m, f) = binop_module(BinOp::Shl);
    assert_fragment_refuses(m, f, "is not provably below the width 64", "shl a b");
}

#[test]
fn s4_mutation_control_ashr_is_refused() {
    let (m, f) = binop_const_module(BinOp::AShr, 1);
    assert_fragment_refuses(m, f, "BinOp AShr is outside the TV fragment", "ashr");
}

#[test]
fn s4_mutation_control_width_retype_is_refused() {
    let (mut m, f) = binop_const_module(BinOp::Shl, 3);
    certify(&mut m, f).expect("honest");
    retype(&mut m, f, &Ty::U64, &Ty::U32);
    assert_kernel_refuses(&m, "u64->u32 retype of shl");
}

// ---------------------------------------------------------------------------
// S5 — mixed widths via ZExt / Trunc
// ---------------------------------------------------------------------------

/// `widen(a: u32) -> u64 = zext a`
fn widen_module() -> (Module, FuncId) {
    let mut mb = builder("s5_widen");
    let sig = mb.add_func_type(vec![Ty::U32], vec![Ty::U64]);
    let mut fb = function(&mut mb, "widen", sig);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::U32);
    fb.switch_to_block(e);
    let r = fb.zext(Ty::U32, Ty::U64, a);
    fb.ret(vec![r]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

/// `narrow_add(a: u64, b: u8) -> u8 = trunc(a) + b`
fn narrow_add_module() -> (Module, FuncId) {
    let mut mb = builder("s5_narrow");
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U8], vec![Ty::U8]);
    let mut fb = function(&mut mb, "narrow_add", sig);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::U64);
    let b = fb.add_block_param(e, Ty::U8);
    fb.switch_to_block(e);
    let t = fb.trunc(Ty::U64, Ty::U8, a);
    let r = fb.add(Ty::U8, t, b);
    fb.ret(vec![r]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

#[test]
fn s5_positive_zext_certifies() {
    let (mut m, f) = widen_module();
    assert_eq!(
        unsigned(&run(&m, "widen", vec![u(Ty::U32, 0xFFFF_FFFF)])),
        0xFFFF_FFFF
    );
    certify(&mut m, f).expect("zext across widths is in the fragment");
    assert_certified(&m, "widen");
}

#[test]
fn s5_positive_trunc_with_mixed_width_params_certifies() {
    let (mut m, f) = narrow_add_module();
    assert_eq!(
        unsigned(&run(
            &m,
            "narrow_add",
            vec![u(Ty::U64, 0x1_02), u(Ty::U8, 3)]
        )),
        5
    );
    certify(&mut m, f).expect("trunc + mixed-width params are in the fragment");
    assert_certified(&m, "narrow_add");
}

/// `wide_inc(a: u32) -> u64`: honest `zext(a) + 1` (wraps at 2^64), or the
/// miscompile `zext(a + 1)` (wraps at 2^32 first: 0xFFFF_FFFF maps to 0, not
/// 2^32).
fn wide_inc_module(miscompiled: bool) -> (Module, FuncId) {
    let mut mb = builder("s5_wide_inc");
    let sig = mb.add_func_type(vec![Ty::U32], vec![Ty::U64]);
    let mut fb = function(&mut mb, "wide_inc", sig);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::U32);
    fb.switch_to_block(e);
    let r = if miscompiled {
        let one = fb.uconst(Ty::U32, 1);
        let inc = fb.add(Ty::U32, a, one);
        fb.zext(Ty::U32, Ty::U64, inc)
    } else {
        let wide = fb.zext(Ty::U32, Ty::U64, a);
        let one = fb.uconst(Ty::U64, 1);
        fb.add(Ty::U64, wide, one)
    };
    fb.ret(vec![r]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

#[test]
fn s5_negative_twin_widen_after_wrap_is_refused() {
    let (mut honest, f) = wide_inc_module(false);
    let (mut twin, _) = wide_inc_module(true);
    assert_eq!(
        unsigned(&run(&honest, "wide_inc", vec![u(Ty::U32, 0xFFFF_FFFF)])),
        1 << 32
    );
    assert_eq!(
        unsigned(&run(&twin, "wide_inc", vec![u(Ty::U32, 0xFFFF_FFFF)])),
        0
    );
    certify(&mut honest, f).expect("honest");
    twin.proof_obligations = honest.proof_obligations.clone();
    twin.proof_certificates = honest.proof_certificates.clone();
    assert_kernel_refuses(&twin, "zext(a + 1) under the certificate of zext(a) + 1");
}

#[test]
fn s5_negative_twin_zext_to_wider_result_is_refused() {
    // `widen` retyped to return u16 from a u8 param with the SAME certificate:
    // the modulus in the re-derived `Nat.mod x 2^16` differs from the recorded
    // `2^64` — the kernel refuses.
    let (mut m, f) = widen_module();
    certify(&mut m, f).expect("honest");
    retype(&mut m, f, &Ty::U64, &Ty::U16);
    retype(&mut m, f, &Ty::U32, &Ty::U8);
    assert_kernel_refuses(&m, "widen retyped u8->u16");
}

#[test]
fn s5_mutation_control_sext_is_refused() {
    let (mut m, f) = widen_module();
    mutate(&mut m, f, |inst| match inst {
        Inst::Cast { op, .. } => {
            *op = CastOp::SExt;
            true
        }
        _ => false,
    });
    assert_fragment_refuses(m, f, "is outside the TV fragment", "sext");
}

#[test]
fn s5_mutation_control_bool_zext_is_refused() {
    // `b as u8` (ZExt Bool -> U8) is well-formed IR but outside the fragment:
    // a Bool has no width to widen from.
    let mut mb = builder("s5_bool_zext");
    let sig = mb.add_func_type(vec![Ty::Bool], vec![Ty::U8]);
    let mut fb = function(&mut mb, "to_u8", sig);
    let e = fb.create_block();
    let p = fb.add_block_param(e, Ty::Bool);
    fb.switch_to_block(e);
    let r = fb.zext(Ty::Bool, Ty::U8, p);
    fb.ret(vec![r]);
    let f = fb.build();
    assert_fragment_refuses(
        mb.build().expect("ModuleBuilder::build: test fixture"),
        f,
        "Cast ZExt bool -> u8 is outside the TV fragment",
        "bool zext",
    );
}

#[test]
fn s5_mutation_control_width_retype_u32_to_u64_is_refused() {
    let (mut m, f) = addmul_module(Ty::U32);
    certify(&mut m, f).expect("honest");
    retype(&mut m, f, &Ty::U32, &Ty::U64);
    assert_kernel_refuses(&m, "u32->u64 retype");
}

// ---------------------------------------------------------------------------
// S3 × Fragment-4 — a signed literal as a GEP index
// ---------------------------------------------------------------------------

/// `boxed_pick(a, b: u32) -> u32`: a heap `[u32; 2]`, `a` stored at cell 0
/// and `b` at `&cells[idx]`, then `cells[idx]` loaded back and the box
/// released. The box is a `CleanHeap` cell, so it is released by `Release`
/// (count 1 -> 0) — `Dealloc` of it is undefined behaviour (decided by the
/// interpreter: Lean has no byte size for an array cell and answers
/// `unsupported.layout`) and is refused by the Fragment-4 walker as a wrong
/// emission.
/// `idx` is the literal `k` at `idx_ty` — a signed index type is legal IR.
fn boxed_index_module(idx_ty: Ty, k: i128) -> (Module, FuncId) {
    use trust_ir::inst::AllocOrigin;
    let mut mb = builder("s3_boxed_index");
    let sig = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![Ty::U32]);
    let elem = mb.add_type(Ty::U32);
    let mut fb = function(&mut mb, "boxed_pick", sig);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::U32);
    let b = fb.add_block_param(e, Ty::U32);
    fb.switch_to_block(e);
    let cells = fb.heap_alloc(Ty::Array(elem, 2), None, Some(4), AllocOrigin::CleanHeap);
    fb.store(Ty::U32, cells, a);
    let idx = fb.iconst(idx_ty, k);
    let slot = fb.gep(Ty::U32, cells, vec![idx]);
    fb.store(Ty::U32, slot, b);
    let r = fb.load(Ty::U32, slot);
    fb.release(cells);
    fb.ret(vec![r]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

#[test]
fn s3_positive_non_negative_signed_gep_index_certifies() {
    // A NON-negative signed literal's bit pattern is its value, so it folds
    // to the cell the machine addresses: `&cells[1i64]` is cell 4.
    let (mut m, f) = boxed_index_module(Ty::I64, 1);
    assert_eq!(
        unsigned(&run(&m, "boxed_pick", vec![u(Ty::U32, 7), u(Ty::U32, 9)])),
        9
    );
    certify(&mut m, f).expect("a non-negative signed GEP index is in the fragment");
    // The certificate lanes accept it and it is kernel-tier. (The codegen
    // lane is not asserted. A certified Fragment-4 body no longer carries a
    // `Dealloc` — its cell is released by `Release` — so its codegen verdict
    // is whatever `HeapAlloc(CleanHeap)` earns: `validate_module_for_codegen`
    // admits this licensed body, while trust-cg refuses `HeapAlloc(CleanHeap)`.
    // Whether that allocation is itself `UnlowerableForCodegen` is the open
    // HeapAlloc-layout follow-up, a lowering rule and not a certificate
    // verdict.)
    let what = "boxed_pick[1i64]";
    let e = validate_module(&m);
    assert!(e.is_empty(), "{what}: validate_module => {e:?}");
    let e = validate_module_with_authority(&m, &RejectingModuleProofAuthority);
    assert!(
        e.is_empty(),
        "{what}: validate_module_with_authority => {e:?}"
    );
    assert_eq!(
        validate_module_report(&m)
            .replayed_certificate_refs()
            .map(|r| r.len()),
        Some(1),
        "{what}: the certificate is kernel-tier authority"
    );
}

#[test]
fn s3_mutation_control_negative_signed_gep_index_is_refused() {
    // `&cells[-1i8]` is UB in the reference semantics (`eval_gep` refuses a
    // negative index). Its bit pattern (255) must NOT fold to a defined cell
    // — the walker refuses by name, and nothing reaches the kernel.
    let (m, f) = boxed_index_module(Ty::I8, -1);
    let func = m.function_by_name("boxed_pick").expect("entry");
    let ub = Interpreter::with_module(&m)
        .execute_func(func.id, vec![u(Ty::U32, 7), u(Ty::U32, 9)])
        .err()
        .map(|e| e.to_string());
    assert!(
        ub.as_deref().is_some_and(|e| e.contains("negative index")),
        "the reference interpreter must refuse the negative index as UB: {ub:?}"
    );
    assert_fragment_refuses(
        m,
        f,
        "is not a closed non-negative literal (a negative signed index is UB)",
        "boxed_pick[-1i8]",
    );
}

// ---------------------------------------------------------------------------
// Still outside — the widening stops where the rulings say
// ---------------------------------------------------------------------------

#[test]
fn out_of_fragment_widths_stay_refused_by_name() {
    for ty in [Ty::U128, Ty::Usize] {
        let (m, f) = addmul_module(ty.clone());
        assert_fragment_refuses(
            m,
            f,
            "is outside the TV fragment (U8..U64, I8..I64, Bool, fieldless enums)",
            &format!("addmul({ty})"),
        );
    }
}

/// `mk_zero() -> Lvl` (a Clean callee returning the fieldless enum) and
/// `zero_code() -> u64 = extract_field 0 (call mk_zero())`. An enum is a
/// fragment PARAM sort (S2), but never a RESULT sort — for the function
/// itself and, by the same rule, for a pinned callee symbol. The walker
/// refuses the callee by name rather than leaning on the call-edge post-pass
/// (which would refuse too: an enum-returning callee holds no rechecked TV).
#[test]
fn enum_returning_callee_is_refused_by_name() {
    let mut mb = builder("s2_enum_callee");
    let lvl = Ty::Enum(EnumId::new(0));
    let mk_sig = mb.add_func_type(vec![], vec![lvl.clone()]);
    let code_sig = mb.add_func_type(vec![], vec![Ty::U64]);
    let mk_zero = {
        let mut fb = function(&mut mb, "mk_zero", mk_sig);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let v = fb.const_value(lvl.clone(), Constant::Aggregate(vec![Constant::Int(0)]));
        fb.ret(vec![v]);
        fb.build()
    };
    let zero_code = {
        let mut fb = function(&mut mb, "zero_code", code_sig);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let l = fb.call(mk_zero, vec![]);
        let tag = fb.extract_field(Ty::U8, l, 0);
        let wide = fb.cast(CastOp::ZExt, Ty::U8, Ty::U64, tag);
        fb.ret(vec![wide]);
        fb.build()
    };
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.add_enum(lvl_def());
    assert_eq!(run_nullary(&m, "zero_code"), 0);
    assert_fragment_refuses(
        m,
        zero_code,
        "callee `mk_zero` returns the enum",
        "zero_code via an enum-returning callee",
    );
}

// ---------------------------------------------------------------------------
// Adversarial review pass — shapes the implementation pass did not probe
// ---------------------------------------------------------------------------

/// `quot(a, b, c: u64) -> u64 = if c == 0 then 0 else a / b` — the diamond
/// guards a value that is NOT the divisor. The `else` arm still divides by
/// `b`, which may be zero: UB in the reference semantics, and `Nat.div _ 0`
/// is TOTAL (`= 0`) in the kernel, so denoting it would certify a body the
/// machine never defines. The S4 nonzero fact is keyed by VALUE, never by
/// "a dominating zero test exists somewhere".
fn quot_foreign_guard_module() -> (Module, FuncId) {
    let mut mb = builder("adv_quot_foreign");
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = function(&mut mb, "quot", sig);
    let e = fb.create_block();
    let z = fb.create_block();
    let d = fb.create_block();
    let a = fb.add_block_param(e, Ty::U64);
    let b = fb.add_block_param(e, Ty::U64);
    let c = fb.add_block_param(e, Ty::U64);
    fb.switch_to_block(e);
    let zero = fb.uconst(Ty::U64, 0);
    let t = fb.icmp(ICmpOp::Eq, Ty::U64, c, zero);
    fb.condbr(t, z, vec![], d, vec![]);
    fb.switch_to_block(z);
    let zero2 = fb.uconst(Ty::U64, 0);
    fb.ret(vec![zero2]);
    fb.switch_to_block(d);
    let q = fb.udiv(Ty::U64, a, b);
    fb.ret(vec![q]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

#[test]
fn adv_guard_on_a_foreign_value_does_not_license_udiv() {
    let (m, f) = quot_foreign_guard_module();
    let entry = m.function_by_name("quot").expect("entry").id;
    let ub = Interpreter::with_module(&m)
        .execute_func(entry, vec![u(Ty::U64, 7), u(Ty::U64, 0), u(Ty::U64, 1)])
        .err()
        .map(|e| e.to_string());
    assert!(
        ub.as_deref()
            .is_some_and(|e| e.contains("division by zero")),
        "the reference interpreter must refuse `a / 0` on the guarded arm as UB: {ub:?}"
    );
    assert_fragment_refuses(
        m,
        f,
        "is not provably nonzero",
        "udiv under a zero test on a DIFFERENT value",
    );
}

/// `quot_swapped(a, b: u64) -> u64 = if b != 0 then 0 else a / b` — the
/// `icmp ne` diamond with the arms exchanged, so the `udiv` sits on the arm
/// where `b` IS zero. The `Ne` fact must land on the `then` arm only.
fn quot_ne_wrong_arm_module() -> (Module, FuncId) {
    let mut mb = builder("adv_quot_ne_wrong_arm");
    let sig = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = function(&mut mb, "quot", sig);
    let e = fb.create_block();
    let z = fb.create_block();
    let d = fb.create_block();
    let a = fb.add_block_param(e, Ty::U64);
    let b = fb.add_block_param(e, Ty::U64);
    fb.switch_to_block(e);
    let zero = fb.uconst(Ty::U64, 0);
    let t = fb.icmp(ICmpOp::Ne, Ty::U64, b, zero);
    // `then` is the b != 0 arm — the fixture puts the constant there and the
    // division on the b == 0 arm.
    fb.condbr(t, z, vec![], d, vec![]);
    fb.switch_to_block(z);
    let zero2 = fb.uconst(Ty::U64, 0);
    fb.ret(vec![zero2]);
    fb.switch_to_block(d);
    let q = fb.udiv(Ty::U64, a, b);
    fb.ret(vec![q]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

#[test]
fn adv_ne_zero_test_licenses_only_the_then_arm() {
    let (m, f) = quot_ne_wrong_arm_module();
    assert_fragment_refuses(
        m,
        f,
        "is not provably nonzero",
        "udiv on the `b == 0` arm of an `icmp ne b, 0` diamond",
    );
}

/// `shr(a: i8) -> i8 = a >>u k` — `LShr` is a BIT-PATTERN op even at a signed
/// type: the reference interpreter shifts `InterpretInt::raw`, so
/// `-1i8 >>u 1` is `127`, never `-1`. The S4 denotation `Nat.div a (2^k)`
/// only agrees with that because the signed carrier IS the bit pattern.
fn lshr_i8_module(k: i128) -> (Module, FuncId) {
    let mut mb = builder("adv_lshr_i8");
    let sig = mb.add_func_type(vec![Ty::I8], vec![Ty::I8]);
    let mut fb = function(&mut mb, "shr", sig);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I8);
    fb.switch_to_block(e);
    let kk = fb.iconst(Ty::I8, k);
    let r = fb.binop(BinOp::LShr, Ty::I8, a, kk);
    fb.ret(vec![r]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

#[test]
fn adv_signed_lshr_is_logical_on_the_bit_pattern() {
    let (mut m, f) = lshr_i8_module(1);
    assert_eq!(signed(&run(&m, "shr", vec![i(Ty::I8, -1)])), 127);
    assert_eq!(signed(&run(&m, "shr", vec![i(Ty::I8, -2)])), 127);
    certify(&mut m, f).expect("`lshr i8` by a literal below the width is in the fragment");
    assert_certified(&m, "lshr i8 a, 1");
    // The twin shifts by one bit more: a real miscompile the kernel decides.
    let mut twin = m.clone();
    mutate(&mut twin, f, |inst| match inst {
        Inst::Const { value, .. } if *value == Constant::Int(1) => {
            *value = Constant::Int(2);
            true
        }
        _ => false,
    });
    assert_eq!(signed(&run(&twin, "shr", vec![i(Ty::I8, -1)])), 63);
    assert_kernel_refuses(&twin, "lshr i8 by 1 -> by 2");
}

/// `quot3(a: i8) -> i8 = a /u 3` — `UDiv` at a signed type is likewise the
/// bit-pattern quotient (`-1i8 /u 3 == 85`), which is what `Nat.div` states.
fn udiv_i8_module(k: i128) -> (Module, FuncId) {
    let mut mb = builder("adv_udiv_i8");
    let sig = mb.add_func_type(vec![Ty::I8], vec![Ty::I8]);
    let mut fb = function(&mut mb, "quot3", sig);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I8);
    fb.switch_to_block(e);
    let kk = fb.iconst(Ty::I8, k);
    let r = fb.binop(BinOp::UDiv, Ty::I8, a, kk);
    fb.ret(vec![r]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

#[test]
fn adv_signed_udiv_is_the_bit_pattern_quotient() {
    let (mut m, f) = udiv_i8_module(3);
    assert_eq!(signed(&run(&m, "quot3", vec![i(Ty::I8, -1)])), 85);
    assert_eq!(signed(&run(&m, "quot3", vec![i(Ty::I8, 9)])), 3);
    certify(&mut m, f).expect("`udiv i8` by a nonzero literal is in the fragment");
    assert_certified(&m, "udiv i8 a, 3");
    // A NEGATIVE divisor literal is nonzero too (its bit pattern is 253), and
    // the quotient the machine computes is the bit-pattern one.
    let (mut neg, g) = udiv_i8_module(-3);
    assert_eq!(signed(&run(&neg, "quot3", vec![i(Ty::I8, -1)])), 1);
    certify(&mut neg, g).expect("a negative nonzero divisor literal is still nonzero");
    assert_certified(&neg, "udiv i8 a, -3");
}

/// `less(a, b: u8) -> bool = a <s b` — a SIGNED comparison at an UNSIGNED
/// declared type. `InterpretInt::as_signed` reads the bit pattern's sign bit
/// and ignores the declared signedness, so `less(200, 5)` is TRUE; the S3
/// `2^(w-1)` bias must agree, and the `ult` twin (FALSE there) must be
/// refused by the kernel.
fn slt_at_u8_module() -> (Module, FuncId) {
    let mut mb = builder("adv_slt_u8");
    let sig = mb.add_func_type(vec![Ty::U8, Ty::U8], vec![Ty::Bool]);
    let mut fb = function(&mut mb, "less", sig);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::U8);
    let b = fb.add_block_param(e, Ty::U8);
    fb.switch_to_block(e);
    let r = fb.icmp(ICmpOp::Slt, Ty::U8, a, b);
    fb.ret(vec![r]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

#[test]
fn adv_signed_compare_at_an_unsigned_type_reads_the_sign_bit() {
    let (mut m, f) = slt_at_u8_module();
    assert_eq!(
        run(&m, "less", vec![u(Ty::U8, 200), u(Ty::U8, 5)]).as_bool(),
        Some(true),
        "`slt` reads the 8-bit pattern's sign bit even at u8"
    );
    assert_eq!(
        run(&m, "less", vec![u(Ty::U8, 5), u(Ty::U8, 200)]).as_bool(),
        Some(false)
    );
    certify(&mut m, f).expect("`icmp slt u8` is in the fragment");
    assert_certified(&m, "slt at u8");
    let mut twin = m.clone();
    mutate(&mut twin, f, set_icmp(ICmpOp::Slt, ICmpOp::Ult));
    assert_eq!(
        run(&twin, "less", vec![u(Ty::U8, 200), u(Ty::U8, 5)]).as_bool(),
        Some(false),
        "the twin really is a different function"
    );
    assert_kernel_refuses(&twin, "slt -> ult at u8");
}

/// A fieldless enum whose discriminants are EXPLICIT and non-contiguous.
fn sparse_def() -> EnumDef {
    EnumDef::new(
        EnumId::new(0),
        "Sparse",
        ["lo", "mid", "hi"]
            .into_iter()
            .map(|n| EnumVariant {
                name: n.into(),
                fields: vec![],
                field_names: vec![],
            })
            .collect(),
    )
    .with_discriminants(vec![Some(0), Some(5), Some(9)])
}

/// `sparse_code(s: Sparse) -> u64` as a `Switch` over the tag lane with the
/// dead `[Unreachable]` default, the cases listed OUT OF ASCENDING ORDER so
/// the "last case becomes the else branch" rule picks a middle discriminant.
fn sparse_module(cases: &[i128]) -> (Module, FuncId) {
    let mut mb = builder("adv_sparse");
    let sparse = Ty::Enum(EnumId::new(0));
    let sig = mb.add_func_type(vec![sparse.clone()], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let f = {
        let mut fb = function(&mut mb, "sparse_code", sig);
        let e = fb.create_block();
        let arms: Vec<_> = cases.iter().map(|_| fb.create_block()).collect();
        let d = fb.create_block();
        let s = fb.add_block_param(e, sparse.clone());
        fb.switch_to_block(e);
        let tag = fb.extract_field(Ty::U8, s, 0);
        fb.switch(
            tag,
            cases
                .iter()
                .zip(&arms)
                .map(|(k, arm)| SwitchCase {
                    value: Constant::Int(*k),
                    target: *arm,
                    args: vec![],
                })
                .collect(),
            d,
            vec![],
        );
        for (k, arm) in cases.iter().zip(&arms) {
            fb.switch_to_block(*arm);
            let v = fb.uconst(Ty::U64, 100 + u128::try_from(*k).expect("nonneg"));
            fb.ret(vec![v]);
        }
        fb.switch_to_block(d);
        fb.unreachable();
        fb.build()
    };
    for (name, tag) in [("probe_lo", 0i128), ("probe_mid", 5), ("probe_hi", 9)] {
        let mut fb = mb.function(name, nullary);
        fb.set_producer(Producer::TRust);
        fb.set_body_gate(BodyGate::Gated {
            authority: "trust-verify".to_string(),
            evidence: None,
        });
        let e = fb.create_block();
        fb.switch_to_block(e);
        let v = fb.const_value(
            sparse.clone(),
            Constant::Aggregate(vec![Constant::Int(tag)]),
        );
        let out = fb.call(f, vec![v]);
        fb.ret(vec![out]);
        fb.build();
    }
    let mut m = mb.build().expect("ModuleBuilder::build: test fixture");
    m.add_enum(sparse_def());
    (m, f)
}

#[test]
fn adv_dead_default_switch_over_sparse_out_of_order_cases_certifies() {
    // Cases in the order 9, 0, 5: the LAST case (the MIDDLE discriminant) is
    // the one the denotation folds into the else branch.
    let (mut m, f) = sparse_module(&[9, 0, 5]);
    assert_eq!(run_nullary(&m, "probe_lo"), 100);
    assert_eq!(run_nullary(&m, "probe_mid"), 105);
    assert_eq!(run_nullary(&m, "probe_hi"), 109);
    certify(&mut m, f)
        .expect("an exhaustive sparse tag Switch with a dead default is in the fragment");
    assert_certified(&m, "sparse_code(out of order)");
    // The twin exchanges the first and last case targets: `lo` and `mid` now
    // report each other's code, and the else branch changes with them.
    let mut twin = m.clone();
    mutate(&mut twin, f, |inst| match inst {
        Inst::Switch { cases, .. } => {
            let (a, b) = (cases[1].target, cases[2].target);
            cases[1].target = b;
            cases[2].target = a;
            true
        }
        _ => false,
    });
    assert_eq!(run_nullary(&twin, "probe_lo"), 105);
    assert_kernel_refuses(&twin, "sparse switch with exchanged case targets");
}

#[test]
fn adv_dead_default_switch_needs_the_exact_discriminant_set() {
    // The case set {0, 5, 6} is neither the enum's discriminants nor a
    // superset of them: tag 9 would fall into the dead default.
    let (m, f) = sparse_module(&[0, 5, 6]);
    assert_fragment_refuses(
        m,
        f,
        "Switch default is Unreachable but the cases",
        "sparse dead default with a wrong case set",
    );
}

/// What the S3 carrier check binds, and what it does NOT — the honest scope
/// of the signedness label, pinned so a future change cannot widen the claim
/// silently.
///
/// The comparand is `fun (callees) (params) => body`: it carries a BINDER per
/// parameter and NOTHING for the result. So the signed carrier alias binds the
/// PARAMETER positions by name (`s3_mutation_control_sign_only_retype_*`), and
/// the result position only through the statement's `Eq` type — where
/// `CleanTV.Int<w>` is definitionally `Nat`, so the kernel cannot separate them.
/// A tamper that relabels ONLY the result's signedness therefore still checks.
/// It states a TRUE equation (no bit changes), but it does not re-earn the
/// emitted RESULT signature against the source one; closing it needs the
/// producer to record the result carrier too (a clean-side companion), which
/// is why `TRUST.md` item 6 names the parameter binders and not the result.
fn widen8_module(dst: Ty) -> (Module, FuncId) {
    let mut mb = builder("adv_widen8");
    let sig = mb.add_func_type(vec![Ty::U8], vec![dst.clone()]);
    let mut fb = function(&mut mb, "widen8", sig);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::U8);
    fb.switch_to_block(e);
    let r = fb.zext(Ty::U8, dst.clone(), a);
    fb.ret(vec![r]);
    let f = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), f)
}

#[test]
fn adv_result_only_sign_relabel_is_not_bound_by_the_carrier_check() {
    // Honest `widen8(a: u8) -> u32 = zext a`, then the result alone relabelled
    // `i32`. The single `u8` parameter binder is unchanged and still honest,
    // so the by-name check has nothing to catch, and `CleanTV.Int32 := Nat`
    // makes the relabelled `Eq` type def-eq to the minted one.
    let (mut m, f) = widen8_module(Ty::U32);
    assert_eq!(unsigned(&run(&m, "widen8", vec![u(Ty::U8, 200)])), 200);
    certify(&mut m, f).expect("honest u32 result");
    retype(&mut m, f, &Ty::U32, &Ty::I32);
    assert_eq!(signed(&run(&m, "widen8", vec![u(Ty::U8, 200)])), 200);
    assert_certified(
        &m,
        "result-only u32->i32 relabel (NOT bound — honest scope)",
    );
    // A WIDTH change of the same result is still refused by the kernel: the
    // wrap moduli differ, so this residue really is signedness-only.
    let (mut wide, g) = widen8_module(Ty::U32);
    certify(&mut wide, g).expect("honest u32 result");
    retype(&mut wide, g, &Ty::U32, &Ty::U64);
    assert_kernel_refuses(&wide, "result-only u32->u64 retype");
}

/// The same boundary on the S2 side: a fieldless-enum parameter denotes at
/// `Nat` (the roadmap's "range-bounded Nat tag") and the tag-lane
/// `ExtractField` is the IDENTITY on it, so an enum parameter and the bare
/// unsigned tag of the same width are ONE comparand telescope. A certificate
/// minted for the scalar spelling checks for the enum spelling. That is the
/// chosen denotation, not an accident — recorded here so the choice is
/// visible where the carrier check is.
#[test]
fn adv_enum_param_and_its_bare_tag_share_one_comparand_telescope() {
    let mut mb = builder("adv_tag_scalar");
    let sig = mb.add_func_type(vec![Ty::U8], vec![Ty::U64]);
    let mut fb = function(&mut mb, "code", sig);
    let e = fb.create_block();
    let t = fb.add_block_param(e, Ty::U8);
    fb.switch_to_block(e);
    let r = fb.zext(Ty::U8, Ty::U64, t);
    fb.ret(vec![r]);
    let scalar_f = fb.build();
    let mut scalar = mb.build().expect("ModuleBuilder::build: test fixture");
    certify(&mut scalar, scalar_f).expect("honest scalar tag");
    assert_certified(&scalar, "code(t: u8)");

    let mut mb = builder("adv_tag_enum");
    let lvl = Ty::Enum(EnumId::new(0));
    let sig = mb.add_func_type(vec![lvl.clone()], vec![Ty::U64]);
    let mut fb = function(&mut mb, "code", sig);
    let e = fb.create_block();
    let l = fb.add_block_param(e, lvl.clone());
    fb.switch_to_block(e);
    let tag = fb.extract_field(Ty::U8, l, 0);
    let r = fb.zext(Ty::U8, Ty::U64, tag);
    fb.ret(vec![r]);
    let enum_f = fb.build();
    let mut enum_m = mb.build().expect("ModuleBuilder::build: test fixture");
    enum_m.add_enum(lvl_def());
    enum_m.proof_obligations = scalar.proof_obligations.clone();
    enum_m.proof_certificates = scalar.proof_certificates.clone();
    enum_m.proof_obligations[0].function = Some(enum_f);
    assert_certified(&enum_m, "the scalar certificate under the enum spelling");
}
